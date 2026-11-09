#!/usr/bin/env python3
"""Differential rustc / QRust Borrow Checker audit (stdlib only).

Runs rustc and QRust as independent oracles; never treats an unsupported QRust
construct as a parity test. Does not execute, repair, or generate demo programs.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
FIXTURES = ROOT / 'tests' / 'rustc_borrow_cases'
AREAS = {'nll', 'reborrow', 'move_path', 'cfg', 'region', 'return_phi', 'unsupported'}
# Symbolic branch equivalence is a mandatory guard, not optional metadata
SYMBOLIC_BRANCH_CASES = {'cfg_diamond_last_use', 'cfg_future_shared_use',
                         'return_shared_phi_owner_move'}
BASELINE_AREAS = ('nll','reborrow','move_path','cfg','region','return_phi')


def inventory() -> list[dict[str, str]]:
    result = []
    for line in (FIXTURES / 'manifest.tsv').read_text(encoding='utf-8').splitlines():
        if not line or line.startswith('#'):
            continue
        parts = line.split('\t')
        if len(parts) != 6:
            raise ValueError(f'malformed manifest: {line}')
        ident, area, expect, coverage, hint, meaning = parts
        if area not in AREAS or expect not in {'accept', 'reject'} or coverage not in {'paired','rustc_only'}:
            raise ValueError(f'invalid audit declaration: {line}')
        if not ident.replace('_', '').isalnum() or not ident.isascii():
            raise ValueError(f'invalid case identifier: {ident}')
        if not meaning or (expect == 'reject' and hint == '-'):
            raise ValueError(f'missing expected negative diagnostic: {ident}')
        rs = FIXTURES / f'{ident}.rs'
        qr = FIXTURES / f'{ident}.qr'
        if not rs.is_file() or qr.is_file() != (coverage == 'paired'):
            raise ValueError(f'fixture mismatch: {ident}')
        if ident in {entry['id'] for entry in result}:
            raise ValueError(f'duplicate id: {ident}')
        if coverage == 'paired':
            qr_source=qr.read_text(encoding='utf-8')
            before_main=qr_source.split('fn main(', 1)[0]
            # Quantum-gate builtins do not exist as ordinary typed helper
            # functions. Reject test fixtures that would compare unrelated
            # frontend failures to rustc borrow decisions
            for builtin in ('qubit(', 'rx(', 'ry(', 'rz(', 'h(', 'cx('):
                if builtin in before_main:
                    raise ValueError(f'quantum builtin {builtin} in typed helper: {ident}')
        if ident in SYMBOLIC_BRANCH_CASES:
            rust_source = rs.read_text(encoding='utf-8')
            qrust_source = qr.read_text(encoding='utf-8') if qr.is_file() else ''
            if (coverage != 'paired' or 'if flag' not in rust_source or
                    'if flag' not in qrust_source or 'flag:bool' not in qrust_source or
                    'if true' in qrust_source or 'if false' in qrust_source):
                raise ValueError(f'non-equivalent constant CFG oracle: {ident}')
        result.append(dict(id=ident, area=area, expect=expect, coverage=coverage,
                           hint=hint, description=meaning))
    if len(result) < 25 or sum(item['coverage']=='paired' for item in result) < 20:
        raise ValueError('audit matrix is unexpectedly small')
    for area in BASELINE_AREAS:
        paired = [item for item in result if item['area'] == area and item['coverage'] == 'paired']
        if not {'accept','reject'}.issubset({item['expect'] for item in paired}):
            raise ValueError(f'missing positive or negative rustc evidence for {area}')
    return result


def execute(argv: list[str], timeout: int) -> dict[str, object]:
    try:
        done = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              text=True, encoding='utf-8', errors='replace',
                              timeout=timeout, check=False)
        return dict(ok=done.returncode == 0, exit_code=done.returncode,
                    stdout=done.stdout[-6000:], stderr=done.stderr[-6000:])
    except (OSError, subprocess.TimeoutExpired) as exc:
        return dict(ok=None, exit_code=None, stdout='', stderr=str(exc))


def check_version(program: str) -> str:
    result = execute([program, '--version'], 15)
    return str(result['stdout']).strip() or str(result['stderr']).strip()


# A generic "typed MIR" rejection is not evidence of a borrow rule
BORROW_MARKERS = ('borrow','loan','reborrow','suspend','conflict','move','moved',
                  'lifetime','reference escapes','consumed')
SURFACE_MARKERS = ('unexpected token','unsupported syntax','not yet supported',
                   'unknown function','unknown typed function','unknown type','expected expression',
                   'parse error','unsupported construct')


def diagnose_qrust_rejection(message: str) -> str:
    lowered = message.lower()
    if any(marker in lowered for marker in SURFACE_MARKERS):
        return 'qrust_unrelated_rejection'
    if any(marker in lowered for marker in BORROW_MARKERS):
        return 'borrow_evidence'
    return 'qrust_weak_diagnostic'


def self_test_classification() -> None:
    assert diagnose_qrust_rejection('cannot borrow mutably') == 'borrow_evidence'
    assert diagnose_qrust_rejection('loan conflict') == 'borrow_evidence'
    assert diagnose_qrust_rejection('typed MIR unsupported syntax') == 'qrust_unrelated_rejection'
    assert diagnose_qrust_rejection('typed MIR validation failed') == 'qrust_weak_diagnostic'
    assert diagnose_qrust_rejection('unexpected token: borrow') == 'qrust_unrelated_rejection'
    assert diagnose_qrust_rejection("unknown typed function 'qubit'") == 'qrust_unrelated_rejection'



def audit(cases: list[dict[str,str]], rustc: str, qrust: str, timeout: int) -> dict[str,object]:
    rows: list[dict[str,object]] = []
    with tempfile.TemporaryDirectory(prefix='qrust-rustc-audit-') as tmp:
        meta = str(Path(tmp) / 'oracle.rmeta')
        for item in cases:
            ident = item['id']
            rs = str(FIXTURES / f'{ident}.rs')
            entry: dict[str, object] = dict(item)
            rust = execute([rustc, '--edition=2024', '--crate-type=lib',
                            '--crate-name=borrow_oracle', '--emit=metadata', '-A', 'warnings',
                            '-o', meta, rs], timeout)
            entry['rustc'] = rust
            if rust['ok'] is None:
                entry['status']='tool_failure'
            elif rust['ok'] != (item['expect']=='accept'):
                entry['status']='rustc_oracle_drift'
            elif rust['ok'] is False and not any(h in str(rust['stderr'])
                    for h in item['hint'].split('|')):
                entry['status']='unexpected_rustc_diagnostic'
            elif item['coverage']=='rustc_only':
                entry['status']='unsupported_surface'
            else:
                qr = execute([qrust, 'check', str(FIXTURES / f'{ident}.qr')], timeout)
                entry['qrust']=qr
                if qr['ok'] is None:
                    entry['status']='tool_failure'
                elif qr['ok']==rust['ok']:
                    if qr['ok'] is False:
                        evidence = diagnose_qrust_rejection(str(qr['stderr']))
                        entry['qrust_diagnostic_evidence'] = evidence
                        entry['status'] = 'matched' if evidence == 'borrow_evidence' else evidence
                    else:
                        entry['status']='matched'
                elif rust['ok'] is True:
                    entry['status']='overrejection_candidate'
                else:
                    entry['status']='unsound_acceptance_candidate'
            rows.append(entry)
    counts = dict(Counter(str(row['status']) for row in rows))
    by_area = {}
    for area in BASELINE_AREAS:
        selected = [row for row in rows if row['area'] == area and row['coverage'] == 'paired']
        by_area[area] = dict(paired=len(selected), matched=sum(
            row['status'] == 'matched' for row in selected))
    baseline_clear = all(row['status'] in ('matched','unsupported_surface') for row in rows)
    return dict(generated_utc=datetime.now(timezone.utc).isoformat(),
                rustc_version=check_version(rustc),
                qrust_executable=qrust, counts=counts,
                architecture_gate=dict(paired_baseline_clear=baseline_clear,
                    unit_and_mir_invariants='run cargo test separately',
                    unsupported_surface_count=counts.get('unsupported_surface',0),
                    evidence_by_area=by_area,
                    core_v1_certified=False),
                cases=rows)


def markdown_report(report: dict[str,object]) -> str:
    cases = report['cases']
    grouped:dict[str,list[dict[str,object]]] = defaultdict(list)
    for item in cases:
        grouped[str(item['area'])].append(item)
    lines = [
        '# QRust vs rustc — Borrow Checker differential audit', '',
        f"- Generated UTC: `{report['generated_utc']}`",
        f"- rustc: `{report['rustc_version']}`",
        '- Compare `rustc --crate-type lib --emit=metadata` against `qrust check` (Typed Frontend).',
        '- `rustc_only` entries are **feature gaps, not parity failures**.',
        '- Rust/QRust programs are structurally equivalent borrow situations, not identical language programs.',
        '', '## Overall result', '',
    ]
    for status, count in sorted(report['counts'].items()):
        lines.append(f'- `{status}`: {count}')
    architecture=report['architecture_gate']
    lines.extend(['', '## Architecture validation boundary', '',
        f"- Paired differential baseline clear: **{architecture['paired_baseline_clear']}**",
        '- Unit/MIR invariants require a separate successful `cargo test`.',
        '- Core v1 certified: **False**; complete Rust semantics and formal soundness are not established.',
        '- Each fixture pair is a structural counterpart, not an identical Rust program.',
        '- A generic `typed MIR` error is insufficient evidence of a Borrow Checker rule.',
        '', '| Area | Paired | Matched |', '|---|---:|---:|',
    ])
    for area, evidence in architecture['evidence_by_area'].items():
        lines.append(f"| {area} | {evidence['paired']} | {evidence['matched']} |")
    lines.extend(['','## Evidence by semantic area','',
                  '| Area | Case | rustc | QRust | Classification |',
                  '|---|---|---|---|---|'])
    for area, items in grouped.items():
        for case in items:
            r = case.get('rustc', {})
            q = case.get('qrust', {})
            def verdict(v:dict[str,object]) -> str:
                return 'accepted' if v.get('ok') is True else ('rejected' if v.get('ok') is False else 'not run')
            lines.append(f"| {area} | `{case['id']}` | {verdict(r)} | {verdict(q)} | `{case['status']}` |")
    lines.extend(['', '## Interpretation', '',
        '- `matched` confirms agreement for that specific paired snippet only.',
        '- `unsound_acceptance_candidate` needs immediate investigation: QRust accepted code rustc rejected.',
        '- `overrejection_candidate` may be a missing language feature or an imprecise borrow proof.',
        '- `qrust_unrelated_rejection` means a surface/parser rejection, not confirmed borrow parity.',
        '- `qrust_weak_diagnostic` is a rejection without causal borrow/region evidence.',
        '- `rustc_oracle_drift` or `unexpected_rustc_diagnostic` invalidates the reference fixture.',
        '- This audit is not a proof of Rust compatibility or soundness. Add new cases for each bug.',
        ''])
    return '\n'.join(lines)


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rustc', default=shutil.which('rustc') or 'rustc')
    exe = 'qrust.exe' if sys.platform=='win32' else 'qrust'
    parser.add_argument('--qrust', default=str(ROOT / 'target' / 'release' / exe))
    parser.add_argument('--timeout', type=int, default=30)
    parser.add_argument('--validate-only', action='store_true', help='verify fixture matrix without invoking compilers')
    parser.add_argument('--self-test', action='store_true', help='check classifier invariants without compilers')
    parser.add_argument('--json', type=Path, help='output structured evidence JSON')
    parser.add_argument('--markdown', type=Path, help='output human-readable Markdown report')
    args=parser.parse_args()
    try:
        cases=inventory()
        if args.self_test:
            self_test_classification()
            print('Audit classification self-tests OK')
            return 0
        if args.validate_only:
            print('Audit manifest valid:',len(cases),'cases;',sum(c['coverage']=='paired' for c in cases),
                  'paired;',sum(c['coverage']=='rustc_only' for c in cases),'rustc-only')
            return 0
        report=audit(cases,args.rustc,args.qrust,args.timeout)
        for flag,output in [(args.json,json.dumps(report,indent=2,ensure_ascii=False)+'\n'),
                            (args.markdown,markdown_report(report))]:
            if flag is not None:
                flag.parent.mkdir(parents=True,exist_ok=True)
                flag.write_text(output,encoding='utf-8')
        print('rustc oracle version:',report['rustc_version'])
        print('Audit classification:',report['counts'])
        for row in report['cases']:
            if row['status'] not in {'matched','unsupported_surface'}:
                print('ISSUE:',row['id'],row['status'])
        return 1 if any(row['status'] not in {'matched','unsupported_surface'} for row in report['cases']) else 0
    except (OSError,ValueError) as exc:
        print('audit failed:',exc,file=sys.stderr)
        return 2

if __name__ == '__main__':
    raise SystemExit(main())
