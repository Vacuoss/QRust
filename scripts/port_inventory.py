#!/usr/bin/env python3
"""QRust builtin inventory, from current source registries. Python 3 standard library only."""
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
src = root / "src"
math = (src / "math.rs").read_text(encoding="utf-8")
sema = (src / "sema.rs").read_text(encoding="utf-8")
surface = (src / "surface.rs").read_text(encoding="utf-8")
syntax = (src / "syntax.rs").read_text(encoding="utf-8")

def between(text, pattern):
    match = re.search(pattern, text, re.S)
    if not match:
        raise SystemExit("Required source registry not found; update this inventory script")
    return match.group(1)

functions = re.findall(r'\("([^"]+)",(\d+)\)', between(math, r'pub const FUNCTIONS:.*?= &\[(.*?)\];'))
gates = re.findall(r'gate!\((\w+),', sema)
spellings = re.findall(r'"([A-Za-z0-9_]+)"', between(sema, r'fn gate_by_name\(.*?\{\s*Some\(match name \{(.*?)_ => return None'))
capabilities = re.findall(r'\("([^"]+)",', between(surface, r'pub const CAPABILITIES.*?= &\[(.*?)\];'))

aliases = []
for line in between(math, r'pub fn canonical.*?match name \{(.*?)_ => name').splitlines():
    for lhs in re.findall(r'((?:"[a-z_0-9]+"(?:\s*\|\s*"[a-z_0-9]+")*))\s*=>', line):
        aliases.extend(re.findall(r'"([a-z_0-9]+)"', lhs))

for label, value in [
    ("Builtin compile-time math functions", len(functions)),
    ("Math aliases", len(set(aliases))),
    ("Gate implementations (not Rust std)", len(gates)),
    ("Gate names including aliases", len(set(spellings))),
    ("Quantum primitives (QRust-specific)", 7),
    ("Compile-time assertions (QRust-specific)", 5),
    ("Total independent builtin operations", len(functions) + len(gates) + 7 + 5),
    ("Language surface descriptors (some preview-only)", len(capabilities)),
]:
    print(f"{label}: {value}")
print("Math names:", ", ".join(name for name, _ in functions))
print("Gate IDs:", ", ".join(gates))
print("Async source execution: NOT SUPPORTED")
print("Rust standard library port: NOT IMPLEMENTED")
