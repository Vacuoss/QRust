//Compile-time opt-in allocation counter
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicU64, AtomicU8, Ordering};

pub struct CountingSystem;
static ALLOCATIONS: AtomicU64 = AtomicU64::new(0);
static BYTES: AtomicU64 = AtomicU64::new(0);
static LIVE: AtomicU64 = AtomicU64::new(0);
static PEAK: AtomicU64 = AtomicU64::new(0);

#[inline]
fn acquired(size: usize) {
    let current=LIVE.fetch_add(size as u64, Ordering::Relaxed)+size as u64;
    PEAK.fetch_max(current, Ordering::Relaxed);
}
#[inline]
fn released(size: usize) { LIVE.fetch_sub(size as u64, Ordering::Relaxed); }
//Resets the observed peak to currently outstanding allocations. Call only in the single-threaded CLI
//benchmark, never while other threads allocate
pub fn reset_peak() { PEAK.store(LIVE.load(Ordering::Relaxed), Ordering::Relaxed); }


#[global_allocator]
static ALLOCATOR: CountingSystem = CountingSystem;
unsafe impl GlobalAlloc for CountingSystem {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() { ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
            BYTES.fetch_add(layout.size() as u64, Ordering::Relaxed);
            acquired(layout.size()); count_stage(layout.size()); }
        ptr
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc_zeroed(layout) };
        if !ptr.is_null() { ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
            BYTES.fetch_add(layout.size() as u64, Ordering::Relaxed);
            acquired(layout.size()); count_stage(layout.size()); }
        ptr
    }
    unsafe fn realloc(&self, ptr: *mut u8, old: Layout, size: usize) -> *mut u8 {
        let new_ptr = unsafe { System.realloc(ptr, old, size) };
        if !new_ptr.is_null() { ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
            BYTES.fetch_add(size as u64, Ordering::Relaxed);
            if size>=old.size() { acquired(size-old.size()); } else { released(old.size()-size); }
            count_stage(size); }
        new_ptr
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        released(layout.size());
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[derive(Clone, Copy)]
pub struct Snapshot { pub calls: u64, pub bytes: u64, pub live: u64, pub peak: u64 }
pub fn snapshot() -> Snapshot {
    Snapshot { calls: ALLOCATIONS.load(Ordering::Relaxed),
        bytes: BYTES.load(Ordering::Relaxed),
        live: LIVE.load(Ordering::Relaxed), peak: PEAK.load(Ordering::Relaxed) }
}


#[derive(Clone, Copy)]
#[repr(u8)]
pub enum Stage { Lexer = 0, Parser = 1, Lowering = 2, Semantic = 3 }
pub const STAGE_LABELS: [&str; 4] = ["Lexer", "Parser", "Lowering", "Semantic Check"];
const UNTRACKED: u8 = u8::MAX;
static ACTIVE_STAGE: AtomicU8 = AtomicU8::new(UNTRACKED);
static STAGE_CALLS: [AtomicU64; 4] = [const { AtomicU64::new(0) }; 4];
static STAGE_BYTES: [AtomicU64; 4] = [const { AtomicU64::new(0) }; 4];

pub struct StageScope(u8);
impl StageScope {
    #[inline]
    pub fn enter(stage: Stage) -> Self {
        Self(ACTIVE_STAGE.swap(stage as u8, Ordering::Relaxed))
    }
}
impl Drop for StageScope {
    #[inline]
    fn drop(&mut self) { ACTIVE_STAGE.store(self.0, Ordering::Relaxed); }
}
#[inline]
fn count_stage(size: usize) {
    let stage = ACTIVE_STAGE.load(Ordering::Relaxed) as usize;
    if stage < STAGE_CALLS.len() {
        STAGE_CALLS[stage].fetch_add(1, Ordering::Relaxed);
        STAGE_BYTES[stage].fetch_add(size as u64, Ordering::Relaxed);
    }
}
#[derive(Clone, Copy)]
pub struct StageCounters { pub calls: [u64; 4], pub bytes: [u64; 4] }
pub fn stage_snapshot() -> StageCounters {
    StageCounters {
        calls: std::array::from_fn(|i| STAGE_CALLS[i].load(Ordering::Relaxed)),
        bytes: std::array::from_fn(|i| STAGE_BYTES[i].load(Ordering::Relaxed)),
    }
}
