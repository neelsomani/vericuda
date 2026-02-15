#![no_std]

use core::sync::atomic::{AtomicU32, Ordering};

pub unsafe fn bad(flag: *mut AtomicU32, out: *mut u32) {
    let flag_ref = &*flag;
    // Deliberately incorrect orderings that the translator should reject.
    let observed = flag_ref.load(Ordering::Relaxed);
    *out = observed;
    flag_ref.store(1, Ordering::Relaxed);
}
