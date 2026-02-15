#![no_std]
#![allow(dead_code)]

use core::sync::atomic::{AtomicU32, Ordering};

pub unsafe fn atomic_flag(flag: *mut AtomicU32, out: *mut u32) {
    let flag_ref = &*flag;
    let observed = flag_ref.load(Ordering::Acquire);
    *out = observed;
    flag_ref.store(1, Ordering::Release);
}
