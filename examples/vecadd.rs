#![no_std]

#[allow(improper_ctypes_definitions)]
pub unsafe fn vecadd(a: &[f32], b: &[f32], c: *mut f32, idx: usize) {
    if idx < a.len() {
        let elem = unsafe { &mut *c.add(idx) };
        *elem = a[idx] + b[idx];
    }
}