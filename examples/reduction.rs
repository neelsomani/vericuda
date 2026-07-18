#![no_std]
#![feature(asm_experimental_arch)]

#[inline(always)]
unsafe fn model_barrier() {
    #[cfg(target_arch = "nvptx64")]
    core::arch::asm!("bar.sync 0;");

    #[cfg(not(target_arch = "nvptx64"))]
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

/// Eight-lane model of the verified tree-reduction shape.
///
/// `shared` is an ordinary raw pointer in Rust.  Passing `_1` to
/// `mir2coq.py --shared-param` is an explicit modeling convention; it is not a
/// claim that rustc assigns this parameter to PTX shared space.
#[no_mangle]
pub unsafe extern "C" fn reduction(shared: *mut f32, tid: u32) {
    *shared.add(tid as usize) = (tid + 1) as f32;
    model_barrier();

    for s in 0..3u32 {
        let stride = 4u32 >> s;
        if tid < stride {
            let a = *shared.add(tid as usize);
            let b = *shared.add((tid + stride) as usize);
            *shared.add(tid as usize) = a + b;
        }
        model_barrier();
    }
}
