#![no_std]
#![allow(dead_code)]

pub unsafe fn saxpy(a: f32, x: *const f32, y: *mut f32, n: i32) {
    let mut i = 0i32;
    loop {
        if i >= n {
            break;
        }

        let idx = i as usize;
        let xi = *x.add(idx);
        let yi = *y.add(idx);
        *y.add(idx) = a * xi + yi;

        i += 1;
    }
}
