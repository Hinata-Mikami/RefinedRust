#![allow(dead_code)]

#[mapper::run]
pub fn cleanup_erased_fake_borrow(opt: Option<i32>) -> i32 {
    match opt {
        Some(x) => x,
        None => 0,
    }
}
