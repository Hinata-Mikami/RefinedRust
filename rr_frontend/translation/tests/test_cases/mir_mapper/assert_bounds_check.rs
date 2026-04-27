#![allow(dead_code)]

#[mapper::run]
pub fn assert_bounds_check(xs: &[u32], i: usize) -> u32 {
    xs[i]
}
