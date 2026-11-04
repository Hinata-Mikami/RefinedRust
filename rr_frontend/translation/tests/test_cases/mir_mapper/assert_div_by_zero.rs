#![allow(dead_code)]

#[mapper::run]
pub fn assert_div_by_zero(x: u32, y: u32) -> u32 {
    x / y
}
