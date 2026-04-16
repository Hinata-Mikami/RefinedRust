#![allow(dead_code)]

#[mapper::run]
pub fn box_deref(x: Box<u32>) -> u32 {
    *x
}
