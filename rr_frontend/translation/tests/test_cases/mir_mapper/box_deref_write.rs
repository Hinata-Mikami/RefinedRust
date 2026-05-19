#![allow(dead_code)]

#[mapper::run]
pub fn box_deref_write(mut x: Box<u32>) -> u32 {
    *x = 7;
    *x
}
