#![allow(dead_code)]

#[mapper::run]
pub fn conditional_drop(b: bool, x: Box<u32>) -> Option<Box<u32>> {
    if b { Some(x) } else { None }
}
