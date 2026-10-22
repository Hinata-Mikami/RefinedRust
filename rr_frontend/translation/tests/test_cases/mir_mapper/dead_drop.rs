#![allow(dead_code)]

#[mapper::run]
pub fn dead_drop(x: Box<u32>) {
    let _y = x;
}
