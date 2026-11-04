#![allow(dead_code)]

pub struct Pair(Box<u32>, Box<u32>);

#[mapper::run]
pub fn open_drop_with_goto_prelude(p: Pair) {
    let x = p.0;
    let y = x;
    drop(y);
}
