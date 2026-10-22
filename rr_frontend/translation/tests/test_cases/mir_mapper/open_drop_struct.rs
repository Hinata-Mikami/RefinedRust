#![allow(dead_code)]

pub struct Pair(Box<u32>, Box<u32>);

#[mapper::run]
pub fn open_drop_struct(p: Pair) {
    let Pair(x, _) = p;
    drop(x);
}
