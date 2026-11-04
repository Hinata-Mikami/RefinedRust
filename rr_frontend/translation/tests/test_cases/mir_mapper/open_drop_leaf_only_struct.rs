#![allow(dead_code)]

pub struct Pair(Box<u32>, Box<u32>);

#[mapper::run]
pub fn open_drop_leaf_only_struct(p: Pair) {
    let x = p.0;
    drop(x);
}
