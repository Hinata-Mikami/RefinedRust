#![allow(dead_code)]

pub struct Triple(Box<u32>, Box<u32>, Box<u32>);

#[mapper::run]
pub fn eliminated_drop_multi_hop(t: Triple) {
    let Triple(a, b, c) = t;
    let _x = a;
    let _y = b;
    let _z = c;
}
