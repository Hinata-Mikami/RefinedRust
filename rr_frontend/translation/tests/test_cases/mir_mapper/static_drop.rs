#![allow(dead_code)]

#[mapper::run]
pub fn static_drop() {
    let _x = Box::new(0_u32);
}
