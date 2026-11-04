#![allow(dead_code)]

#[mapper::run]
pub fn eliminated_drop_stop_at_join(b: bool, x: Box<u32>) {
    let y = x;
    if b {
        drop(y);
    }
}
