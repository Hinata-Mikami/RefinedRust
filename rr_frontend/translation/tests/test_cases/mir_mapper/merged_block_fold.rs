#![allow(dead_code)]

#[mapper::run]
pub fn merged_block_fold(b: bool, x: Box<u32>) -> Option<Box<u32>> {
    if b {
        let y = x;
        Some(y)
    } else {
        None
    }
}
