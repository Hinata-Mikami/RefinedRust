#![allow(dead_code)]

pub enum Either {
    Left(Box<u32>, Box<u32>),
    Right(Box<u32>),
}

#[mapper::run]
pub fn open_drop_enum(e: Either) {
    if let Either::Left(x, _) = e {
        drop(x);
    }
}
