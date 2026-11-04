#![allow(dead_code)]

pub enum Either {
    Left(Box<u32>, Box<u32>),
    Right(Box<u32>, Box<u32>),
}

#[mapper::run]
pub fn open_drop_target_join_rejected(b: bool, e: Either) {
    let x = if b {
        match e {
            Either::Left(v, _) => Some(v),
            Either::Right(v, _) => Some(v),
        }
    } else {
        None
    };

    if let Some(v) = x {
        drop(v);
    }
}
