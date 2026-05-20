#![feature(core_intrinsics)]
#![allow(dead_code, internal_features)]

#[repr(i8)]
pub enum Ordering {
    Less = -1,
    Equal = 0,
    Greater = 1,
}

impl Ordering {
    #[mapper::run]
    pub const fn lowered_discriminant_value(self) -> i8 {
        core::intrinsics::discriminant_value(&self)
    }
}
