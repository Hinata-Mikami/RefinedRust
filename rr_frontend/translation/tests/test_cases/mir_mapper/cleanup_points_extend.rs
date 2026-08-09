#![allow(dead_code)]

#[mapper::run]
#[mapper::points]
pub fn cleanup_points_extend(mut first: Vec<u32>, second: Vec<u32>) -> Vec<u32> {
    std::iter::Extend::extend(&mut first, second.into_iter());
    first
}
