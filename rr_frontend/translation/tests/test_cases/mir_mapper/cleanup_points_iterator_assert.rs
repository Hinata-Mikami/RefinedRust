#![allow(dead_code)]

#[mapper::run]
#[mapper::points]
pub fn cleanup_points_iterator_assert<I: Iterator>(iter: I, n: usize) {
    let result = iter.take(n).skip(n).next();
    assert!(result.is_none());
}
