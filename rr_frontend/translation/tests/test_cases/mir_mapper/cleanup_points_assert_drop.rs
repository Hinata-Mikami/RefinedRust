#![allow(dead_code)]

#[mapper::run]
#[mapper::points]
pub fn cleanup_points_assert_drop<T>(value: T, condition: bool) {
    assert!(condition);
    drop(value);
}
