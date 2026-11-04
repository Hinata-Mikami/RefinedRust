#![allow(dead_code)]

#[mapper::run]
pub fn cleanup_erased_only(opt: Option<i32>) -> i32 {
    if let Some(x) = opt { x } else { 0 }
}
