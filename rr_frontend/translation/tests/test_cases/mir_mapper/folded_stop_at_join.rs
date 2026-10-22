#![allow(dead_code)]

#[mapper::run]
pub fn folded_stop_at_join(b: bool, opt: Option<i32>) -> i32 {
    let x = if b {
        match opt {
            Some(v) => v,
            None => 0,
        }
    } else {
        1
    };
    x
}
