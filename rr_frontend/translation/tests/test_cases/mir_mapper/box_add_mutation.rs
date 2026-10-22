#![allow(dead_code)]

#[mapper::run]
pub fn box_add_mutation(mut x: Box<i32>) -> Box<i32> {
    *x += 42;
    x
}
