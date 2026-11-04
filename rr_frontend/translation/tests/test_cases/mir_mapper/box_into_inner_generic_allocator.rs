#![feature(allocator_api)]
#![allow(dead_code)]

use std::alloc::Allocator;

struct Node<T>(T);

#[mapper::run]
#[mapper::points]
fn box_into_inner<T, A: Allocator>(value: Box<Node<T>, A>) -> T {
    value.0
}
