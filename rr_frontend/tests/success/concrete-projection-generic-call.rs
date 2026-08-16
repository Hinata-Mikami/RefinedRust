//@check-pass

#![feature(register_tool)]
#![register_tool(rr)]

use std::iter::Iterator;
use std::ops::Range;

#[rr::only_spec]
fn consume<T>(_value: T) {}

#[rr::verify]
fn main() {
    consume::<<Range<usize> as Iterator>::Item>(0usize);
}
