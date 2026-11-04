//@stderr-only

#![feature(register_tool)]
#![register_tool(rr)]

#[rr::only_spec]
fn dependency<T>(x: T) -> T {
    x
}

#[rr::inline]
fn inline_calls_dependency<T>(x: T) -> T {
    dependency(x)
}

#[rr::verify]
fn concrete_caller(x: i32) -> i32 {
    inline_calls_dependency(x)
}

fn main() {}
