//@stderr-only

#![feature(register_tool)]
#![register_tool(rr)]

#[rr::name("VALUE")]
static VALUE: i32 = 42;

#[rr::only_spec]
fn dependency(x: i32) -> i32 {
    x
}

#[rr::inline]
fn inline_calls_function(x: i32) -> i32 {
    dependency(x)
}

#[rr::inline]
fn inline_uses_static() -> i32 {
    VALUE
}

fn main() {}
