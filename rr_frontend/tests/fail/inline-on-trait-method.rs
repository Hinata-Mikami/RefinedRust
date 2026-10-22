//@stderr-only

#![feature(register_tool)]
#![register_tool(rr)]

trait Trait {
    #[rr::inline]
    fn method(x: i32) -> i32 {
        x
    }
}

struct Type;

impl Trait for Type {
    #[rr::inline]
    fn method(x: i32) -> i32 {
        x
    }
}

fn main() {}
