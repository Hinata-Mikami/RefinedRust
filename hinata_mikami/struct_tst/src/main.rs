#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#[rr::refined_by("c" : "Z", "x" : "Z")]
#[rr::invariant("1 <= c")]
struct Inner{
    #[rr::field("c")]
    count: i32,
    #[rr::field("x")]
    data: i32,
}

#[rr::refined_by("p" : "int i32" * "int i32")]
struct Outer{
    #[rr::field("p")]
    ptr: Inner,
}

#[rr::returns("()")]
fn main() {

    let i = Inner { count: 1, data: 15 };
    let o = Outer {
        ptr: i
    };
}
