#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#[rr::refined_by("(c, x)")]
#[rr::invariant("1 <= c")]
struct Inner{
    #[rr::field("c")]
    count: i32,
    #[rr::field("x")]
    data: i32,
}

// #[rr::refined_by("p" : "int i32" * "int i32")]
// struct Outer{
//     #[rr::field("p")]
//     ptr: Inner,
// }

#[rr::params("j")]
#[rr::args("j")]
#[rr::returns("j.1")]
fn get_count(i : Inner) -> i32 {
    i.count
}

#[rr::returns("()")]
fn main() {

    let i = Inner { count: 1, data: 15 };
    // let o = Outer {
    //     ptr: i
    // };
}
