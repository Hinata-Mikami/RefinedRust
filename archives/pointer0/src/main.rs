#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#[rr::refined_by("v" : "Z")]
struct Data{
    #[rr::field("v")]
    value: i32,
}

fn main() {
    logic();
}

#[rr::returns("()")]
fn logic() {
    let mut d = Data { value: 1 };
    let mut p = &mut d;
}