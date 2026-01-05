#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#[rr::params("x": "Z")]
#[rr::args("x" @ "int i32")]
#[rr::requires("(x + 1 ≤ MaxInt i32)%Z")]
#[rr::returns("x + 1")]
fn add_one(x: i32) -> i32 {
    x + 1
}

#[rr::params("x": "Z")]
#[rr::args("x" @ "int i32")]
#[rr::requires("Zeven x")]
#[rr::requires("(x + 2 ≤ MaxInt i32)%Z")]
#[rr::returns("x + 2")]
#[rr::ensures("Zeven (x + 2)")] // 手動で証明を追加 : Zeven(x + 2) -> Zeven x , Zeven 2
fn add_two(x: i32) -> i32 {
    let y = add_one(x);
    let z = add_one(y);
    z
}

fn main(){

    let a = 0; 
    let b = add_two(a); 

    assert!(b % 2 == 0); 

}
