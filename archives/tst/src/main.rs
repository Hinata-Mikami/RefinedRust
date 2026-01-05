#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#[rr::returns("10")]
fn returns_ten() -> i32 {
    10
}

#[rr::params("x")]
#[rr::args("x")]
#[rr::returns("x")]
fn do_nothing(x : i32) -> i32{
    x
}

#[rr::returns("()")]
fn main() {

    assert!(1 == 1);
    // assert!(1 == 2); // fail
    assert!(1 == 2 - 1);

    let x = returns_ten();
    assert!(x == 10); 

    let y = 20;
    assert!(x + y == y + x);

    assert!(do_nothing(x) == 10);
    assert!(x == do_nothing(x));

    assert!({
        let a = 1;
        let b = 2;
        a < b
    });  // block 式 (セミコロンがない最後の式の値が返る)

    assert!(if x == 10 { true } else { false });

}
