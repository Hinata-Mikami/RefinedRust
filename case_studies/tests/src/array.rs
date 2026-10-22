#[rr::returns("[(1); (2); (3)]")]
fn array_init() -> [i32; 3] {
    let x = [1, 2, 3];
    assert!(x[2] == 3);
    x
}

#[rr::returns("replicate 3 ((42))")]
fn array_repeat() -> [i32; 3] {
    [42; 3]
}
