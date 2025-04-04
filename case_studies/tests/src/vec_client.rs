use std::vec::Vec;

#[rr::verify]
fn init_vec() {
    let mut v: Vec<i32> = Vec::new();

    v.push(42);
    assert!(v.pop().unwrap() == 42);
}
