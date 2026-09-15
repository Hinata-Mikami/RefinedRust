use crate::*;

#[rr::returns("()")]
fn get_mut_client() {

    // We have desugared this, as the macro uses parts of Rust our frontend does not support yet.
    //let mut x = vec![100, 200, 300];
    let mut x = Vec::new();
    x.push(100);
    x.push(200);
    x.push(300);

    let xr = x.get_mut(1).unwrap();
    assert!(*xr == 200);
    *xr = 42;
    assert!(*x.get_mut(1).unwrap() == 42);
}

#[rr::returns("max_list_Z (min_int i32) v")]
fn max_list_i32(v: &Vec<i32>) -> i32 {
    let mut m = i32::MIN;

    for x in v {
        #[rr::inv_vars("m")]
        #[rr::inv("m = max_list_Z (min_int i32) {Hist}")]
        #[rr::ignore] ||{};

        m = m.max(*x);
    }

    m
}
