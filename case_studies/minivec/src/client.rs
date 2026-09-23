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

#[rr::params("op" : "Z → Z → Z", "p")]
#[rr::requires(#iris "□ ∀ a b, {F::Pre} π p combine *[a; b]")]
#[rr::requires(#iris "□ (∀ a b c, {F::Post} π p combine *[a; b] c -∗ ⌜c = op a b⌝ ∗ True)")]
#[rr::returns("fold_left op values init")]
#[rr::may_unwind_if("(∃ a b, {F::UnwindCondition} combine p *[a; b]) ∨ {F::DropGlueUnwind}")]
fn fold_i32<F>(
    values: &Vec<i32>,
    init: i32,
    combine: F,
) -> i32 
    where F: Fn(i32, i32) -> i32
{
    let mut acc = init;
    for x in values {
        #[rr::inv_vars("acc")]
        #[rr::inv("acc = fold_left op {Hist} init")]
        #[rr::ignore] ||{};
        acc = combine(acc, *x);
    }
    acc
}

#[rr::verify]
fn fold_client() {
    let mut x = Vec::new();
    x.push(1);
    x.push(2);

    let res = fold_i32(&x, 0, #[rr::returns("Z.max x y")] |x, y| x.max(y));
    assert!(res == 2);

}
