
// TODO write some simple test cases


#[rr::verify]
fn loop1() {
    
    let mut x = 0;

    while x < 5 {
        let _ = #[rr::exists("i")]
        #[rr::inv_var("x": "#i")]
        #[rr::inv("(0 ≤ i ≤ 5)%Z")]
        #[rr::ignore] ||{};

        x += 1;
    }

    assert!(x == 5);
}


// Basic infinite loop test
#[rr::verify]
#[allow(unreachable_code)]
#[allow(clippy::self_assignment)]
fn loop2() {
    let mut x = 0;

    loop {
        let _ =
        #[rr::inv_var("x": "#0%Z")]
        #[rr::ignore] ||{};

        x = x;
    }

    unreachable!();
}


// Demonstrates that we need definitely-initialized analysis.
// (interestingly, this still partially works without, because we just do one loop unfolding
// without an invariant if it's not initialized yet...)
#[rr::verify]
fn loop3() {
    let mut x = 0;

    while x < 5 {
        let _ = #[rr::exists("i")]
        #[rr::inv_var("x": "#i")]
        #[rr::inv("(0 ≤ i ≤ 5)%Z")]
        #[rr::ignore] ||{};

        let y = 0;

        x += 1 + y;
    }

    assert!(x == 5);
}
