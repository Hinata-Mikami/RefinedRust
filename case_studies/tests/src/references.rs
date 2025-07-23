
#[rr::observe("x.ghost": "(#x.cur.cur, x.cur.ghost)")]
#[rr::returns("x.cur.cur")]
fn mut_ref_test1(x: &mut &mut i32) -> i32 {
    **x
}

#[rr::params("γ1", "γ2", "i", "j")]
#[rr::args("((-[(i, γ1); j]), γ2)")]
#[rr::observe("γ2": "(-[#(#i, γ1); #j] : plist place_rfn _)")]
#[rr::returns("i")]
fn mut_ref_test2(x: &mut (&mut i32, i32)) -> i32 {
    *((*x).0)
}

/* maybe we should enforce the following order:
    pre:
    - regions due to rhs
    - borrow

    post:
    - assignment

    In this case, we misclassify the constraint between 5 and 7. We should classify it as a value constraint
    Or maybe rather as something that comes from the borrow. (on the way to the place, we dereference that region, which is why we need the inclusion)

    In addition, we also miss the inclusion on the universal lifetime and place lifetime we need.
    */
// TODO
#[rr::skip]
#[rr::params("γ1", "γ2", "i", "j")]
#[rr::args("(#(-[#(#i, γ1); #j]), γ2)")]
#[rr::observe("γ2": "(-[#(#i, γ1); #j])")]
#[rr::returns("i")]
fn mut_ref_test3(x: &mut (&mut i32, i32)) -> i32 {
    let y = &mut *(*x).0;
    *y
}

// TODO
#[rr::skip]
#[rr::params("γ1", "γ2", "i", "j")]
#[rr::args("(#(-[#(#i, γ1); #j]), γ2)")]
#[rr::observe("γ2": "(-[#(#i, γ1); #j])")]
#[rr::returns("i")]
fn mut_ref_test4<'a, 'b, 'c>(x: &'a mut (&'b mut i32, &'c mut i32)) -> i32 {
    let y = &mut *(*x).0;
    *y
}

#[rr::returns("x")]
fn generic_id<T>(x : T) -> T {
    x
}

#[rr::verify]
fn call_generic_id1() {
    let x = 5;
    let y = generic_id(&x);

    let _ = *y;
}

#[rr::returns("x")]
fn shr_ref_id<'a, T: 'a>(x : &'a T) -> &'a T {
    x
}

#[rr::verify]
fn call_shr_ref_id1() {
    let x = 5;
    let y = shr_ref_id(&x);

    let _ = *y;
}

// TODO: does not work currently
#[rr::skip]
fn call_shr_ref_id2() {
    let x = Some(5);
    let y = shr_ref_id(&x);

    let _ = y.unwrap();
}

#[rr::verify]
fn call_shr_ref_id3(x: &mut i32) {
    shr_ref_id(&*x);
}


// TODO
#[rr::skip]
fn call_shr_ref_id4(x: &mut i32) {
    shr_ref_id::<'_, i32>(&*x);
}
