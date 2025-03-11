use crate::Cell;

#[rr::verify]
fn test1() {
    // pick invariant P := Zeven
    //#[rr::instantiate("Zeven")]
    let c = Cell::new(42i32);

    test2(&c);
}

#[rr::args("Zeven")]
fn test2(c: &Cell<i32>) {
    assert!(c.replace(2) % 2 == 0);
}
