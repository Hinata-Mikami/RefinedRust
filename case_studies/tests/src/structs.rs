
#[repr(C)]
struct Pair<T, U> {
    x: T,
    y: U,
}

impl<T, U> Pair<T, U> {

    #[rr::returns(" *[x; y]")]
    pub fn new(x: T, y: U) -> Self {
        Self{x, y}
    }
}


#[rr::verify]
fn tuple_shrblocked_read() {
    let x = (1, 2);
    let xr = &x.0;

    // can be copied even while the first field is share-borrowed.
    let y = x;

    assert!(*xr == 1);
}

#[rr::verify]
fn tuple_shrblocked_read_shared(x: &(i32, i32)) {
    let xb = x.0;
    let xr = &x.0;

    // can be copied even while the first field is share-borrowed.
    let y = x;

    assert!(*xr == xb);
}

#[rr::verify]
fn tuple_owned_overwrite_after_read() {
    let mut x = (1i32, 2i32);
    let first = x.0;

    x = (3, 4);

    assert!(first == 1);
    assert!(x.0 == 3);
}


#[rr::verify]
fn mutref_reborrow_overwrite() {
    let mut x = 34;
    let mut xr = &mut x;
    let mut xrr = &mut (*xr);

    let mut y = 42;
    // xr gets killed here
    xr = &mut y;


    assert!(*xrr == 34);
    assert!(*xr == 42);

}


#[rr::refined_by("x" : "Z")]
#[rr::invariant("Zeven x")]
struct EvenInt {
    #[rr::field("x")]
    num: i32,
}

impl EvenInt {
    #[rr::requires("Zeven x")]
    #[rr::returns("x")]
    pub fn new(x: i32) -> Self {
        Self {num: x}
    }

    // Internal function breaking the invariant.
    // Instead of giving it a spec, we inline its proof at call sites.
    #[rr::inline]
    fn add(&mut self) {
        self.num += 1;
    }

    #[rr::requires("(self.cur + other ∈ i32)%Z")]
    #[rr::observe("self.ghost": "(self.cur+other)")]
    #[rr::tactics("apply Zeven_plus_Zeven; solve_goal.")]
    pub fn add_even(&mut self, other: &Self) {
        self.num += other.num;
    }

    #[rr::requires("(self.cur + 2 ≤ MaxInt i32)%Z")]
    #[rr::observe("self.ghost": "(self.cur+2)")]
    #[rr::tactics("rewrite -Z.add_assoc; apply Zeven_plus_Zeven; solve_goal.")]
    pub fn add_two(&mut self) {
        self.num;

        self.add();
        self.add();
    }
}



pub struct Foo {}

impl Foo {
    #[rr::returns("()")]
    pub fn a(&mut self) {
        assert!(true);
    }

    #[rr::returns("()")]
    pub fn b(&mut self) {
        assert!(true);
    }
}
