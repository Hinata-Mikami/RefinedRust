
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

    #[rr::params("x", "γ")]
    #[rr::args(#raw "((-[x]), γ)")]
    #[rr::requires("(x + 1 ≤ MaxInt i32)%Z")]
    #[rr::observe("γ": "(-[#(x+1)%Z] : plistRT _)")]
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
