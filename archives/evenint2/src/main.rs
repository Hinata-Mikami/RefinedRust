// ——― RefinedRust annotations ——―//
#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
// ——― RefinedRust annotations END ——―//

fn main() {
    let mut a;
    let b;
    unsafe {
        a = EvenInt::new(0);
        b = EvenInt::new(2);
    }

    a.add_even(&b);
    assert!(a.get() % 2 == 0);  // 検証したいこと
}

// RefinedRustの数理モデルはCoqの整数Zを使う
// この辺の話は SPEC_FORMAT.md に詳しく記載
#[rr::refined_by("x" : "Z")] // EvenInt は Coq integers "Z"
#[rr::invariant("Zeven x")]  // Zeven x : x が偶数であるというCoq上の述語（不変条件）
struct EvenInt {
    #[rr::field("x")]
    num: i32,
}

impl EvenInt {
    
    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::requires("Zeven x")]  //事前条件
    #[rr::returns("x")]         //事後条件
    /// Create a new even integer.
    pub unsafe fn new(x: i32) -> Self {
        Self {num: x}
    }

    #[rr::params("x", "γ")]
    #[rr::args(#raw "(#(-[#x]), γ)")]   //#raw :EvenIntが持つ不変条件を満たさなくてもいいという意味
                                        // we use -[#x] for the contents of the mutable reference
                                        // γが指す場所に格納されている整数をxとする，ということ？
    #[rr::requires("(x + 1 ≤ MaxInt i32)%Z")]
    #[rr::observe("γ": "(-[#(x+1)%Z] : plist place_rfn _)")] //事後条件（たぶん）
    /// Internal function. Unsafely add 1, making the integer odd.
    unsafe fn add(&mut self) {
        self.num += 1;
    }

    /// Get the even integer
    pub fn get(&self) -> i32 {
        self.num
    }

    /// Add another even integer.
    #[rr::params("x", "y", "γ")]
    #[rr::args("(#x, γ)", "(#y)")]
    #[rr::requires("(MinInt i32 ≤ x + y ∧ x + y ≤ MaxInt i32)%Z")]
    #[rr::observe("γ": "(x+y)")]
    pub fn add_even(&mut self, other: &Self) {
        self.num += other.num;
    }

    #[rr::params("x", "γ")]
    #[rr::args("(#x, γ)")]
    #[rr::requires("(x + 2 ≤ MaxInt i32)%Z")]
    #[rr::observe("γ": "(x+2)")]
    /// Add 2 to an even integer.
    pub fn add_two(&mut self) {
        self.num;

        unsafe {
            self.add();
            self.add();
        }
    }
}
