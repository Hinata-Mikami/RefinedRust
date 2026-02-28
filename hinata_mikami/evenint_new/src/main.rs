#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#[rr::returns("()")]
// MinInt i32 ≤ -2147483648 を自動で解決できず手動で検証を記述
fn main() {
    let mut a;
    let b;
    unsafe {
        a = EvenInt::new(0);
        b = EvenInt::new(2);
    }

    a.add_even(&b);
    assert!(a.get() % 2 == 0);
}

#[rr::refined_by("x" : "Z")]
#[rr::invariant("Zeven x")]
struct EvenInt {
    #[rr::field("x")]
    num: i32,
}

impl EvenInt {
    /// Create a new even integer.
    #[rr::requires("Zeven x")]
    #[rr::returns("x")]
    pub unsafe fn new(x: i32) -> Self {
        Self {num: x}
    }

    /// Internal function. Unsafely add 1, making the integer odd.
    #[rr::params("x", "γ")]
    #[rr::args(#raw "((-[x]), γ)")]                // -[x] : the contents of the mutable reference
                                                   //        = 構造体の "raw" refinement
    #[rr::requires("(x + 1 ≤ MaxInt i32)%Z")]
    #[rr::observe("γ": "-[#(x+1)] : plistRT [_]")] // -[x] は plistRT [_] 型？詳しい記載はなく
    unsafe fn add(&mut self) {
        self.num += 1;
    }

    /// Get the even integer
    #[rr::ensures("Zeven self")]
    #[rr::returns("self")]
    pub fn get(&self) -> i32 {
        self.num
    }

    /// Add another even integer.
    #[rr::requires("(self.cur + other)%Z ∈ i32")]
    #[rr::observe("self.ghost": "self.cur + other")]
    pub fn add_even(&mut self, other: &Self) {
        self.num += other.num;
    }
    // Zeven(self) ∧ Zeven(other) ⇒ Zeven(self + other) を手動で証明

    /// Add 2 to an even integer.
    /// 可変参照は x.cur で現在の値を，x.ghost でゴースト変数の値を参照可能。
    /// self は宣言する必要がないのかもしれない
    #[rr::requires("(self.cur + 2 ≤ MaxInt i32)%Z")]
    #[rr::observe("self.ghost": "(self.cur + 2)")] 
    pub fn add_two(&mut self) {
        self.num;

        unsafe {
            self.add();
            self.add();
        }
    }
}
