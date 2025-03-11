
#[repr(transparent)]
#[rr::refined_by("()" : "unit")]
#[rr::exists("x")]
#[rr::invariant("Zeven x")]
#[rr::mode(na)]
pub struct EvenCell {
    #[rr::field("x")]
    value: i32,
}

impl EvenCell {
    #[rr::requires("Zeven value")]
    #[rr::returns("()")]
    pub const fn new(value: i32) -> Self {
        Self { value }
    }

    #[rr::exists("x")]
    #[rr::ensures("Zeven x")]
    #[rr::returns("x")]
    pub fn into_inner(self) -> i32 {
        self.value
    }

    #[rr::exists("x")]
    #[rr::ensures("Zeven x")]
    #[rr::returns("x")]
    pub const fn get(&self) -> i32 {
        self.value
    }
}
