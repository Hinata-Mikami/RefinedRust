
struct Payload {
    value: usize,
}

impl Payload {
    #[rr::verify]
    fn value(&self) -> usize {
        self.value
    }
}

enum Entry {
    #[rr::refined_by("x" : "Z")]
    Data(#[rr::field("#(-[ #x])")] Box<Payload>),
}

impl Entry {
    #[rr::verify]
    fn read(&self) -> usize {
        match self {
            Self::Data(payload) => payload.value(),
        }
    }
}

