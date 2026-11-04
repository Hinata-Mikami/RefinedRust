#![allow(dead_code)]

struct Payload {
    value: usize,
}

impl Payload {
    fn value(&self) -> usize {
        self.value
    }
}

enum Entry {
    Data(Box<Payload>),
}

impl Entry {
    #[mapper::run]
    fn read(&self) -> usize {
        match self {
            Self::Data(payload) => payload.value(),
        }
    }
}
