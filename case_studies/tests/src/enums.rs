#![rr::import("refinedrust.extra_proofs.tests", "enums")]

#[rr::refined_by("option (place_rfn {rt_of T})")]
#[rr::derive_instantiate("DropGlueUnwind" := "{T::DropGlueUnwind}")]
enum Option<T> {
    #[rr::pattern("None")]
    None,
    #[rr::pattern("Some" $ "x")]
    #[rr::refinement("*[x]")]
    Some(T)
}

#[rr::refined_by("option (place_rfn {rt_of T})")]
#[rr::context("EqDecision {xt_of T}")]
#[rr::skip(drop_glue)]
enum Contextual<T> {
    #[rr::pattern("None")]
    None,
    #[rr::pattern("Some" $ "x")]
    #[rr::refinement("*[x]")]
    Some(T),
}

#[rr::context("EqDecision {xt_of T}")]
impl<T> Contextual<T> {
    #[rr::returns("None")]
    fn new() -> Self {
        Self::None
    }
}

impl<T> Option<T> {
    #[rr::returns("None")]
    pub fn none() -> Self {
        Self::None
    }

    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("Some x")]
    pub fn some(x : T) -> Self {
        Self::Some(x)
    }
}


#[rr::refined_by("result (place_rfn {rt_of T}) (place_rfn {rt_of U})")]
#[rr::derive_instantiate("DropGlueUnwind" := "{T::DropGlueUnwind} ∨ {U::DropGlueUnwind}")]
enum Result<T, U> {
    #[rr::pattern("Ok" $ "x")]
    #[rr::refinement("*[x]")]
    Ok(T),
    #[rr::pattern("Err" $ "x")]
    #[rr::refinement("*[x]")]
    Err(U),
}

impl<T, U> Result<T, U> {
    #[rr::params("x")]
    #[rr::args("x")]
    pub fn foo(&self) {
    }
}

#[repr(u8)]
#[rr::refined_by("sizes")]
enum Sizes {
    #[rr::pattern("Sz1")]
    Sz1 = 2,
    #[rr::pattern("Sz2")]
    Sz2,
}

impl Sizes {
    #[rr::returns("Sz1")]
    pub fn new() -> Self {
        Self::Sz1
    }
}


enum Anon {
    ABitAnon,
    ReallyAnon
}

impl Anon {
    // TODO: should have a way to escape and interpret this name by writing {anon::ABitAnon}
    #[rr::returns("enums_Anon_ABitAnon")]
    pub fn new() -> Self {
        Self::ABitAnon
    }
}

// TODO: handle drop glue for auto-generated enums.
// We need to fix the RT handling for that.
// (Also needed for derived impls e.g. for Ord)
#[rr::skip(drop_glue)]
enum Anon2<T> {
    ABitAnon(T),
    ReallyAnon
}

impl<T> Anon2<T> {
    // TODO: should have a way to escape and interpret this name by writing {anon::ABitAnon}
    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("enums_Anon2_ABitAnon *[x]")]
    pub fn new(x: T) -> Self {
        Self::ABitAnon(x)
    }
}
