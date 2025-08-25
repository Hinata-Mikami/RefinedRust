#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.arithops")]
#![allow(unused)]


#[rr::export_as(core::ops::Add)]
#[rr::exists("AddOpDefined" : "{xt_of Self} → {xt_of Rhs} → Prop")]
#[rr::exists("AddOp" : "{xt_of Self} → {xt_of Rhs} → {xt_of Output}")]
pub trait Add<Rhs = Self> {
    type Output;

    #[rr::requires("{AddOpDefined} self rhs")]
    #[rr::returns("{AddOp} self rhs")]
    fn add(self, rhs: Rhs) -> Self::Output;
}

macro_rules! add_impl {
    ($t:ty, $x:expr) => (
        #[rr::instantiate("AddOp" := "λ a b : Z, a + b")] 
        #[rr::instantiate("AddOpDefined" := $x)]
        impl Add for $t {
            type Output = $t;

            #[rr::default_spec]
            fn add(self, other: $t) -> $t { self + other }
        }

        #[rr::instantiate("AddOp" := "λ a b : Z, a + b")] 
        #[rr::instantiate("AddOpDefined" := $x)]
        impl Add<$t> for &$t {
            type Output = $t;

            #[rr::default_spec]
            fn add(self, other: $t) -> $t { *self + other }
        }

        #[rr::instantiate("AddOp" := "λ a b : Z, a + b")] 
        #[rr::instantiate("AddOpDefined" := $x)]
        impl<'a> Add<&'a $t> for $t {
            type Output = $t;

            #[rr::default_spec]
            fn add(self, other: &'a $t) -> $t { self + *other }
        }

        #[rr::instantiate("AddOp" := "λ a b : Z, a + b")] 
        #[rr::instantiate("AddOpDefined" := $x)]
        impl<'a> Add<&'a $t> for & $t {
            type Output = $t;

            #[rr::default_spec]
            fn add(self, other: &'a $t) -> $t { *self + *other }
        }
    )
}


add_impl! { usize, "λ a b, (a + b) ∈ usize" }
add_impl! { u8, "λ a b, (a + b) ∈ u8" }
add_impl! { u16, "λ a b, (a + b) ∈ u16" }
add_impl! { u32, "λ a b, (a + b) ∈ u32" }
add_impl! { u64, "λ a b, (a + b) ∈ u64" }
add_impl! { u128, "λ a b, (a + b) ∈ u128" }
add_impl! { isize, "λ a b, (a + b) ∈ isize" }
add_impl! { i8, "λ a b, (a + b) ∈ i8" }
add_impl! { i16, "λ a b, (a + b) ∈ i16" }
add_impl! { i32, "λ a b, (a + b) ∈ i32" }
add_impl! { i64, "λ a b, (a + b) ∈ i64" }
add_impl! { i128, "λ a b, (a + b) ∈ i128" }


#[rr::export_as(core::ops::Mul)]
#[rr::exists("MulOpDefined" : "{xt_of Self} → {xt_of Rhs} → Prop")]
#[rr::exists("MulOp" : "{xt_of Self} → {xt_of Rhs} → {xt_of Output}")]
pub trait Mul<Rhs = Self> {
    type Output;

    #[rr::requires("{MulOpDefined} self rhs")]
    #[rr::returns("{MulOp} self rhs")]
    fn mul(self, rhs: Rhs) -> Self::Output;
}

macro_rules! mul_impl {
    ($t:ty, $x:expr) => (
        #[rr::instantiate("MulOp" := "λ a b : Z, a * b")] 
        #[rr::instantiate("MulOpDefined" := $x)]
        impl Mul for $t {
            type Output = $t;

            #[rr::default_spec]
            fn mul(self, other: $t) -> $t { self * other }
        }

        #[rr::instantiate("MulOp" := "λ a b : Z, a * b")] 
        #[rr::instantiate("MulOpDefined" := $x)]
        impl Mul<$t> for &$t {
            type Output = $t;

            #[rr::default_spec]
            fn mul(self, other: $t) -> $t { *self * other }
        }

        #[rr::instantiate("MulOp" := "λ a b : Z, a * b")] 
        #[rr::instantiate("MulOpDefined" := $x)]
        impl<'a> Mul<&'a $t> for $t {
            type Output = $t;

            #[rr::default_spec]
            fn mul(self, other: &'a $t) -> $t { self * *other }
        }

        #[rr::instantiate("MulOp" := "λ a b : Z, a * b")] 
        #[rr::instantiate("MulOpDefined" := $x)]
        impl<'a> Mul<&'a $t> for & $t {
            type Output = $t;

            #[rr::default_spec]
            fn mul(self, other: &'a $t) -> $t { *self * *other }
        }
    )
}


mul_impl! { usize, "λ a b, (a * b) ∈ usize" }
mul_impl! { u8, "λ a b, (a * b) ∈ u8" }
mul_impl! { u16, "λ a b, (a * b) ∈ u16" }
mul_impl! { u32, "λ a b, (a * b) ∈ u32" }
mul_impl! { u64, "λ a b, (a * b) ∈ u64" }
mul_impl! { u128, "λ a b, (a * b) ∈ u128" }
mul_impl! { isize, "λ a b, (a * b) ∈ isize" }
mul_impl! { i8, "λ a b, (a * b) ∈ i8" }
mul_impl! { i16, "λ a b, (a * b) ∈ i16" }
mul_impl! { i32, "λ a b, (a * b) ∈ i32" }
mul_impl! { i64, "λ a b, (a * b) ∈ i64" }
mul_impl! { i128, "λ a b, (a * b) ∈ i128" }



#[rr::export_as(core::ops::Sub)]
#[rr::exists("SubOpDefined" : "{xt_of Self} → {xt_of Rhs} → Prop")]
#[rr::exists("SubOp" : "{xt_of Self} → {xt_of Rhs} → {xt_of Output}")]
pub trait Sub<Rhs = Self> {
    type Output;

    #[rr::requires("{SubOpDefined} self rhs")]
    #[rr::returns("{SubOp} self rhs")]
    fn sub(self, rhs: Rhs) -> Self::Output;
}

macro_rules! sub_impl {
    ($t:ty, $x:expr) => (
        #[rr::instantiate("SubOp" := "λ a b : Z, a - b")] 
        #[rr::instantiate("SubOpDefined" := $x)]
        impl Sub for $t {
            type Output = $t;

            #[rr::default_spec]
            fn sub(self, other: $t) -> $t { self - other }
        }

        #[rr::instantiate("SubOp" := "λ a b : Z, a - b")] 
        #[rr::instantiate("SubOpDefined" := $x)]
        impl Sub<$t> for &$t {
            type Output = $t;

            #[rr::default_spec]
            fn sub(self, other: $t) -> $t { *self - other }
        }

        #[rr::instantiate("SubOp" := "λ a b : Z, a - b")] 
        #[rr::instantiate("SubOpDefined" := $x)]
        impl<'a> Sub<&'a $t> for $t {
            type Output = $t;

            #[rr::default_spec]
            fn sub(self, other: &'a $t) -> $t { self - *other }
        }

        #[rr::instantiate("SubOp" := "λ a b : Z, a - b")] 
        #[rr::instantiate("SubOpDefined" := $x)]
        impl<'a> Sub<&'a $t> for & $t {
            type Output = $t;

            #[rr::default_spec]
            fn sub(self, other: &'a $t) -> $t { *self - *other }
        }
    )
}


sub_impl! { usize, "λ a b, (a - b) ∈ usize" }
sub_impl! { u8, "λ a b, (a - b) ∈ u8" }
sub_impl! { u16, "λ a b, (a - b) ∈ u16" }
sub_impl! { u32, "λ a b, (a - b) ∈ u32" }
sub_impl! { u64, "λ a b, (a - b) ∈ u64" }
sub_impl! { u128, "λ a b, (a - b) ∈ u128" }
sub_impl! { isize, "λ a b, (a - b) ∈ isize" }
sub_impl! { i8, "λ a b, (a - b) ∈ i8" }
sub_impl! { i16, "λ a b, (a - b) ∈ i16" }
sub_impl! { i32, "λ a b, (a - b) ∈ i32" }
sub_impl! { i64, "λ a b, (a - b) ∈ i64" }
sub_impl! { i128, "λ a b, (a - b) ∈ i128" }
