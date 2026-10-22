#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.num")]

use paste::paste;

macro_rules! u_abs_diff_impl {
    ($t:ty) => {
        paste! {
            #[rr::export_as(#method core::num::$t::abs_diff)]
            #[rr::returns("Z.abs (x - other)")]
            pub fn [<$t _abs_diff>](x: $t, other: $t) -> $t {
                if x < other {
                    other - x
                } else {
                    x - other
                }
            }
        }
    }
}

u_abs_diff_impl!(u8);
u_abs_diff_impl!(u16);
u_abs_diff_impl!(u32);
u_abs_diff_impl!(u64);
u_abs_diff_impl!(u128);
u_abs_diff_impl!(usize);


macro_rules! i_abs_diff_impl {
    ($t:ty, $ut:ty) => {
        paste! {
            #[rr::only_spec]
            #[rr::export_as(#method core::num::$t::abs_diff)]
            #[rr::returns("Z.abs (x - other)")]
            pub fn [<$t _abs_diff>](x: $t, other: $t) -> $ut {
                if x < other {
                    // Converting a non-negative x from signed to unsigned by using
                    // `x as U` is left unchanged, but a negative x is converted
                    // to value x + 2^N. Thus if `s` and `o` are binary variables
                    // respectively indicating whether `self` and `other` are
                    // negative, we are computing the mathematical value:
                    //
                    //    (other + o*2^N) - (self + s*2^N)    mod  2^N
                    //    other - self + (o-s)*2^N            mod  2^N
                    //    other - self                        mod  2^N
                    //
                    // Finally, taking the mod 2^N of the mathematical value of
                    // `other - self` does not change it as it already is
                    // in the range [0, 2^N).
                    (other as $ut).wrapping_sub(x as $ut)
                } else {
                    (x as $ut).wrapping_sub(other as $ut)
                }
            }

            #[rr::export_as(#method core::num::$t::is_positive)]
            #[rr::returns("bool_decide (x > 0)")]
            pub fn [<$t _is_positive>](x: $t) -> bool { x > 0 }

            #[rr::export_as(#method core::num::$t::is_negative)]
            #[rr::returns("bool_decide (x < 0)")]
            pub fn [<$t _is_negative>](x: $t) -> bool { x < 0 }

        }
    }
}

i_abs_diff_impl!(i8, u8);
i_abs_diff_impl!(i16, u16);
i_abs_diff_impl!(i32, u32);
i_abs_diff_impl!(i64, u64);
i_abs_diff_impl!(i128, u128);
i_abs_diff_impl!(isize, usize);

macro_rules! i_abs_impl {
    ($t:ty, $x:expr) => {
        paste! {
            #[rr::export_as(#method core::num::$t::abs)]
            #[rr::requires($x)]
            #[rr::returns("Z.abs x")]
            pub fn [<$t _abs>](x: $t) -> $t {
                // Note that the #[rustc_inherit_overflow_checks] and #[inline]
                // above mean that the overflow semantics of the subtraction
                // depend on the crate we're being called from.
                if x.is_negative() {
                    -x
                } else {
                    x
                }
            }
        }
    }
}
// TOOD: requires attribute parser needs to support it.
//i_abs_impl!(i8, "x <> MinInt i8");


macro_rules! u_is_power_of_two_impl {
    ($t:ty) => {
        paste! {
            #[rr::only_spec]
            #[rr::export_as(#method core::num::$t::is_power_of_two)]
            #[rr::returns("bool_decide (is_power_of_two (Z.to_nat x))")]
            pub fn [<$t _is_power_of_two>](x: $t) -> bool {
                x.count_ones() == 1
            }
        }
    }
}

// Only for unsized types
u_is_power_of_two_impl!(u8);
u_is_power_of_two_impl!(u16);
u_is_power_of_two_impl!(u32);
u_is_power_of_two_impl!(u64);
u_is_power_of_two_impl!(u128);
u_is_power_of_two_impl!(usize);
