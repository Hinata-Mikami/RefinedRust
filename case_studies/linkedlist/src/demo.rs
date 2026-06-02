use super::List;



#[rr::returns("max_list_Z (MinInt i32) v")]
fn max_list_i32(v: &List<i32>) -> i32 {
    let mut m = i32::MIN;

    for x in v {
        #[rr::inv_vars("m")]
        #[rr::inv("m = max_list_Z (MinInt i32) {Hist}")]
        #[rr::ignore] ||{};

        m = m.max(*x);
    }

    m
}


// Ord's spec defines mathematical components: 
// - "Ord" : "{T} → {T} → ordering"
// - "Ord_lt_trans" : "∀ a b c, a <_{Ord} b → b <_{Ord} c → a <_{Ord} c"
// - ...

#[rr::returns("max_list_cmp {T::Ord} v None")]
fn max_list<T>(v: &List<T>) -> Option<T> 
where T: Ord + Copy
{
    let mut m = None;

    for x in v {
        #[rr::inv_vars("m")]
        #[rr::inv("m = max_list_cmp {T::Ord} {Hist} None")]
        #[rr::ignore] ||{};

        m = m.max(Some(*x));
    }

    m
}


#[rr::returns("max_list_cmp Z.compare (Z.abs <$> v) None")]
fn max_list_abs(v: &List<i32>) -> Option<u32> 
{
    v.iter().map(#[rr::returns("Z.abs x")] |x| x.abs_diff(0)).max()
}







































