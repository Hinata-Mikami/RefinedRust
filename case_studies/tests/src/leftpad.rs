
// attaching axiomatic specs to these, as we do not have specifications for these parts of std yet.
#[rr::only_spec]
#[rr::returns("Z.max a b")]
fn max_usize(a: usize, b: usize) -> usize {
    if a >= b { a } else { b }
}
#[rr::only_spec]
#[rr::returns("a - b")]
fn saturating_sub_usize(a: usize, b: usize) -> usize {
    a.saturating_sub(b)
}
#[rr::only_spec]
#[rr::returns("v !! Z.to_nat i")]
fn vec_get<T>(v: &Vec<T>, i: usize) -> Option<&T> {
    v.get(i)
}

#[rr::only_spec]
#[rr::requires("Copyable {C}")] // TODO: should be automatically encoded due to Copy requirement
#[rr::returns("(replicate (Z.to_nat l - length s) c) ++ s")]
pub fn leftpad<C:Copy>(c:C, l:usize, s:&Vec<C>)-> Vec<C>
  { 
    let rl = max_usize(l, s.len());
    let pl = saturating_sub_usize(l, s.len());
    let mut r = Vec::<C>::with_capacity(rl); 
    let mut i = 0usize;

    while i<pl {
        let _ = #[rr::exists("ic" : "Z")]
        #[rr::inv_var("i": "#ic")]
        #[rr::inv_var("r" : "# (<#> <$#> replicate (Z.to_nat ic) c)")]
        #[rr::inv("(0 ≤ ic ≤ l - length s)%Z")]
        #[rr::ignore] ||{};

        r.push(c); i+=1;
    }

    while i<rl {
        let _ = #[rr::exists("ic")]
        #[rr::inv_var("i": "#ic")]
        #[rr::inv_var("r" : "#(<#> <$#> (replicate (Z.to_nat l - length s)%nat c ++ (take (Z.to_nat ic - (Z.to_nat l - length s))%nat s)))")]
        #[rr::inv("(l - length s ≤ ic ≤ Z.max l (length s))%Z")]
        #[rr::ignore] ||{};

        let x = vec_get(s, i-pl);
        r.push(*(x.unwrap())); i+=1;
    }
    
    r                                                                  
}
