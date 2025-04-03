#![rr::include("iterator")]

#[rr::verify]
fn loop1() {
    
    let mut x = 0;

    while x < 5 {
        let _ = #[rr::exists("i")]
        #[rr::inv_var("x": "#i")]
        #[rr::inv("(0 ≤ i ≤ 5)%Z")]
        #[rr::ignore] ||{};

        x += 1;
    }

    assert!(x == 5);
}


// Basic infinite loop test
#[rr::verify]
#[allow(unreachable_code)]
#[allow(clippy::self_assignment)]
fn loop2() {
    let mut x = 0;

    loop {
        let _ =
        #[rr::inv_var("x": "#0%Z")]
        #[rr::ignore] ||{};

        x = x;
    }

    unreachable!();
}


// Demonstrates that we need definitely-initialized analysis.
// (interestingly, this still partially works without, because we just do one loop unfolding
// without an invariant if it's not initialized yet...)
#[rr::verify]
fn loop3() {
    let mut x = 0;

    while x < 5 {
        let _ = #[rr::exists("i")]
        #[rr::inv_var("x": "#i")]
        #[rr::inv("(0 ≤ i ≤ 5)%Z")]
        #[rr::ignore] ||{};

        let y = 0;

        x += 1 + y;
    }

    assert!(x == 5);
}



#[rr::refined_by("(start, last)" : "Z * Z")]
#[rr::invariant("(start ≤ last)%Z")]
struct MyRange {
    #[rr::field("start")]
    start: usize,
    #[rr::field("last")]
    end: usize,
}


#[rr::instantiate("Next" := "λ s1 e s2, ⌜s1.2 = s2.2 ∧ 
    if_None e (s1 = s2 ∧ s1.1 = s1.2) ∧ 
    if_Some e (λ e, s1.1 = e ∧ s2.1 = (s1.1 + 1)%Z ∧ s1.1 < s1.2)⌝%I")]
impl Iterator for MyRange {
    type Item = usize; 

    #[rr::default_spec]
    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let res = self.start;
            self.start += 1;
            Some(res)
        }
        else {
            None
        }
    }
}

//impl IntoIterator for MyRange {
    //type Item = usize;
    //type IntoIter = MyRange;

    //fn into_iterator(self) -> Self::IntoIter {
        //self
    //}
//}

#[rr::trust_me]
fn loop4_myrange() {
    let mut x = 0;
    
    let r = MyRange {
        start: 0,
        end: 10,
    };
    for i in r {

        // let's use Iter to refer to the current iterator state.
        let _ = #[rr::exists("i")]
        #[rr::inv_var("{Iter}": "#i")]
        #[rr::inv("x = sum_list (seq 0 i.(start))")]
        #[rr::ignore] ||{};
        // This version should go through directly.
    
        // alternative: let's use history
        let _ =
        #[rr::inv("x = sum_list {Hist}")]
        #[rr::ignore] ||{};
        // for this version, I'll need an inductive proof about Next in the end, I think.

        x += i;
    }
}


//#[rr::verify]
fn loop4() {
    let mut x = 0;
    
    for i in 0..10 {

        // let's use Iter to refer to the current iterator state.
        let _ = #[rr::exists("i")]
        #[rr::inv_var("{Iter}": "#i")]
        #[rr::inv("x = sum_list (seq 0 i.(start))")]
        #[rr::ignore] ||{};
        // This version should go through directly.
    
        // alternative: let's use history
        let _ =
        #[rr::inv("x = sum_list {Hist}")]
        #[rr::ignore] ||{};
        // for this version, I'll need an inductive proof about Next in the end, I think.

        x += i;
    }
}

/*
trait RecBla {
    type Bla : RecBla;

    #[rr::exists("y")]
    #[rr::returns("y")]
    fn mk(&self) -> Self::Bla;

    // TODO how does this work? 
    //#[rr::verify]
    //fn evil(&self, x: <Self::Bla as RecBla>::Bla);
}

// I guess this is okay. mk doesn't actually have a requirement for Bla to satisfy RecBla.
#[rr::verify]
fn recbla_test<T: RecBla>(x: T) {
    // all of the nested trait requirements are contained in the requirement on T.

    // Maybe I need a bundled version of trait requirements that can encapsulate the types properly.
    // + i.e., a trait requirement also comes with a record of semantic types which in turn satisfy
    //     a trait requirement
    //   needs step-indexing..

    let y = x.mk();
    //let z = y.mk();
    //x.evil(z);
    //let w = z.mk();
}
*/

/*
#[rr::verify]
fn call_recbla_test<T: RecBla>(x: T) {
    // I guess when I assemble T : RecBla, 
    // there is some recursive construction going on that must terminate after finitely many steps.
    // (by reaching an associated type Bla for which the RecBla instance has a fixpoint on the Bla
    // instantiation, or by having a blanket implementation, I guess)

    recbla_test(x);
}
*/

// Options: 
//
