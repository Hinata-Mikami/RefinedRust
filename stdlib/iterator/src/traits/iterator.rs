
//use core::iter::Map;
use crate::adapters::map::Map;
use std::ops::Try;


#[rr::export_as(core::iter::traits::Iterator)]

// TODO: better syntax for {rt_of T} ? Infer coercions automatically?

// example for state changes on None:
// - fusing iterator (make any iterator Fused)
//
// potential follow-on papers (and use case for refined trait specifications):
// classification of iterator properties that clients might expect to hold and what implementations typically satisfy?


/// Spec: A relation
#[rr::exists("Next" : "{rt_of Self} (* current state *) → option {rt_of Item} (* next element to emit *) → {rt_of Self} (* next state *) → iProp Σ")]
/// Spec: the refinement needs to admit a relation specifying the history of emitted elements

/// Avi: should this be a list of options?
/// for fused iterators, we shouldn't need it -> use case for refinements.
//#[rr::exists("History" : "{rt_of Self} → list (option {rt_of Self::Item}) → iProp Σ")]
/// Spec: Next should be consistent with the history
//#[rr::exists("NextConsistent" : "∀ s e s' h, ⊢ Next s e s' -∗ History s h -∗ History s' (e :: h)")]
#[rr::exists("History" : "{rt_of Self} → list (option {rt_of Self::Item})")]
/// Spec: Next should be consistent with the history
#[rr::exists("NextConsistent" : "∀ s e s', ⊢ Next s e s' -∗ ⌜History s' = e :: History s⌝")]
pub trait Iterator {
    type Item;

    #[rr::params("it_state" : "{rt_of Self}", "γ")]
    #[rr::args("(#it_state, γ)")]
    /// Postcondition: There exists an optional next item and the successor state of the iterator.
    #[rr::exists("x" : "option {rt_of Item}", "new_it_state" : "{rt_of Self}")]
    /// Postcondition: If there is a next item, it obeys the iterator's relation, and similarly the
    /// successor state is determined.
    #[rr::ensures(#iris "Next it_state x new_it_state")]
    /// Postcondition: The state of the iterator has been updated.
    #[rr::observe("γ": "new_it_state")]
    /// Postcondition: We return the optional next element.
    #[rr::returns("<#>@{option} x")]
    fn next(&mut self) -> Option<Self::Item>;

    /// We pick an invariant Inv
    /// TODO: maybe release Inv when we drop the Map iterator
    #[rr::params("it_state" : "{rt_of Self}", "clos_state" : "{rt_of F}", "Inv" : "{rt_of I} → {rt_of F} → iProp Σ")]
    #[rr::args("it_state", "clos_state")]
    /// Precondition: The picked invariant should hold initially.
    #[rr::requires(#iris "Inv it_state clos_state")]
    /// Precondition: persistently, each iteration preserves the invariant.
    /// If the inner iterator has been advanced, we can call the closure.
    #[rr::requires(#iris "□ (∀ it_state it_state' clos_state e,
        {Self.Next} it_state (Some e) it_state' -∗
        Inv it_state clos_state -∗
        {F.Pre} clos_state e ∗
        (∀ e' clos_state', {F.Post} clos_state e clos_state' e' -∗ Inv it_state' clos_state'))")]
    /// Precondition: If no element is emitted, the invariant is also upheld.
    #[rr::requires(#iris "□ (∀ it_state it_state' clos_state e,
        {Self.Next} it_state None it_state' -∗
        Inv it_state clos_state -∗
        Inv it_state' clos_state)")]
    #[rr::returns("mk_map [] it_state")]
    fn map<B, F>(self,
        f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> B,
    {
        Map::new(self, f)
    }

    /// Specification: we iterate until we fail. 
    /// Postcondition: we get a bigsep of the postconditions of the closure calls that succeeded.
    fn try_for_each<F, R>(&mut self, f: F) -> R
    where
        Self: Sized,
        F: FnMut(Self::Item) -> R,
        R: Try<Output = ()>,
    {
        #[inline]
        fn call<T, R>(mut f: impl FnMut(T) -> R) -> impl FnMut((), T) -> R {
            move |(), x| f(x)
        }

        unimplemented!();
        //self.try_fold((), call(f))
    }


    // TODO: more methods
    // Basically, we should have a common interface for types implementing the Iterator trait, and
    // when we generate a specific instantiation, we want to instantiate that interface.
}


mod extensions {
// Iterator doesn't have DoneDec. But here we can add it.
#[rr::trait_extension]
#[rr::exists("DoneDec")]

trait IteratorRefinement : Iterator {

    // we should be able to override the default spec of Iterator
    //
    // look at depth and width subtyping.
    // - width lets you add new fields  : add new functions in a subtrait
    // - depth lets you subtype fields : override specs of existing functions
    // - generally want both
    //
    // How does relate to subtrait relationships at the specification level?
    // - we generally want depth subtyping at the spec level, but could allow both (warn if there's width subtyping?)
    //
    // This would be a really nice usability thing: we wouldn't be restricted to just one kind of spec.

    // Problem: we cannot get depth subtyping in Rust, this isn't really native in Rust.
    // We could try to get something like a marker trait which doesn't have extra Rust-level things
    // but just marks that we should override certain specs. 
    // This would involve some hackery and isn't quite what Rust programmers might expect.

    // Or give some quirky name to this.
    #[rr::ensures(...)]
    fn _next(&mut self) -> Option<<Self as Iterator>::Item> {
        self.next()
    }
}

// use the more restricted spec
#[rr::spec_as(Iterator -> IteratorRefinement)]
fn test_iterator_ext<T>(mut x: T) where T: Iterator {
    // Problem: if both traits are in scope, we cannot call .next anymore, as both traits are in scope.

    //x.next();
}


// Instead: define a marker trait that says that we should use the overridden specifications from IteratorRefinement.
// RefinedRust should then copy the specification from IteratorRefinement.
#[rr::copy_from(IteratorRefinement)]
pub trait IteratorRefinementImpl where Self: Iterator { }


// also for erroneous impls of Iterator/FusedIterator.
// It might be useful to say at the spec level something is a FusedIterator even if the Rust code doesn't.

#[rr::spec_as(Iterator: IteratorRefinement)] 
fn test_iterator_ext2<T>(mut x: T) where T: Iterator {
    // This should use the spec from IteratorRefinement
    x.next();
}

// Would be nice if we can easily write that.
// Need to think of good interface.
//
//
// multiple inheritance? FusedGlobalIterator
// - e.g. we might want to override the spec of different methods in two different extensions.
//   I guess we could implement this, but the whole coherence thing is something we have to
//   implement. It doesnt' come from Rust.

// What happens with impls of the trait?
// - Can I use an impl of IteratorRefinement as an Iterator?
//   + this is necessary for soundness
//   + for this, the spec of IteratorRefinement needs to be an actual refinement of Iterator
// - 

// We could do the same thing for FusedIterator etc.

// Does trait/specification inheritance give us good things?
// TODO think about this.
//  i.e. what if we have a subtrait?
//  Ideally, we want to specify new exists-attributes, and (partially) instantiate the attributes of the super trait.
//  - this seems doable.
//  We also want to override default specifications.
//  - But we do not really have a syntax for that.
//  I guess the problem is that we should not really think of it as inheritance, but as extension. 
//
//
// where clause at the spec level???
//
// is this a generally useful pattern?
//
// Can we override at the mathematical level the specification that is used to use a subspec (of a subtrait)?
// -> Yeah, that's doable
}


mod experiments {
/*

// Self : Rust type
// {Self} : RefinedRust type
// {rt_of Self} : mathematical type

#[rr::invariant(#iris "have ownership of range between ptr1 and ptr2")]
struct raw_range {
    ptr1: *mut i32,
    ptr2: *mut i32,
}

#[rr::instantiate("Done" := "λ x : (Z, Z), x.0 < x.1")]
#[rr::instantiate("Next" := "λ (s1 : loc * loc) (e : Z) (s2 : loc * loc),
    (s1.0 ↦ e) ∗
    ⌜s1.1 = s2.1⌝ ∗
    ⌜s2.0 = s1.0 + sizeof(i32)⌝ ∗
    ")]
impl Iterator for raw_range {
    type Item = i32;

    fn next(&mut self) -> Option<u32> {
        if self.0 < self.1 {
            let e = self.0;
            self.0 += 1;
            Some(e)
        }
        else {
            None
        }
    }
}
// This kind of example might also come up for trees with pointers.

#[rr::refined_by("ptr" : "loc")]
//#[rr::refined_by("vals" : "list Z")]
#[rr::exists("vals" : "list Z")]
#[rr::invariant(#iris "[∗ list] i ↦ val ∈ vals: ptr +ₗ i ↦ val")]
#[rr::invariant(#iris "last vals = 0")]
#[rr::invariant(#iris "∀ i < length vals, vals[i] ≠ 0")]
struct null_str {
    ptr: *mut i32,
}

// implicit dynamic frames style??
// Done is in Prop because it states something about the datastructure (we cannot state ownership about it);
// Next states something about the returned value, so we should be able to assert ownership
#[rr::instantiate("Done" := "λ x : (loc), l ↦_unowned 0")]
#[rr::instantiate("Next" := "λ (s1 : loc * loc) (e : Z) (s2 : loc * loc),
    (s1.0 ↦ e) ∗
    ⌜s1.1 = s2.1⌝ ∗
    ⌜s2.0 = s1.0 + sizeof(i32)⌝ ∗
    ")]
impl Iterator for null_str {
    type Item = i32;

    fn next(&mut self) -> Option<u32> {
        if self.0 < self.1 {
            let e = self.0;
            self.0 += 1;
            Some(e)
        }
        else {
            None
        }
    }
}
*/

// Avi: What if we had an iterator which can't be called anytime (next has extra preconditions)
//
// The style of having to assert ownership through a struct invariant might lead to additional
// work, e.g. when interfacing with C. We'd first have to wrap it in the struct, etc.
// Limitation!
// TODO Can we think about lifting that limitation? More expressive/crazy impl of Iterator?
//
//
//
// Expressivity lemma? Can we say that we can specify any iterator you can write in Rust?
// Is our spec complete?
//  It would be good to say that our spec handles everything.
//  Add extra stuff to make it fully expressive if it disappears when you don't need it.
//  We shouldn't loose anything from user's POV.
// TODO think about this.
// If we make Iterator more expressive, how do we change map?
// Are there design patterns?

// Avi: we should be able to infer more things in the types.

//#[rr::refined_by("cur, bound")]
//#[rr::invariant("cur < bound")]
//struct Seq {
    //cur: i32,
    //bound: i32,
//}

//#[rr::instantiate("Done" := "λ (cur, bound), cur = bound")]
//#[rr::instantiate("Next" := " λ (cur, bound) elem (cur2, bound2), 
    //elem = cur ∧ bound2 = bound ∧ ")]
//impl Iterator for Seq
//{ 

//}


// there is some i, 
// up to i the elements are changed
// after that, the elements are unchanged
/*
fn mutex_iter(mut x: Vec<Mutex<VmState>>) -> Result<(), MutexError> {
    // TODO check this case in the security monitor out.

    // element type &mut VmState
    // (model of VmState, γ) 
    // after iteration:
    // history [(s1, γ1); ...; (sn, γn)]
    // 
    // x now has elements [*γ1; ...; *γn]
    //
    for m in x.iter_mut() {
        let state = m.acquire()?;

    }
    Ok(())

}
*/


/*
use std::collections::HashMap;

type VmId = usize;
fn mutex_iter2(mut x: HashMap<VmId, Mutex<VmState>>) {
    //x.get_mut(id)
    
    for (k, v) in &mut x {
        if k % 2 {
            // mutate v

        }
    }
}
*/



// For loop encoding: 
// - we should keep track of the history.
// - We should be able to access the history in the spec
//
//


fn loop_iter_test_seq_1() {
    let mut sum = 0;

    #[rr::exists("sum_z" : "Z")]
    #[rr::invariant("sum" : "sum_z")]
    // TODO it would be really good to get rid of that. This should be an implied constraint of the
    // iterator state being reachable from the initial state.
    #[rr::invariant("{iter}" : "iter.bound = 10")]
    #[rr::invariant("sum_z = sum_list history")]
    for i in 0..10 {
        // here we call next. we get a new element, and know that the history has the new element
        // consed. 
        // So we can re-establish the invariant.
        //
        // Note: for our concrete case, we need to know that the integers are in range 0..10 to
        // prevent overflows. This is guaranteed by each element's next relation.
        //
        // Do we need an invariant on the iterator state? I guess we should know that the maximum
        // up to which we iterate stays 10.
        // 
        // We could get that by requiring a transitive reaches relation.
        // However, then we need an inductive proof that that part (the bound) stays the same.
        // We could explicitly specify the reaches relation, instead of defining it implicitly? 
        // Then we could always have as an invariant that the current iterator state is reachable.
        // 
        // Then we need to prove inductively that Next is consistent with reachability.
        //
        sum += i; 
    }
}

fn loop_iter_test_vec_1() {
    let mut v = vec![1, 2, 3]; 

    // the elements emitted so far have been resolved
    #[rr::invariant("[∗ list] x ∈ history, gvar_pobs x.1 (1+x.2)")]
    for x in &mut v {
        // we also need to know that all elements of the vector are in range to enable safe addition.
        *x += 1;
    }
    // when the iterator is done, I need to know that the history has a particular length.
}

}
