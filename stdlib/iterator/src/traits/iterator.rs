
#![rr::import("rrstd.iterator.theories", "iterator")]

//use crate::adapters::map::Map;
//use std::ops::Try;

use crate::adapters::map::Map;

// example for state changes on None:
// - fusing iterator (make any iterator Fused)

/// Spec: A relation
#[rr::export_as(core::iter::Iterator)]
#[rr::exists("Next" : "thread_id → {xt_of Self} → option {xt_of Item} → {xt_of Self} → iProp Σ")]
pub trait Iterator {
    type Item;

    /// Postcondition: There exists an optional next item and the successor state of the iterator.
    #[rr::exists("new_it_state" : "{xt_of Self}")]
    /// Postcondition: The state of the iterator has been updated.
    #[rr::observe("self.ghost": "($# new_it_state)")]
    /// Postcondition: If there is a next item, it obeys the iterator's relation, and similarly the
    /// successor state is determined.
    #[rr::ensures(#iris "{Next} π self.cur ret new_it_state")]
    fn next(&mut self) -> Option<Self::Item>;

    /// We pick an invariant Inv
    /// TODO: maybe release Inv when we drop the Map iterator
    #[rr::trust_me]
    #[rr::params("Inv" : "thread_id → {xt_of Self} → {xt_of F} → iProp Σ")]
    /// Precondition: The picked invariant should hold initially.
    #[rr::requires(#iris "Inv π self f")]
    /// Precondition: persistently, each iteration preserves the invariant.
    /// If the inner iterator has been advanced, we can call the closure.
    #[rr::requires(#iris "□ (∀ it_state it_state' clos_state e,
        {Self::Next} π it_state (Some e) it_state' -∗
        Inv π it_state clos_state -∗
        {F::Pre} π clos_state *[e] ∗
        (∀ e' clos_state', {F::PostMut} π clos_state *[e] clos_state' e' -∗ Inv π it_state' clos_state'))")]
    /// Precondition: If no element is emitted, the invariant is also upheld.
    #[rr::requires(#iris "□ (∀ it_state it_state' clos_state,
        {Self::Next} π it_state None it_state' -∗
        Inv π it_state clos_state -∗
        Inv π it_state' clos_state)")]
    #[rr::returns("mk_map_x self f")]
    fn map<B, F>(self, f: F) -> Map<B, Self, F>
    where
        Self: Sized,
        F: FnMut(Self::Item) -> B,
    {
        Map::new(self, f)
    }

    /*
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
    */

    #[rr::trust_me]
    #[rr::exists("seq", "s2", "s2'")]
    // TODO: have an escape to refer to the attrs record instead
    #[rr::ensures(#iris "IteratorNextFusedTrans traits_iterator_Iterator_Self_spec_attrs π self seq s2")]
    #[rr::ensures(#iris "{Next} π s2 None s2'")]
    #[rr::returns("{B::FromSequence} seq")]
    fn collect<B: FromIterator<Self::Item>>(self) -> B
    where
        Self: Sized,
    {
        // This is too aggressive to turn on for everything all the time, but PR#137908
        // accidentally noticed that some rustc iterators had malformed `size_hint`s,
        // so this will help catch such things in debug-assertions-std runners,
        // even if users won't actually ever see it.
        //if cfg!(debug_assertions) {
            //let hint = self.size_hint();
            //assert!(hint.1.is_none_or(|high| high >= hint.0), "Malformed size_hint {hint:?}");
        //}

        FromIterator::from_iter(self)
    }


    // TODO: more methods
}

#[rr::export_as(core::iter::IntoIterator)]
#[rr::exists("IntoIter" : "{xt_of Self} → {xt_of IntoIter}")]
pub trait IntoIterator {
    /// The type of the elements being iterated over.
    type Item;

    /// Which kind of iterator are we turning this into?
    type IntoIter: Iterator<Item = Self::Item>;

    #[rr::returns("{IntoIter} self")]
    fn into_iter(self) -> Self::IntoIter;
}

#[rr::instantiate("IntoIter" := "id")]
impl<I> IntoIterator for I where I: Iterator {
    type Item = <I as Iterator>::Item;
    type IntoIter = I;

    #[rr::default_spec]
    fn into_iter(self) -> I {
        self
    }
}


#[rr::export_as(core::iter::FromIterator)]
#[rr::exists("FromSequence" : "list ({xt_of A}) → {xt_of Self}")]
pub trait FromIterator<A> {
    #[rr::verify]
    //#[rr::exists("seq", "s2", "s2'")]
    // Problem: RefinedRust currently does not translate the Iterator requirement on T::IntoIter. 
    // Maybe let's do a hacky wrapper solution for that for now. 
    //#[rr::ensures(#iris "IteratorNextFusedTrans {attrs_of T::IntoIter} ({T::IntoIter} iter) seq s2")]
    //#[rr::ensures(#iris "{T::Next} s2 None s2'")]
    //#[rr::returns("{FromSequence} seq")]
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self;
}
