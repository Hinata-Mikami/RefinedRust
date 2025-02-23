Section trans.
  
  Fixpoint IteratorNextFusedTrans {Self_rt Item_rt : Type} 
    (attrs : traits_iterator_Iterator_spec_attrs Self_rt Item_rt)
    (s1 : Self_rt) (els : list (Item_rt)) (s2 : Self_rt) : iProp Σ
    :=
    match els with
    | [] => ⌜s1 = s2⌝
    | (e1 :: els) => 
      ∃ s1', 
        attrs.(traits_iterator_Iterator_Next) s1 (Some e1) s1' ∗
        IteratorNextFusedTrans attrs s1' els s2
    end.

  (* Steps for loops with iterators:
     - set a variable with the initial state in the context
       (we need a special identifier for that, I guess?)
     - add invariant using IteratorNextFusedTrans from the initial state to the current iterator state.
       

     Frontend: 
     - identify that we have a for loop
     - find the iterator variable
     - add it to the set of variables we need an invariant on
     - etc. 

   *)

  (* TODO: we might need some Lithium instances to automate the SL reasoning here. 
     Is Next opaque for us? I guess it should unfold. Let's just see how it works.
  *)


End trans.
