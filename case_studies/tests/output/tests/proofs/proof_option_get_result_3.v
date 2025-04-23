From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_option_get_result_3.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma option_get_result_3_proof (π : thread_id) :
  option_get_result_3_lemma π.
Proof.
  option_get_result_3_prelude.

  rep liRStep; liShow.
  (*
    iApply type_read_ofty_copy.
    { simpl. apply enum_t_copyable.
      intros. destruct r; simpl. 
      - apply _. 
      - apply struct_t_copy.
        constructor; last apply _. 
        apply enum_t_copyable.
        intros []. apply _.
    } 
  repeat liRStep. 
   *)

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  

  (* What is a good way to handle Copyable? *)
  (* 
     - Maybe let's just do some manual hackery.
     - Cleaner: allow attributes to depend on semty, and implement it via trait attrs.

      Q: can we put it in the trait_incl requirements that we anyways have? (and make it a kindof semantic assumption?)
      - Why do that instead of just hard-coding it in the spec? 
        + because of generic specialization of specs of default specs.
      - I moved the trait incl there to allow cyclic impls.

      In this case however it doesn't matter that we put it for the actual generics.
      I need to show that it is Copy.
      I guess I could put it there though. (Q: default stuff doesn't have trait incls now, right?)
      So let's just add it to the spec for now.


    Implementation plan: 
    - we represent builtin traits in GenericScope, somehow.
     + TODO: figure out details. maybe we just have a marker for a trait assumption that says whether its Copy. 
    - alternative: we add general support for semantic requirements on Self. 
       this might be neater and more general. It's an optional definition that every trait can declare.
       If we assume a trait somewhere (in a function), we assume it. 
       If I implement an impl, I need to prove it.
       Maybe for now restrict this to just the Self type.
       + then we have a general mechanism for when to generate Copy/Send/Sync etc.
    - if a function requires copyable, we add it as a semantic assumption.
      

   *)


  (* What is a good way to handle other traits like Send, Sync? *)



  Unshelve. all: print_remaining_sidecond.
Admitted.
End proof.
