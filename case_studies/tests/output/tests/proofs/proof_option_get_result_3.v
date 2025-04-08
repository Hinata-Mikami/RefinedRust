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

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  

  (* What is a good way to handle Copyable? *)
  (* 
     - Maybe let's just do some manual hackery.
     - Cleaner: allow attributes to depend on semty, and implement it via trait attrs.
     TODO.

   *)


  (* What is a good way to handle other traits like Send, Sync? *)



  Unshelve. all: print_remaining_sidecond.
Admitted.
End proof.
