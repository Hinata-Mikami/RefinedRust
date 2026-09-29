From radium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.clone.clone.generated Require Export generated_specs_clone.
From rrstd.mem.mem.generated Require Export generated_specs_mem.
From rrstd.num.num.generated Require Export generated_specs_num.
From rrstd.option.option.generated Require Export generated_specs_option.
From rrstd.ptr.theories Require Export alignment shims specs.
From rrstd.ptr.ptr Require Export generated_code_ptr.

Section alignment_AlignmentEnum_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Section components.
    Definition alignment_AlignmentEnum__Align1Shl0_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl0_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl0_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl0_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl0_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl0_ty.
    Definition alignment_AlignmentEnum__Align1Shl1_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl1_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl1_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl1_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl1_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl1_ty.
    Definition alignment_AlignmentEnum__Align1Shl2_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl2_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl2_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl2_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl2_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl2_ty.
    Definition alignment_AlignmentEnum__Align1Shl3_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl3_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl3_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl3_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl3_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl3_ty.
    Definition alignment_AlignmentEnum__Align1Shl4_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl4_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl4_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl4_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl4_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl4_ty.
    Definition alignment_AlignmentEnum__Align1Shl5_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl5_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl5_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl5_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl5_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl5_ty.
    Definition alignment_AlignmentEnum__Align1Shl6_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl6_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl6_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl6_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl6_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl6_ty.
    Definition alignment_AlignmentEnum__Align1Shl7_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl7_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl7_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl7_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl7_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl7_ty.
    Definition alignment_AlignmentEnum__Align1Shl8_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl8_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl8_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl8_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl8_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl8_ty.
    Definition alignment_AlignmentEnum__Align1Shl9_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl9_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl9_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl9_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl9_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl9_ty.
    Definition alignment_AlignmentEnum__Align1Shl10_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl10_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl10_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl10_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl10_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl10_ty.
    Definition alignment_AlignmentEnum__Align1Shl11_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl11_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl11_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl11_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl11_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl11_ty.
    Definition alignment_AlignmentEnum__Align1Shl12_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl12_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl12_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl12_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl12_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl12_ty.
    Definition alignment_AlignmentEnum__Align1Shl13_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl13_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl13_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl13_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl13_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl13_ty.
    Definition alignment_AlignmentEnum__Align1Shl14_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl14_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl14_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl14_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl14_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl14_ty.
    Definition alignment_AlignmentEnum__Align1Shl15_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl15_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl15_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl15_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl15_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl15_ty.
    Definition alignment_AlignmentEnum__Align1Shl16_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl16_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl16_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl16_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl16_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl16_ty.
    Definition alignment_AlignmentEnum__Align1Shl17_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl17_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl17_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl17_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl17_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl17_ty.
    Definition alignment_AlignmentEnum__Align1Shl18_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl18_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl18_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl18_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl18_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl18_ty.
    Definition alignment_AlignmentEnum__Align1Shl19_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl19_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl19_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl19_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl19_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl19_ty.
    Definition alignment_AlignmentEnum__Align1Shl20_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl20_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl20_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl20_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl20_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl20_ty.
    Definition alignment_AlignmentEnum__Align1Shl21_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl21_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl21_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl21_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl21_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl21_ty.
    Definition alignment_AlignmentEnum__Align1Shl22_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl22_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl22_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl22_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl22_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl22_ty.
    Definition alignment_AlignmentEnum__Align1Shl23_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl23_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl23_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl23_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl23_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl23_ty.
    Definition alignment_AlignmentEnum__Align1Shl24_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl24_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl24_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl24_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl24_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl24_ty.
    Definition alignment_AlignmentEnum__Align1Shl25_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl25_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl25_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl25_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl25_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl25_ty.
    Definition alignment_AlignmentEnum__Align1Shl26_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl26_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl26_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl26_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl26_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl26_ty.
    Definition alignment_AlignmentEnum__Align1Shl27_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl27_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl27_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl27_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl27_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl27_ty.
    Definition alignment_AlignmentEnum__Align1Shl28_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl28_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl28_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl28_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl28_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl28_ty.
    Definition alignment_AlignmentEnum__Align1Shl29_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl29_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl29_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl29_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl29_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl29_ty.
    Definition alignment_AlignmentEnum__Align1Shl30_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl30_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl30_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl30_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl30_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl30_ty.
    Definition alignment_AlignmentEnum__Align1Shl31_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl31_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl31_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl31_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl31_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl31_ty.
    Definition alignment_AlignmentEnum__Align1Shl32_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl32_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl32_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl32_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl32_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl32_ty.
    Definition alignment_AlignmentEnum__Align1Shl33_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl33_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl33_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl33_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl33_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl33_ty.
    Definition alignment_AlignmentEnum__Align1Shl34_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl34_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl34_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl34_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl34_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl34_ty.
    Definition alignment_AlignmentEnum__Align1Shl35_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl35_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl35_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl35_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl35_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl35_ty.
    Definition alignment_AlignmentEnum__Align1Shl36_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl36_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl36_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl36_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl36_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl36_ty.
    Definition alignment_AlignmentEnum__Align1Shl37_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl37_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl37_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl37_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl37_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl37_ty.
    Definition alignment_AlignmentEnum__Align1Shl38_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl38_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl38_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl38_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl38_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl38_ty.
    Definition alignment_AlignmentEnum__Align1Shl39_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl39_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl39_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl39_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl39_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl39_ty.
    Definition alignment_AlignmentEnum__Align1Shl40_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl40_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl40_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl40_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl40_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl40_ty.
    Definition alignment_AlignmentEnum__Align1Shl41_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl41_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl41_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl41_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl41_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl41_ty.
    Definition alignment_AlignmentEnum__Align1Shl42_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl42_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl42_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl42_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl42_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl42_ty.
    Definition alignment_AlignmentEnum__Align1Shl43_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl43_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl43_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl43_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl43_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl43_ty.
    Definition alignment_AlignmentEnum__Align1Shl44_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl44_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl44_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl44_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl44_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl44_ty.
    Definition alignment_AlignmentEnum__Align1Shl45_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl45_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl45_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl45_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl45_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl45_ty.
    Definition alignment_AlignmentEnum__Align1Shl46_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl46_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl46_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl46_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl46_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl46_ty.
    Definition alignment_AlignmentEnum__Align1Shl47_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl47_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl47_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl47_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl47_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl47_ty.
    Definition alignment_AlignmentEnum__Align1Shl48_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl48_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl48_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl48_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl48_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl48_ty.
    Definition alignment_AlignmentEnum__Align1Shl49_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl49_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl49_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl49_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl49_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl49_ty.
    Definition alignment_AlignmentEnum__Align1Shl50_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl50_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl50_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl50_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl50_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl50_ty.
    Definition alignment_AlignmentEnum__Align1Shl51_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl51_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl51_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl51_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl51_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl51_ty.
    Definition alignment_AlignmentEnum__Align1Shl52_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl52_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl52_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl52_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl52_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl52_ty.
    Definition alignment_AlignmentEnum__Align1Shl53_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl53_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl53_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl53_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl53_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl53_ty.
    Definition alignment_AlignmentEnum__Align1Shl54_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl54_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl54_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl54_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl54_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl54_ty.
    Definition alignment_AlignmentEnum__Align1Shl55_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl55_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl55_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl55_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl55_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl55_ty.
    Definition alignment_AlignmentEnum__Align1Shl56_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl56_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl56_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl56_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl56_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl56_ty.
    Definition alignment_AlignmentEnum__Align1Shl57_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl57_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl57_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl57_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl57_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl57_ty.
    Definition alignment_AlignmentEnum__Align1Shl58_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl58_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl58_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl58_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl58_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl58_ty.
    Definition alignment_AlignmentEnum__Align1Shl59_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl59_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl59_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl59_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl59_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl59_ty.
    Definition alignment_AlignmentEnum__Align1Shl60_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl60_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl60_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl60_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl60_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl60_ty.
    Definition alignment_AlignmentEnum__Align1Shl61_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl61_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl61_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl61_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl61_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl61_ty.
    Definition alignment_AlignmentEnum__Align1Shl62_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl62_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl62_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl62_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl62_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl62_ty.
    Definition alignment_AlignmentEnum__Align1Shl63_ty  : (spec_with 0 [] ((type (plist place_rfnRT [])))).
    Proof.
      exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_AlignmentEnum__Align1Shl63_sls +[])).
    Defined.

    Definition alignment_AlignmentEnum__Align1Shl63_rt  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum__Align1Shl63_ty)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl63_rt.
    #[global] Typeclasses Transparent alignment_AlignmentEnum__Align1Shl63_ty.
    Definition alignment_AlignmentEnum_enum_rt  :=
      λ rfn : (alignment_enum), match rfn with | _Align1Shl0 => alignment_AlignmentEnum__Align1Shl0_rt| _Align1Shl1 => alignment_AlignmentEnum__Align1Shl1_rt| _Align1Shl2 => alignment_AlignmentEnum__Align1Shl2_rt| _Align1Shl3 => alignment_AlignmentEnum__Align1Shl3_rt| _Align1Shl4 => alignment_AlignmentEnum__Align1Shl4_rt| _Align1Shl5 => alignment_AlignmentEnum__Align1Shl5_rt| _Align1Shl6 => alignment_AlignmentEnum__Align1Shl6_rt| _Align1Shl7 => alignment_AlignmentEnum__Align1Shl7_rt| _Align1Shl8 => alignment_AlignmentEnum__Align1Shl8_rt| _Align1Shl9 => alignment_AlignmentEnum__Align1Shl9_rt| _Align1Shl10 => alignment_AlignmentEnum__Align1Shl10_rt| _Align1Shl11 => alignment_AlignmentEnum__Align1Shl11_rt| _Align1Shl12 => alignment_AlignmentEnum__Align1Shl12_rt| _Align1Shl13 => alignment_AlignmentEnum__Align1Shl13_rt| _Align1Shl14 => alignment_AlignmentEnum__Align1Shl14_rt| _Align1Shl15 => alignment_AlignmentEnum__Align1Shl15_rt| _Align1Shl16 => alignment_AlignmentEnum__Align1Shl16_rt| _Align1Shl17 => alignment_AlignmentEnum__Align1Shl17_rt| _Align1Shl18 => alignment_AlignmentEnum__Align1Shl18_rt| _Align1Shl19 => alignment_AlignmentEnum__Align1Shl19_rt| _Align1Shl20 => alignment_AlignmentEnum__Align1Shl20_rt| _Align1Shl21 => alignment_AlignmentEnum__Align1Shl21_rt| _Align1Shl22 => alignment_AlignmentEnum__Align1Shl22_rt| _Align1Shl23 => alignment_AlignmentEnum__Align1Shl23_rt| _Align1Shl24 => alignment_AlignmentEnum__Align1Shl24_rt| _Align1Shl25 => alignment_AlignmentEnum__Align1Shl25_rt| _Align1Shl26 => alignment_AlignmentEnum__Align1Shl26_rt| _Align1Shl27 => alignment_AlignmentEnum__Align1Shl27_rt| _Align1Shl28 => alignment_AlignmentEnum__Align1Shl28_rt| _Align1Shl29 => alignment_AlignmentEnum__Align1Shl29_rt| _Align1Shl30 => alignment_AlignmentEnum__Align1Shl30_rt| _Align1Shl31 => alignment_AlignmentEnum__Align1Shl31_rt| _Align1Shl32 => alignment_AlignmentEnum__Align1Shl32_rt| _Align1Shl33 => alignment_AlignmentEnum__Align1Shl33_rt| _Align1Shl34 => alignment_AlignmentEnum__Align1Shl34_rt| _Align1Shl35 => alignment_AlignmentEnum__Align1Shl35_rt| _Align1Shl36 => alignment_AlignmentEnum__Align1Shl36_rt| _Align1Shl37 => alignment_AlignmentEnum__Align1Shl37_rt| _Align1Shl38 => alignment_AlignmentEnum__Align1Shl38_rt| _Align1Shl39 => alignment_AlignmentEnum__Align1Shl39_rt| _Align1Shl40 => alignment_AlignmentEnum__Align1Shl40_rt| _Align1Shl41 => alignment_AlignmentEnum__Align1Shl41_rt| _Align1Shl42 => alignment_AlignmentEnum__Align1Shl42_rt| _Align1Shl43 => alignment_AlignmentEnum__Align1Shl43_rt| _Align1Shl44 => alignment_AlignmentEnum__Align1Shl44_rt| _Align1Shl45 => alignment_AlignmentEnum__Align1Shl45_rt| _Align1Shl46 => alignment_AlignmentEnum__Align1Shl46_rt| _Align1Shl47 => alignment_AlignmentEnum__Align1Shl47_rt| _Align1Shl48 => alignment_AlignmentEnum__Align1Shl48_rt| _Align1Shl49 => alignment_AlignmentEnum__Align1Shl49_rt| _Align1Shl50 => alignment_AlignmentEnum__Align1Shl50_rt| _Align1Shl51 => alignment_AlignmentEnum__Align1Shl51_rt| _Align1Shl52 => alignment_AlignmentEnum__Align1Shl52_rt| _Align1Shl53 => alignment_AlignmentEnum__Align1Shl53_rt| _Align1Shl54 => alignment_AlignmentEnum__Align1Shl54_rt| _Align1Shl55 => alignment_AlignmentEnum__Align1Shl55_rt| _Align1Shl56 => alignment_AlignmentEnum__Align1Shl56_rt| _Align1Shl57 => alignment_AlignmentEnum__Align1Shl57_rt| _Align1Shl58 => alignment_AlignmentEnum__Align1Shl58_rt| _Align1Shl59 => alignment_AlignmentEnum__Align1Shl59_rt| _Align1Shl60 => alignment_AlignmentEnum__Align1Shl60_rt| _Align1Shl61 => alignment_AlignmentEnum__Align1Shl61_rt| _Align1Shl62 => alignment_AlignmentEnum__Align1Shl62_rt| _Align1Shl63 => alignment_AlignmentEnum__Align1Shl63_rt end.
    Definition alignment_AlignmentEnum_enum_ty  : (spec_with 0 [] (∀ (x: _), (type (alignment_AlignmentEnum_enum_rt (x))))) :=
      spec! ( *[]) : 0 | ( *[]) : ([] : list RT), λ rfn, match rfn as x return type (alignment_AlignmentEnum_enum_rt x) with | _Align1Shl0 => alignment_AlignmentEnum__Align1Shl0_ty -[] -[]| _Align1Shl1 => alignment_AlignmentEnum__Align1Shl1_ty -[] -[]| _Align1Shl2 => alignment_AlignmentEnum__Align1Shl2_ty -[] -[]| _Align1Shl3 => alignment_AlignmentEnum__Align1Shl3_ty -[] -[]| _Align1Shl4 => alignment_AlignmentEnum__Align1Shl4_ty -[] -[]| _Align1Shl5 => alignment_AlignmentEnum__Align1Shl5_ty -[] -[]| _Align1Shl6 => alignment_AlignmentEnum__Align1Shl6_ty -[] -[]| _Align1Shl7 => alignment_AlignmentEnum__Align1Shl7_ty -[] -[]| _Align1Shl8 => alignment_AlignmentEnum__Align1Shl8_ty -[] -[]| _Align1Shl9 => alignment_AlignmentEnum__Align1Shl9_ty -[] -[]| _Align1Shl10 => alignment_AlignmentEnum__Align1Shl10_ty -[] -[]| _Align1Shl11 => alignment_AlignmentEnum__Align1Shl11_ty -[] -[]| _Align1Shl12 => alignment_AlignmentEnum__Align1Shl12_ty -[] -[]| _Align1Shl13 => alignment_AlignmentEnum__Align1Shl13_ty -[] -[]| _Align1Shl14 => alignment_AlignmentEnum__Align1Shl14_ty -[] -[]| _Align1Shl15 => alignment_AlignmentEnum__Align1Shl15_ty -[] -[]| _Align1Shl16 => alignment_AlignmentEnum__Align1Shl16_ty -[] -[]| _Align1Shl17 => alignment_AlignmentEnum__Align1Shl17_ty -[] -[]| _Align1Shl18 => alignment_AlignmentEnum__Align1Shl18_ty -[] -[]| _Align1Shl19 => alignment_AlignmentEnum__Align1Shl19_ty -[] -[]| _Align1Shl20 => alignment_AlignmentEnum__Align1Shl20_ty -[] -[]| _Align1Shl21 => alignment_AlignmentEnum__Align1Shl21_ty -[] -[]| _Align1Shl22 => alignment_AlignmentEnum__Align1Shl22_ty -[] -[]| _Align1Shl23 => alignment_AlignmentEnum__Align1Shl23_ty -[] -[]| _Align1Shl24 => alignment_AlignmentEnum__Align1Shl24_ty -[] -[]| _Align1Shl25 => alignment_AlignmentEnum__Align1Shl25_ty -[] -[]| _Align1Shl26 => alignment_AlignmentEnum__Align1Shl26_ty -[] -[]| _Align1Shl27 => alignment_AlignmentEnum__Align1Shl27_ty -[] -[]| _Align1Shl28 => alignment_AlignmentEnum__Align1Shl28_ty -[] -[]| _Align1Shl29 => alignment_AlignmentEnum__Align1Shl29_ty -[] -[]| _Align1Shl30 => alignment_AlignmentEnum__Align1Shl30_ty -[] -[]| _Align1Shl31 => alignment_AlignmentEnum__Align1Shl31_ty -[] -[]| _Align1Shl32 => alignment_AlignmentEnum__Align1Shl32_ty -[] -[]| _Align1Shl33 => alignment_AlignmentEnum__Align1Shl33_ty -[] -[]| _Align1Shl34 => alignment_AlignmentEnum__Align1Shl34_ty -[] -[]| _Align1Shl35 => alignment_AlignmentEnum__Align1Shl35_ty -[] -[]| _Align1Shl36 => alignment_AlignmentEnum__Align1Shl36_ty -[] -[]| _Align1Shl37 => alignment_AlignmentEnum__Align1Shl37_ty -[] -[]| _Align1Shl38 => alignment_AlignmentEnum__Align1Shl38_ty -[] -[]| _Align1Shl39 => alignment_AlignmentEnum__Align1Shl39_ty -[] -[]| _Align1Shl40 => alignment_AlignmentEnum__Align1Shl40_ty -[] -[]| _Align1Shl41 => alignment_AlignmentEnum__Align1Shl41_ty -[] -[]| _Align1Shl42 => alignment_AlignmentEnum__Align1Shl42_ty -[] -[]| _Align1Shl43 => alignment_AlignmentEnum__Align1Shl43_ty -[] -[]| _Align1Shl44 => alignment_AlignmentEnum__Align1Shl44_ty -[] -[]| _Align1Shl45 => alignment_AlignmentEnum__Align1Shl45_ty -[] -[]| _Align1Shl46 => alignment_AlignmentEnum__Align1Shl46_ty -[] -[]| _Align1Shl47 => alignment_AlignmentEnum__Align1Shl47_ty -[] -[]| _Align1Shl48 => alignment_AlignmentEnum__Align1Shl48_ty -[] -[]| _Align1Shl49 => alignment_AlignmentEnum__Align1Shl49_ty -[] -[]| _Align1Shl50 => alignment_AlignmentEnum__Align1Shl50_ty -[] -[]| _Align1Shl51 => alignment_AlignmentEnum__Align1Shl51_ty -[] -[]| _Align1Shl52 => alignment_AlignmentEnum__Align1Shl52_ty -[] -[]| _Align1Shl53 => alignment_AlignmentEnum__Align1Shl53_ty -[] -[]| _Align1Shl54 => alignment_AlignmentEnum__Align1Shl54_ty -[] -[]| _Align1Shl55 => alignment_AlignmentEnum__Align1Shl55_ty -[] -[]| _Align1Shl56 => alignment_AlignmentEnum__Align1Shl56_ty -[] -[]| _Align1Shl57 => alignment_AlignmentEnum__Align1Shl57_ty -[] -[]| _Align1Shl58 => alignment_AlignmentEnum__Align1Shl58_ty -[] -[]| _Align1Shl59 => alignment_AlignmentEnum__Align1Shl59_ty -[] -[]| _Align1Shl60 => alignment_AlignmentEnum__Align1Shl60_ty -[] -[]| _Align1Shl61 => alignment_AlignmentEnum__Align1Shl61_ty -[] -[]| _Align1Shl62 => alignment_AlignmentEnum__Align1Shl62_ty -[] -[]| _Align1Shl63 => alignment_AlignmentEnum__Align1Shl63_ty -[] -[] end.
    Program Definition alignment_AlignmentEnum_enum  : (spec_with 0 [] ((enum ((alignment_enum))))) :=
      spec! ( *[]) : 0 | ( *[]) : ([] : list RT), mk_enum
        _
        (alignment_AlignmentEnum_els)
        (λ rfn, Some (match rfn with | _Align1Shl0 => "_Align1Shl0" | _Align1Shl1 => "_Align1Shl1" | _Align1Shl2 => "_Align1Shl2" | _Align1Shl3 => "_Align1Shl3" | _Align1Shl4 => "_Align1Shl4" | _Align1Shl5 => "_Align1Shl5" | _Align1Shl6 => "_Align1Shl6" | _Align1Shl7 => "_Align1Shl7" | _Align1Shl8 => "_Align1Shl8" | _Align1Shl9 => "_Align1Shl9" | _Align1Shl10 => "_Align1Shl10" | _Align1Shl11 => "_Align1Shl11" | _Align1Shl12 => "_Align1Shl12" | _Align1Shl13 => "_Align1Shl13" | _Align1Shl14 => "_Align1Shl14" | _Align1Shl15 => "_Align1Shl15" | _Align1Shl16 => "_Align1Shl16" | _Align1Shl17 => "_Align1Shl17" | _Align1Shl18 => "_Align1Shl18" | _Align1Shl19 => "_Align1Shl19" | _Align1Shl20 => "_Align1Shl20" | _Align1Shl21 => "_Align1Shl21" | _Align1Shl22 => "_Align1Shl22" | _Align1Shl23 => "_Align1Shl23" | _Align1Shl24 => "_Align1Shl24" | _Align1Shl25 => "_Align1Shl25" | _Align1Shl26 => "_Align1Shl26" | _Align1Shl27 => "_Align1Shl27" | _Align1Shl28 => "_Align1Shl28" | _Align1Shl29 => "_Align1Shl29" | _Align1Shl30 => "_Align1Shl30" | _Align1Shl31 => "_Align1Shl31" | _Align1Shl32 => "_Align1Shl32" | _Align1Shl33 => "_Align1Shl33" | _Align1Shl34 => "_Align1Shl34" | _Align1Shl35 => "_Align1Shl35" | _Align1Shl36 => "_Align1Shl36" | _Align1Shl37 => "_Align1Shl37" | _Align1Shl38 => "_Align1Shl38" | _Align1Shl39 => "_Align1Shl39" | _Align1Shl40 => "_Align1Shl40" | _Align1Shl41 => "_Align1Shl41" | _Align1Shl42 => "_Align1Shl42" | _Align1Shl43 => "_Align1Shl43" | _Align1Shl44 => "_Align1Shl44" | _Align1Shl45 => "_Align1Shl45" | _Align1Shl46 => "_Align1Shl46" | _Align1Shl47 => "_Align1Shl47" | _Align1Shl48 => "_Align1Shl48" | _Align1Shl49 => "_Align1Shl49" | _Align1Shl50 => "_Align1Shl50" | _Align1Shl51 => "_Align1Shl51" | _Align1Shl52 => "_Align1Shl52" | _Align1Shl53 => "_Align1Shl53" | _Align1Shl54 => "_Align1Shl54" | _Align1Shl55 => "_Align1Shl55" | _Align1Shl56 => "_Align1Shl56" | _Align1Shl57 => "_Align1Shl57" | _Align1Shl58 => "_Align1Shl58" | _Align1Shl59 => "_Align1Shl59" | _Align1Shl60 => "_Align1Shl60" | _Align1Shl61 => "_Align1Shl61" | _Align1Shl62 => "_Align1Shl62" | _Align1Shl63 => "_Align1Shl63" end))
        (alignment_AlignmentEnum_enum_rt)
        (alignment_AlignmentEnum_enum_ty -[] -[])
        (λ rfn, match rfn with | _Align1Shl0 => *[]| _Align1Shl1 => *[]| _Align1Shl2 => *[]| _Align1Shl3 => *[]| _Align1Shl4 => *[]| _Align1Shl5 => *[]| _Align1Shl6 => *[]| _Align1Shl7 => *[]| _Align1Shl8 => *[]| _Align1Shl9 => *[]| _Align1Shl10 => *[]| _Align1Shl11 => *[]| _Align1Shl12 => *[]| _Align1Shl13 => *[]| _Align1Shl14 => *[]| _Align1Shl15 => *[]| _Align1Shl16 => *[]| _Align1Shl17 => *[]| _Align1Shl18 => *[]| _Align1Shl19 => *[]| _Align1Shl20 => *[]| _Align1Shl21 => *[]| _Align1Shl22 => *[]| _Align1Shl23 => *[]| _Align1Shl24 => *[]| _Align1Shl25 => *[]| _Align1Shl26 => *[]| _Align1Shl27 => *[]| _Align1Shl28 => *[]| _Align1Shl29 => *[]| _Align1Shl30 => *[]| _Align1Shl31 => *[]| _Align1Shl32 => *[]| _Align1Shl33 => *[]| _Align1Shl34 => *[]| _Align1Shl35 => *[]| _Align1Shl36 => *[]| _Align1Shl37 => *[]| _Align1Shl38 => *[]| _Align1Shl39 => *[]| _Align1Shl40 => *[]| _Align1Shl41 => *[]| _Align1Shl42 => *[]| _Align1Shl43 => *[]| _Align1Shl44 => *[]| _Align1Shl45 => *[]| _Align1Shl46 => *[]| _Align1Shl47 => *[]| _Align1Shl48 => *[]| _Align1Shl49 => *[]| _Align1Shl50 => *[]| _Align1Shl51 => *[]| _Align1Shl52 => *[]| _Align1Shl53 => *[]| _Align1Shl54 => *[]| _Align1Shl55 => *[]| _Align1Shl56 => *[]| _Align1Shl57 => *[]| _Align1Shl58 => *[]| _Align1Shl59 => *[]| _Align1Shl60 => *[]| _Align1Shl61 => *[]| _Align1Shl62 => *[]| _Align1Shl63 => *[] end)
        ([("_Align1Shl0", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl0_ty -[] -[]) (λ '( *[]), _Align1Shl0)); ("_Align1Shl1", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl1_ty -[] -[]) (λ '( *[]), _Align1Shl1)); ("_Align1Shl2", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl2_ty -[] -[]) (λ '( *[]), _Align1Shl2)); ("_Align1Shl3", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl3_ty -[] -[]) (λ '( *[]), _Align1Shl3)); ("_Align1Shl4", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl4_ty -[] -[]) (λ '( *[]), _Align1Shl4)); ("_Align1Shl5", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl5_ty -[] -[]) (λ '( *[]), _Align1Shl5)); ("_Align1Shl6", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl6_ty -[] -[]) (λ '( *[]), _Align1Shl6)); ("_Align1Shl7", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl7_ty -[] -[]) (λ '( *[]), _Align1Shl7)); ("_Align1Shl8", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl8_ty -[] -[]) (λ '( *[]), _Align1Shl8)); ("_Align1Shl9", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl9_ty -[] -[]) (λ '( *[]), _Align1Shl9)); ("_Align1Shl10", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl10_ty -[] -[]) (λ '( *[]), _Align1Shl10)); ("_Align1Shl11", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl11_ty -[] -[]) (λ '( *[]), _Align1Shl11)); ("_Align1Shl12", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl12_ty -[] -[]) (λ '( *[]), _Align1Shl12)); ("_Align1Shl13", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl13_ty -[] -[]) (λ '( *[]), _Align1Shl13)); ("_Align1Shl14", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl14_ty -[] -[]) (λ '( *[]), _Align1Shl14)); ("_Align1Shl15", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl15_ty -[] -[]) (λ '( *[]), _Align1Shl15)); ("_Align1Shl16", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl16_ty -[] -[]) (λ '( *[]), _Align1Shl16)); ("_Align1Shl17", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl17_ty -[] -[]) (λ '( *[]), _Align1Shl17)); ("_Align1Shl18", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl18_ty -[] -[]) (λ '( *[]), _Align1Shl18)); ("_Align1Shl19", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl19_ty -[] -[]) (λ '( *[]), _Align1Shl19)); ("_Align1Shl20", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl20_ty -[] -[]) (λ '( *[]), _Align1Shl20)); ("_Align1Shl21", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl21_ty -[] -[]) (λ '( *[]), _Align1Shl21)); ("_Align1Shl22", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl22_ty -[] -[]) (λ '( *[]), _Align1Shl22)); ("_Align1Shl23", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl23_ty -[] -[]) (λ '( *[]), _Align1Shl23)); ("_Align1Shl24", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl24_ty -[] -[]) (λ '( *[]), _Align1Shl24)); ("_Align1Shl25", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl25_ty -[] -[]) (λ '( *[]), _Align1Shl25)); ("_Align1Shl26", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl26_ty -[] -[]) (λ '( *[]), _Align1Shl26)); ("_Align1Shl27", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl27_ty -[] -[]) (λ '( *[]), _Align1Shl27)); ("_Align1Shl28", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl28_ty -[] -[]) (λ '( *[]), _Align1Shl28)); ("_Align1Shl29", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl29_ty -[] -[]) (λ '( *[]), _Align1Shl29)); ("_Align1Shl30", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl30_ty -[] -[]) (λ '( *[]), _Align1Shl30)); ("_Align1Shl31", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl31_ty -[] -[]) (λ '( *[]), _Align1Shl31)); ("_Align1Shl32", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl32_ty -[] -[]) (λ '( *[]), _Align1Shl32)); ("_Align1Shl33", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl33_ty -[] -[]) (λ '( *[]), _Align1Shl33)); ("_Align1Shl34", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl34_ty -[] -[]) (λ '( *[]), _Align1Shl34)); ("_Align1Shl35", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl35_ty -[] -[]) (λ '( *[]), _Align1Shl35)); ("_Align1Shl36", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl36_ty -[] -[]) (λ '( *[]), _Align1Shl36)); ("_Align1Shl37", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl37_ty -[] -[]) (λ '( *[]), _Align1Shl37)); ("_Align1Shl38", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl38_ty -[] -[]) (λ '( *[]), _Align1Shl38)); ("_Align1Shl39", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl39_ty -[] -[]) (λ '( *[]), _Align1Shl39)); ("_Align1Shl40", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl40_ty -[] -[]) (λ '( *[]), _Align1Shl40)); ("_Align1Shl41", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl41_ty -[] -[]) (λ '( *[]), _Align1Shl41)); ("_Align1Shl42", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl42_ty -[] -[]) (λ '( *[]), _Align1Shl42)); ("_Align1Shl43", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl43_ty -[] -[]) (λ '( *[]), _Align1Shl43)); ("_Align1Shl44", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl44_ty -[] -[]) (λ '( *[]), _Align1Shl44)); ("_Align1Shl45", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl45_ty -[] -[]) (λ '( *[]), _Align1Shl45)); ("_Align1Shl46", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl46_ty -[] -[]) (λ '( *[]), _Align1Shl46)); ("_Align1Shl47", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl47_ty -[] -[]) (λ '( *[]), _Align1Shl47)); ("_Align1Shl48", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl48_ty -[] -[]) (λ '( *[]), _Align1Shl48)); ("_Align1Shl49", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl49_ty -[] -[]) (λ '( *[]), _Align1Shl49)); ("_Align1Shl50", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl50_ty -[] -[]) (λ '( *[]), _Align1Shl50)); ("_Align1Shl51", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl51_ty -[] -[]) (λ '( *[]), _Align1Shl51)); ("_Align1Shl52", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl52_ty -[] -[]) (λ '( *[]), _Align1Shl52)); ("_Align1Shl53", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl53_ty -[] -[]) (λ '( *[]), _Align1Shl53)); ("_Align1Shl54", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl54_ty -[] -[]) (λ '( *[]), _Align1Shl54)); ("_Align1Shl55", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl55_ty -[] -[]) (λ '( *[]), _Align1Shl55)); ("_Align1Shl56", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl56_ty -[] -[]) (λ '( *[]), _Align1Shl56)); ("_Align1Shl57", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl57_ty -[] -[]) (λ '( *[]), _Align1Shl57)); ("_Align1Shl58", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl58_ty -[] -[]) (λ '( *[]), _Align1Shl58)); ("_Align1Shl59", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl59_ty -[] -[]) (λ '( *[]), _Align1Shl59)); ("_Align1Shl60", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl60_ty -[] -[]) (λ '( *[]), _Align1Shl60)); ("_Align1Shl61", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl61_ty -[] -[]) (λ '( *[]), _Align1Shl61)); ("_Align1Shl62", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl62_ty -[] -[]) (λ '( *[]), _Align1Shl62)); ("_Align1Shl63", mk_enum_tag_sem _ (alignment_AlignmentEnum__Align1Shl63_ty -[] -[]) (λ '( *[]), _Align1Shl63))])
        _
        _
        _.
    Next Obligation.
      solve_inhabited.
    Defined.

    Next Obligation.
      done.
    Qed.

    Next Obligation.
      solve_mk_enum_tag_consistent.
    Defined.

    Final Obligation.
      solve_mk_enum_tag_inj_roundtrip.
    Defined.

    #[global] Arguments alignment_AlignmentEnum_enum : simpl never.

    Definition alignment_AlignmentEnum_ty_pre  : (spec_with 0 [] ((type _))) :=
      spec! ( *[]) : 0 | ( *[]) : ([] : list RT), enum_t (alignment_AlignmentEnum_enum -[] -[]).
    Definition alignment_AlignmentEnum_rt_pre  : RT.
    Proof using  .
      let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum_ty_pre)) in exact __a.
    Defined.

    #[global] Typeclasses Transparent alignment_AlignmentEnum_rt_pre.
  End components.
  Arguments enum_ty : simpl never.

  Definition alignment_AlignmentEnum_ty  : (spec_with 0 [] ((type _))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), enum_t (alignment_AlignmentEnum_enum -[] -[]).
  Definition alignment_AlignmentEnum_rt  : RT.
  Proof using  .
    let __a := (normalized_rt_of_spec_ty (alignment_AlignmentEnum_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent alignment_AlignmentEnum_rt.
End alignment_AlignmentEnum_ty.
#[global] Typeclasses Transparent alignment_AlignmentEnum_ty.
#[global] Typeclasses Transparent alignment_AlignmentEnum_rt.
#[global] Arguments alignment_AlignmentEnum_enum : simpl never.

#[global] Arguments alignment_AlignmentEnum_rt : clear implicits.

#[global] Arguments alignment_AlignmentEnum_ty : clear implicits.

#[global] Arguments alignment_AlignmentEnum_ty {_ _}  .

Global Hint Unfold alignment_AlignmentEnum_ty : solve_protected_eq_db.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition alignment_AlignmentEnumasstd_clone_Clone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs ((alignment_AlignmentEnum_rt)))) :=
  mk_Clone_spec_attrs.


End attrs.

Section alignment_Alignment_ty.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition alignment_Alignment_ty  : (spec_with 0 [] ((type (plist place_rfnRT [(alignment_AlignmentEnum_rt) : RT])))).
  Proof.
    exact (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (struct_t alignment_Alignment_sls +[((alignment_AlignmentEnum_ty  -[] -[]))])).
  Defined.

  Definition alignment_Alignment_rt  : RT.
  Proof using  .
    let __a := (normalized_rt_of_spec_ty (alignment_Alignment_ty)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent alignment_Alignment_rt.
  #[global] Typeclasses Transparent alignment_Alignment_ty.
End alignment_Alignment_ty.
#[global] Arguments alignment_Alignment_rt : clear implicits.

#[global] Arguments alignment_Alignment_ty : clear implicits.

#[global] Arguments alignment_Alignment_ty {_ _}  .

Section alignment_Alignment_inv_t.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Program Definition alignment_Alignment_inv_t_inv_spec  : (spec_with 0 [] ((ex_inv_def (alignment_Alignment_rt)%type ((alignment_enum))%type))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), mk_auto_ex_inv_def
          (λ π (inner_rfn : alignment_Alignment_rt) (_ty_rfn : RT_rt ((alignment_enum)%type : RT)),
                  let 'x := _ty_rfn in ⌜inner_rfn = -[#(x)]⌝ ∗ True)%I
          (true)
          ([])
          ([])
          _ _ _ _
        .
  Next Obligation.
    ex_plain_t_solve_shr_auto.
  Defined.

  Next Obligation.
    ex_plain_t_solve_ghost_drop_auto.
  Defined.

  Next Obligation.
    ex_t_solve_persistent.
  Qed.

  Final Obligation.
    ex_plain_t_solve_shr_mono.
  Qed.

  Definition alignment_Alignment_inv_t  : (spec_with 0 [] ((type (((alignment_enum))%type)))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), ex_plain_t _ _ (alignment_Alignment_inv_t_inv_spec  -[] -[]) (alignment_Alignment_ty -[] -[]).
  #[global] Arguments alignment_Alignment_inv_t_inv_spec : simpl never.

  #[global] Arguments alignment_Alignment_inv_t : simpl never.

  #[global] Typeclasses Transparent alignment_Alignment_inv_t.
  Definition alignment_Alignment_inv_t_rt  : RT.
  Proof using  .
    let __a := (normalized_rt_of_spec_ty (alignment_Alignment_inv_t)) in exact __a.
  Defined.

  #[global] Typeclasses Transparent alignment_Alignment_inv_t_rt.
End alignment_Alignment_inv_t.
#[global] Arguments alignment_Alignment_inv_t_rt : clear implicits.

#[global] Arguments alignment_Alignment_inv_t : clear implicits.

#[global] Arguments alignment_Alignment_inv_t {_ _}  .

#[global] Arguments alignment_Alignment_inv_t_inv_spec : clear implicits.

#[global] Arguments alignment_Alignment_inv_t_inv_spec {_ _}  .


Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition alignment_Alignmentasstd_clone_Clone_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Clone_spec_attrs ((alignment_Alignment_inv_t_rt)))) :=
  mk_Clone_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition alignment_AlignmentEnumasstd_marker_Copy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs ((alignment_AlignmentEnum_rt)) (alignment_AlignmentEnumasstd_clone_Clone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section attrs.
Context `{RRGS : !refinedrustGS Σ}.
Program Definition alignment_Alignmentasstd_marker_Copy_spec_attrs `{RRGS : !(refinedrustGS Σ)} : ((Copy_spec_attrs ((alignment_Alignment_inv_t_rt)) (alignment_Alignmentasstd_clone_Clone_spec_attrs))) :=
  mk_Copy_spec_attrs.


End attrs.

Section drop_glue_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End drop_glue_attrs.

Section closure_attrs.
Context `{RRGS : !refinedrustGS Σ}.
End closure_attrs.

(* Included specifications from configured file extra_specs.v *)
From Ltac2 Require Import Notations.
Ltac2 Set start_function_hook as old_start_function_hook :=
  fun () =>
    Control.plus (fun () =>
    match! goal with
    | [ _ : CACHED
          (use_enum_layout_alg alignment_AlignmentEnum_els = Some _)
        |- _ ] =>
        let h := Fresh.in_goal @_Hop in
        assert
          (ty_has_op_type
             (alignment_AlignmentEnum_ty -[] -[])
             (use_op_alg' alignment_AlignmentEnum_els))
          as $h
        > [ ltac1:(solve_ty_has_op_type)
          | let hop := Control.hyp h in
            ltac1:(hop |- enter_cache hop) (Ltac1.of_constr hop)
          ]
    end) (fun _ => ());
    old_start_function_hook ()
  .
Section specs.
Context `{RRGS : !refinedrustGS Σ}.

Definition trait_incl_of_alignment_Alignmentasstd_clone_Clone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_alignment_Alignmentasstd_clone_Clone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec ((alignment_Alignment_inv_t_rt)) (alignment_Alignment_st) ((drop_glue_trivial_spec_attrs ((alignment_Alignment_inv_t_rt)))) (alignment_Alignmentasstd_clone_Clone_spec_attrs))
    -[] -[(alignment_Alignment_inv_t   -[] -[])]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_alignment_AlignmentEnumasstd_clone_Clone_clone  : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[]) : ([] : list RT), (True).

Definition type_of_alignment_AlignmentEnumasstd_clone_Clone_clone  :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT),(λ a b, scope_add_typarams _ -[] (scope_add_elctx (λ ϝ, []) (((Clone_base_spec ((alignment_AlignmentEnum_rt)) (alignment_AlignmentEnum_st) ((drop_glue_trivial_spec_attrs ((alignment_AlignmentEnum_rt)))) (alignment_AlignmentEnumasstd_clone_Clone_spec_attrs))
    -[] -[(alignment_AlignmentEnum_ty  -[] -[])]).(Clone_clone_spec)   a b))) <MERGE!>.

Definition trait_incl_of_alignment_Alignment_as_usize  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_alignment_Alignment_as_usize  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (self) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) self :@: (alignment_Alignment_inv_t   -[] -[]);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, alignment_to_align self @ (int USize);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_alignment_Alignment_new  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_alignment_Alignment_new  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (align) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) align :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ (Option_ty ((alignment_Alignment_inv_t_rt)) -[] -[(alignment_Alignment_inv_t   -[] -[])]);
      (* postcondition *) (λ π : thread_id, (⌜((if_Some ret (λ (ret: _), (is_power_of_two (Z.to_nat align)) ∧ ((ret = alignment_of_align align)))))%Z⌝)
      ∗ (⌜((if_None ret (¬ ((is_power_of_two (Z.to_nat align))))))%Z⌝)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_alignment_Alignment_of (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_alignment_Alignment_of (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, alignment_of_align (ly_align (use_layout_alg' (ty_syn_type T_ty MetaNone))) @ (alignment_Alignment_inv_t   -[] -[]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_add (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_add (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(l `has_layout_loc` (use_layout_alg' (ty_syn_type T_ty MetaNone)))%Z⌝)
        ∗ (⌜((count * size_of_st (ty_syn_type T_ty MetaNone))%Z ∈ ISize)%Z⌝)
        ∗ (loc_in_bounds l 0 ((Z.to_nat count) * size_of_st (ty_syn_type T_ty MetaNone)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l offsetst{ (ty_syn_type T_ty MetaNone) }ₗ count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_addr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_addr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, x.(loc_a) @ (int USize);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_cast (T_rt: RT) (U_rt: RT) (T_st: syn_type) (U_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (DropGlue_U_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (U_rt) )) (DropGlue_U_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (U_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_U_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (U_rt) U_st DropGlue_U_spec_attrs-[] -[U_ty])))).

Definition type_of_const_ptr_cast (T_rt: RT) (U_rt: RT) (T_st: syn_type) (U_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_U_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (U_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; U_ty]) : ([(T_rt, T_st); (U_rt, U_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, x @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_cast_mut (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_cast_mut (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, x @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_is_null (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_is_null (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x.(loc_a) = 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_offset (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_offset (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int ISize);
      (* precondition. *) (λ π : thread_id, (⌜(l `has_layout_loc` (use_layout_alg' (ty_syn_type T_ty MetaNone)))%Z⌝)
        ∗ (⌜((count * size_of_st (ty_syn_type T_ty MetaNone))%Z ∈ ISize)%Z⌝)
        ∗ (
            case_destruct (bool_decide (count < 0))%Z
              (λ b _, if b then loc_in_bounds l (Z.to_nat (-count) * size_of_st (ty_syn_type T_ty MetaNone)) 0 else loc_in_bounds l 0 (Z.to_nat count * size_of_st (ty_syn_type T_ty MetaNone))))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, (l offsetst{ (ty_syn_type T_ty MetaNone) }ₗ count) @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_read (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_read (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (k, ty, src) : ((_ * (xtype) * _)),
      (* elctx........ *) (λ ϝ, [] ++ bor_kind_outlives_elctx k ϝ);
      (* args......... *) src :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (src ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))
        ∗ (⌜(ty_allows_reads ty.(xtype_ty))%Z⌝)
        ∗ (⌜(ty_allows_writes ty.(xtype_ty))%Z⌝)
        ∗ (⌜(st_of ty.(xtype_ty) MetaNone = (ty_syn_type T_ty MetaNone))%Z⌝)
        ∗ (⌜(Copyable ty.(xtype_ty))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ty.(xtype_rfn) @ ty.(xtype_ty);
      (* postcondition *) (λ π : thread_id, (src ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_read_volatile (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_read_volatile (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (k, ty, src) : ((_ * (xtype) * _)),
      (* elctx........ *) (λ ϝ, [] ++ bor_kind_outlives_elctx k ϝ);
      (* args......... *) src :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (src ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))
        ∗ (⌜(ty_allows_reads ty.(xtype_ty))%Z⌝)
        ∗ (⌜(ty_allows_writes ty.(xtype_ty))%Z⌝)
        ∗ (⌜(st_of ty.(xtype_ty) MetaNone = (ty_syn_type T_ty MetaNone))%Z⌝)
        ∗ (⌜(Copyable ty.(xtype_ty))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ty.(xtype_rfn) @ ty.(xtype_ty);
      (* postcondition *) (λ π : thread_id, (src ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_sub (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_sub (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(l `has_layout_loc` (use_layout_alg' (ty_syn_type T_ty MetaNone)))%Z⌝)
        ∗ (⌜((count * size_of_st (ty_syn_type T_ty MetaNone))%Z ∈ ISize)%Z⌝)
        ∗ (loc_in_bounds l (Z.to_nat count * size_of_st (ty_syn_type T_ty MetaNone)) 0)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l offsetst{ (ty_syn_type T_ty MetaNone) }ₗ (-count) @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_with_addr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_with_addr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x, addr) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: alias_ptr_t, addr :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, with_addr x addr @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_wrapping_add (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_wrapping_add (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l wrapping_offsetst{ (ty_syn_type T_ty MetaNone) }ₗ count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_wrapping_byte_add (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_wrapping_byte_add (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l +wₗ count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_wrapping_byte_offset (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_wrapping_byte_offset (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int ISize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l +wₗ count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_wrapping_byte_sub (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_wrapping_byte_sub (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l +wₗ -count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_wrapping_offset (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_wrapping_offset (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int ISize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l wrapping_offsetst{ (ty_syn_type T_ty MetaNone) }ₗ count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_wrapping_sub (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_wrapping_sub (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l wrapping_offsetst{ (ty_syn_type T_ty MetaNone) }ₗ -count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_copy_nonoverlapping (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_copy_nonoverlapping (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (vs, src, dst, size) : ((_ * _ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) src :@: alias_ptr_t, dst :@: alias_ptr_t, size :@: (int USize);
      (* precondition. *) (λ π : thread_id, (src ◁ₗ[π, Owned] #(vs) @ (◁ value_t false (ArraySynType (ty_syn_type T_ty MetaNone) (Z.to_nat size))))
        ∗ (dst ◁ₗ[π, Owned] #(()) @ (◁ uninit (ArraySynType (ty_syn_type T_ty MetaNone) (Z.to_nat size))))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (src ◁ₗ[π, Owned] #(vs) @ (◁ value_t false (ArraySynType (ty_syn_type T_ty MetaNone) (Z.to_nat size))))
      ∗ (dst ◁ₗ[π, Owned] #(vs) @ (◁ value_t false (ArraySynType (ty_syn_type T_ty MetaNone) (Z.to_nat size))))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_dangling (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_dangling (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : ((_)), l @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (⌜(l.(loc_a) ≠ 0)%Z⌝)
      ∗ (⌜(l `has_layout_loc` (use_layout_alg' (ty_syn_type T_ty MetaNone)))%Z⌝)
      ∗ (l ◁ₗ[π, Owned] #(()) @ (◁ uninit UnitSynType))
      ∗ (freeable_nz l 0 1 HeapAlloc)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_dangling_mut (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_dangling_mut (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : ((_)), l @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (⌜(l.(loc_a) ≠ 0)%Z⌝)
      ∗ (⌜(l `has_layout_loc` (use_layout_alg' (ty_syn_type T_ty MetaNone)))%Z⌝)
      ∗ (l ◁ₗ[π, Owned] #(()) @ (◁ uninit UnitSynType))
      ∗ (freeable_nz l 0 1 HeapAlloc)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_add (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_add (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(l `has_layout_loc` (use_layout_alg' (ty_syn_type T_ty MetaNone)))%Z⌝)
        ∗ (⌜((count * size_of_st (ty_syn_type T_ty MetaNone))%Z ∈ ISize)%Z⌝)
        ∗ (loc_in_bounds l 0 ((Z.to_nat count) * size_of_st (ty_syn_type T_ty MetaNone)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l offsetst{ (ty_syn_type T_ty MetaNone) }ₗ count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_addr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_addr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, x.(loc_a) @ (int USize);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_cast (T_rt: RT) (U_rt: RT) (T_st: syn_type) (U_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) (DropGlue_U_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (U_rt) )) (DropGlue_U_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (U_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty; U_ty]) : ([T_rt; U_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty]))) ∧ (trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_U_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (U_rt) U_st DropGlue_U_spec_attrs-[] -[U_ty])))).

Definition type_of_mut_ptr_cast (T_rt: RT) (U_rt: RT) (T_st: syn_type) (U_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_U_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (U_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty; U_ty]) : ([(T_rt, T_st); (U_rt, U_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, x @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_cast_const (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_cast_const (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, x @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_is_null (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_is_null (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (x.(loc_a) = 0) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_offset (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_offset (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int ISize);
      (* precondition. *) (λ π : thread_id, (⌜(l `has_layout_loc` (use_layout_alg' (ty_syn_type T_ty MetaNone)))%Z⌝)
        ∗ (⌜((count * size_of_st (ty_syn_type T_ty MetaNone))%Z ∈ ISize)%Z⌝)
        ∗ (
            case_destruct (bool_decide (count < 0))%Z
              (λ b _, if b then loc_in_bounds l (Z.to_nat (-count) * size_of_st (ty_syn_type T_ty MetaNone)) 0 else loc_in_bounds l 0 (Z.to_nat count * size_of_st (ty_syn_type T_ty MetaNone))))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l offsetst{ (ty_syn_type T_ty MetaNone) }ₗ count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_read (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_read (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (k, ty, src) : ((_ * (xtype) * _)),
      (* elctx........ *) (λ ϝ, [] ++ bor_kind_outlives_elctx k ϝ);
      (* args......... *) src :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (src ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))
        ∗ (⌜(ty_allows_reads ty.(xtype_ty))%Z⌝)
        ∗ (⌜(ty_allows_writes ty.(xtype_ty))%Z⌝)
        ∗ (⌜(st_of ty.(xtype_ty) MetaNone = (ty_syn_type T_ty MetaNone))%Z⌝)
        ∗ (⌜(Copyable ty.(xtype_ty))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ty.(xtype_rfn) @ ty.(xtype_ty);
      (* postcondition *) (λ π : thread_id, (src ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_read_volatile (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_read_volatile (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (k, ty, src) : ((_ * (xtype) * _)),
      (* elctx........ *) (λ ϝ, [] ++ bor_kind_outlives_elctx k ϝ);
      (* args......... *) src :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (src ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))
        ∗ (⌜(ty_allows_reads ty.(xtype_ty))%Z⌝)
        ∗ (⌜(ty_allows_writes ty.(xtype_ty))%Z⌝)
        ∗ (⌜(st_of ty.(xtype_ty) MetaNone = (ty_syn_type T_ty MetaNone))%Z⌝)
        ∗ (⌜(Copyable ty.(xtype_ty))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ty.(xtype_rfn) @ ty.(xtype_ty);
      (* postcondition *) (λ π : thread_id, (src ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_sub (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_sub (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(l `has_layout_loc` (use_layout_alg' (ty_syn_type T_ty MetaNone)))%Z⌝)
        ∗ (⌜((count * size_of_st (ty_syn_type T_ty MetaNone))%Z ∈ ISize)%Z⌝)
        ∗ (loc_in_bounds l ((Z.to_nat count) * size_of_st (ty_syn_type T_ty MetaNone)) 0)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l offsetst{ (ty_syn_type T_ty MetaNone) }ₗ (-count) @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_with_addr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_with_addr (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x, addr) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) x :@: alias_ptr_t, addr :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, with_addr x addr @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_wrapping_add (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_wrapping_add (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l wrapping_offsetst{ (ty_syn_type T_ty MetaNone) }ₗ count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_wrapping_byte_add (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_wrapping_byte_add (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l +wₗ count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_wrapping_byte_offset (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_wrapping_byte_offset (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int ISize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l +wₗ count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_wrapping_byte_sub (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_wrapping_byte_sub (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l +wₗ -count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_wrapping_offset (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_wrapping_offset (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int ISize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l wrapping_offsetst{ (ty_syn_type T_ty MetaNone) }ₗ count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_wrapping_sub (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_wrapping_sub (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, count) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l :@: alias_ptr_t, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, l wrapping_offsetst{ (ty_syn_type T_ty MetaNone) }ₗ -count @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (£ (S (num_laters_per_step 1)) ∗ tr 1)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_write (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_write (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (dst, src) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) dst :@: alias_ptr_t, src :@: T_ty;
      (* precondition. *) (λ π : thread_id, (dst ◁ₗ[π, Owned] #(()) @ (◁ uninit (ty_syn_type T_ty MetaNone)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (dst ◁ₗ[π, Owned] #($# src) @ (◁ T_ty))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_write_volatile (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_write_volatile (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (dst, src) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) dst :@: alias_ptr_t, src :@: T_ty;
      (* precondition. *) (λ π : thread_id, (dst ◁ₗ[π, Owned] #(()) @ (◁ uninit (ty_syn_type T_ty MetaNone)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (dst ◁ₗ[π, Owned] #($# src) @ (◁ T_ty))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_read (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_read (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (k, ty, src) : ((_ * (xtype) * _)),
      (* elctx........ *) (λ ϝ, [] ++ bor_kind_outlives_elctx k ϝ);
      (* args......... *) src :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (src ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))
        ∗ (⌜(ty_allows_reads ty.(xtype_ty))%Z⌝)
        ∗ (⌜(ty_allows_writes ty.(xtype_ty))%Z⌝)
        ∗ (⌜(st_of ty.(xtype_ty) MetaNone = (ty_syn_type T_ty MetaNone))%Z⌝)
        ∗ (⌜(Copyable ty.(xtype_ty))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ty.(xtype_rfn) @ ty.(xtype_ty);
      (* postcondition *) (λ π : thread_id, (src ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_read_volatile (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_read_volatile (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (k, ty, src) : ((_ * (xtype) * _)),
      (* elctx........ *) (λ ϝ, [] ++ bor_kind_outlives_elctx k ϝ);
      (* args......... *) src :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, (src ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))
        ∗ (⌜(ty_allows_reads ty.(xtype_ty))%Z⌝)
        ∗ (⌜(ty_allows_writes ty.(xtype_ty))%Z⌝)
        ∗ (⌜(st_of ty.(xtype_ty) MetaNone = (ty_syn_type T_ty MetaNone))%Z⌝)
        ∗ (⌜(Copyable ty.(xtype_ty))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, ty.(xtype_rfn) @ ty.(xtype_ty);
      (* postcondition *) (λ π : thread_id, (src ◁ₗ[π, k] # ($# ty.(xtype_rfn)) @ ◁ ty.(xtype_ty))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_without_provenance (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_without_provenance (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (addr) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) addr :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : ((_)), l @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (⌜(l `aligned_to` (Z.to_nat addr))%Z⌝)
      ∗ (⌜(l.(loc_a) = addr)%Z⌝)
      ∗ (if decide (addr ≠ 0) then (l ◁ₗ[π, Owned] .@ ◁ unit_t) else True)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_without_provenance_mut (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_without_provenance_mut (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (addr) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) addr :@: (int USize);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (l) : ((_)), l @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, (⌜(l `aligned_to` (Z.to_nat addr))%Z⌝)
      ∗ (⌜(l.(loc_a) = addr)%Z⌝)
      ∗ (if decide (addr ≠ 0) then (l ◁ₗ[π, Owned] .@ ◁ unit_t) else True)) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_write (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_write (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (dst, src) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) dst :@: alias_ptr_t, src :@: T_ty;
      (* precondition. *) (λ π : thread_id, (dst ◁ₗ[π, Owned] #(()) @ (◁ uninit (ty_syn_type T_ty MetaNone)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (dst ◁ₗ[π, Owned] #($# src) @ (◁ T_ty))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_write_volatile (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_write_volatile (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (dst, src) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) dst :@: alias_ptr_t, src :@: T_ty;
      (* precondition. *) (λ π : thread_id, (dst ◁ₗ[π, Owned] #(()) @ (◁ uninit (ty_syn_type T_ty MetaNone)))) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (dst ◁ₗ[π, Owned] #($# src) @ (◁ T_ty))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).


Definition trait_incl_of_alignment_Alignment_new_unchecked  : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (True).

Definition type_of_alignment_Alignment_new_unchecked  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (align) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) align :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(is_power_of_two (Z.to_nat align))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, alignment_of_align align @ (alignment_Alignment_inv_t   -[] -[]);
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mem_replace (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1]) : 1 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mem_replace (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[ulft_1]) : 1 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (dest, src) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1)]);
      (* args......... *) dest :@: (mut_ref ulft_1 T_ty), src :@: T_ty;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, dest.cur @ T_ty;
      (* postcondition *) (λ π : thread_id, (gvar_pobs dest.ghost ($# src))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mem_swap (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[ulft_1; ulft_2]) : 2 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mem_swap (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[ulft_1; ulft_2]) : 2 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (x, y) : ((_ * _)),
      (* elctx........ *) (λ ϝ, [(ϝ, ulft_1); (ϝ, ulft_2)]);
      (* args......... *) x :@: (mut_ref ulft_1 T_ty), y :@: (mut_ref ulft_2 T_ty);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (gvar_pobs x.ghost (y.cur))
      ∗ (gvar_pobs y.ghost (x.cur))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_is_aligned (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_is_aligned (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (a) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) a :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (a `aligned_to` (ly_align (use_layout_alg' (ty_syn_type T_ty MetaNone)))) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_const_ptr_is_aligned_to (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_const_ptr_is_aligned_to (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (a, align) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) a :@: alias_ptr_t, align :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(is_power_of_two (Z.to_nat align))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (a `aligned_to` Z.to_nat align) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_copy (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_copy (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (l, off_src, off_dst, count, len, vs) : ((_ * _ * _ * _ * _ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) l offsetst{ (ty_syn_type T_ty MetaNone) }ₗ off_src :@: alias_ptr_t, l offsetst{ (ty_syn_type T_ty MetaNone) }ₗ off_dst :@: alias_ptr_t, count :@: (int USize);
      (* precondition. *) (λ π : thread_id, (l ◁ₗ[π, Owned] #(vs) @ (◁ value_t false (ArraySynType (ty_syn_type T_ty MetaNone) (Z.to_nat len))))
        ∗ (⌜((0 ≤ count)%Z)%Z⌝)
        ∗ (⌜(0 ≤ off_src)%Z⌝)
        ∗ (⌜(0 ≤ off_dst)%Z⌝)
        ∗ (⌜((off_src + count < len)%Z)%Z⌝)
        ∗ (⌜((off_dst + count < len)%Z)%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ (ret) : ((_)), ret @ unit_t;
      (* postcondition *) (λ π : thread_id, (l ◁ₗ[π, Owned] #(ptr_copy_result off_src off_dst (Z.to_nat count) vs : val) @ (◁ value_t false (ArraySynType (ty_syn_type T_ty MetaNone) (Z.to_nat len))))) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_is_aligned (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_is_aligned (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (a) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) a :@: alias_ptr_t;
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (a `aligned_to` (ly_align (use_layout_alg' (ty_syn_type T_ty MetaNone)))) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_mut_ptr_is_aligned_to (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_mut_ptr_is_aligned_to (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) (a, align) : ((_ * _)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) a :@: alias_ptr_t, align :@: (int USize);
      (* precondition. *) (λ π : thread_id, (⌜(is_power_of_two (Z.to_nat align))%Z⌝)) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, bool_decide (a `aligned_to` Z.to_nat align) @ bool_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_ptr_null (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_ptr_null (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, NULL_loc @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).

Definition trait_incl_of_ptr_null_mut (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) (DropGlue_T_spec: (spec_with 0 [] (DropGlue_spec (RRGS:=RRGS) (T_rt)))) : (spec_with _ _ Prop) :=
  spec! ( *[]) : 0 | ( *[T_ty]) : ([T_rt] : list RT), ((trait_incl_marker (lift_trait_incl DropGlue_spec_incl DropGlue_T_spec (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), DropGlue_base_spec (T_rt) T_st DropGlue_T_spec_attrs-[] -[T_ty])))).

Definition type_of_ptr_null_mut (T_rt: RT) (T_st: syn_type) (DropGlue_T_spec_attrs: (DropGlue_spec_attrs (RRGS:=RRGS) (T_rt) )) :=
  fn(∀ ( *[]) : 0 | ( *[T_ty]) : ([(T_rt, T_st)] : list (RT * syn_type)%type) | 
      (* params....... *) _ : unit,
      (* elctx........ *) (λ ϝ, []);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : unit, NULL_loc @ alias_ptr_t;
      (* postcondition *) (λ π : thread_id, True) |
      (* unwind cond... *) False |
      (* unwind post... *) (λ π : thread_id, True).



End specs.
Section alignment_Alignmentasstd_clone_Clone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition alignment_Alignmentasstd_clone_Clone_spec  : (spec_with _ _ (Clone_spec ((alignment_Alignment_inv_t_rt)))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_alignment_Alignmentasstd_clone_Clone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec ((alignment_Alignment_inv_t_rt)) (alignment_Alignment_st)) (drop_glue_trivial_spec_attrs ((alignment_Alignment_inv_t_rt))) alignment_Alignmentasstd_clone_Clone_spec_attrs 
             <TY> (alignment_Alignment_inv_t   -[] -[]) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition alignment_Alignmentasstd_clone_Clone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), alignment_Alignmentasstd_clone_Clone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec (alignment_Alignment_inv_t_rt) alignment_Alignment_st (drop_glue_trivial_spec_attrs ((alignment_Alignment_inv_t_rt))) alignment_Alignmentasstd_clone_Clone_spec_attrs-[] -[(alignment_Alignment_inv_t   -[] -[])])))).
End alignment_Alignmentasstd_clone_Clone_spec.

Section alignment_Alignmentasstd_marker_Copy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition alignment_Alignmentasstd_marker_Copy_spec  : (spec_with _ _ (Copy_spec ((alignment_Alignment_inv_t_rt)))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ ((alignment_Alignment_inv_t_rt))).
  Definition alignment_Alignmentasstd_marker_Copy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), alignment_Alignmentasstd_marker_Copy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec (alignment_Alignment_inv_t_rt) alignment_Alignment_st alignment_Alignmentasstd_clone_Clone_spec_attrs (drop_glue_trivial_spec_attrs ((alignment_Alignment_inv_t_rt))) alignment_Alignmentasstd_marker_Copy_spec_attrs-[] -[(alignment_Alignment_inv_t   -[] -[])])))).
  Lemma alignment_Alignmentasstd_marker_Copy_semantic_interp  : (Copy_semantic_interp (alignment_Alignment_inv_t_rt) (alignment_Alignment_inv_t   -[] -[])).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End alignment_Alignmentasstd_marker_Copy_spec.

Section alignment_AlignmentEnumasstd_clone_Clone_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition alignment_AlignmentEnumasstd_clone_Clone_spec  : (spec_with _ _ (Clone_spec ((alignment_AlignmentEnum_rt)))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), {|
        Clone_clone_spec  :=
          type_of_alignment_AlignmentEnumasstd_clone_Clone_clone 
             : (spec_with 1 [] fn_spec);
        Clone_clone_from_spec  :=
          (Clone_clone_from_base_spec ((alignment_AlignmentEnum_rt)) (alignment_AlignmentEnum_st)) (drop_glue_trivial_spec_attrs ((alignment_AlignmentEnum_rt))) alignment_AlignmentEnumasstd_clone_Clone_spec_attrs 
             <TY> (alignment_AlignmentEnum_ty  -[] -[]) : (spec_with 2 [] fn_spec);
      |}
  .
  Definition alignment_AlignmentEnumasstd_clone_Clone_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Clone_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), alignment_AlignmentEnumasstd_clone_Clone_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Clone_base_spec (alignment_AlignmentEnum_rt) alignment_AlignmentEnum_st (drop_glue_trivial_spec_attrs ((alignment_AlignmentEnum_rt))) alignment_AlignmentEnumasstd_clone_Clone_spec_attrs-[] -[(alignment_AlignmentEnum_ty  -[] -[])])))).
End alignment_AlignmentEnumasstd_clone_Clone_spec.

Section alignment_AlignmentEnumasstd_marker_Copy_spec.
  Context `{RRGS : !(refinedrustGS Σ)}.
  Definition alignment_AlignmentEnumasstd_marker_Copy_spec  : (spec_with _ _ (Copy_spec ((alignment_AlignmentEnum_rt)))) :=
    spec! ( *[]) : 0 | ( *[]) : ([] : list RT), (@mk_Copy_spec _ _ ((alignment_AlignmentEnum_rt))).
  Definition alignment_AlignmentEnumasstd_marker_Copy_spec_subsumption  :=
    trait_incl_marker (lift_trait_incl Copy_spec_incl (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), alignment_AlignmentEnumasstd_marker_Copy_spec-[] -[]) (spec! ( *[]) : 0 | ( *[]) : ([] : list RT), scope_add_typarams _ -[] ((Copy_base_spec (alignment_AlignmentEnum_rt) alignment_AlignmentEnum_st alignment_AlignmentEnumasstd_clone_Clone_spec_attrs (drop_glue_trivial_spec_attrs ((alignment_AlignmentEnum_rt))) alignment_AlignmentEnumasstd_marker_Copy_spec_attrs-[] -[(alignment_AlignmentEnum_ty  -[] -[])])))).
  Lemma alignment_AlignmentEnumasstd_marker_Copy_semantic_interp  : (Copy_semantic_interp (alignment_AlignmentEnum_rt) (alignment_AlignmentEnum_ty  -[] -[])).
  Proof.
    unfold Copy_semantic_interp in *; apply _.
  Qed.

End alignment_AlignmentEnumasstd_marker_Copy_spec.

