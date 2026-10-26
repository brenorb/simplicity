(** Actual mixed-addition call after the two generator hash/SWU passes.
    Accept their loose coordinate bounds, and preserve caller startup state.
    This is an execution span; the canonical mixed-addition bridge follows. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge C.jet_secp_statement_prefix
  C.jet_secp_curve_statements C.jet_secp_mixed_body_loose C.jet_secp_mixed_function_loose
  C.jet_clight_internal_preserve C.jet_secp_sha_startup C.jet_secp_swu_startup
  C.jet_secp_generator_sha_absorb.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generator_add_stmt := nth 14
  (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))) Sskip.
Lemma generator_add_source : generator_add_stmt=Scall None
  (Evar _secp256k1_gej_add_ge_var (type_of_function f_secp256k1_gej_add_ge_var))
  [Eaddrof (Evar _accum (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
   Eaddrof (Evar _accum (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
   Eaddrof (Evar _add curve_ge_type) (tptr curve_ge_type);
   Ecast (Econst_int Int.zero tint) (tptr tvoid)].
Proof. reflexivity. Qed.
Lemma generator_add_symbol : Genv.find_symbol secp_ge _secp256k1_gej_add_ge_var=
  Some (secp_symbol_block _secp256k1_gej_add_ge_var).
Proof. vm_compute;reflexivity. Qed.
Lemma generator_add_funct : Genv.find_funct secp_ge
  (Vptr (secp_symbol_block _secp256k1_gej_add_ge_var) Ptrofs.zero)=Some (Internal f_secp256k1_gej_add_ge_var).
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge.

Theorem exec_generator_add e le m bx bp x y z u v :
  e!_accum=Some (bx,Tstruct __6123 noattr) ->e!_add=Some (bp,curve_ge_type) ->
  e!_secp256k1_gej_add_ge_var=None ->bx<>bp ->
  square_input_bounds x ->square_input_bounds y ->square_input_bounds z ->
  square_input_bounds u ->square_input_bounds v ->
  fe_at m bx 0 (words5 x) ->fe_at m bx 40 (words5 y) ->fe_at m bx 80 (words5 z) ->
  Mem.load Mint32 m bx 120=Some (Vint Int.zero) ->
  fe_at m bp 0 (words5 u) ->fe_at m bp 40 (words5 v) ->Mem.load Mint32 m bp 80=Some (Vint Int.zero) ->
  Mem.range_perm m bx 0 128 Cur Freeable ->Mem.range_perm m bp 0 88 Cur Freeable ->
  secp_sha_startup m ->swu_startup m ->(forall prefix,generator_sha_prefix_state prefix m) ->exists mf,
  Clight2.exec_stmt secp_ge e le m generator_add_stmt E0 le mf Out_normal /\
  fe_at mf bx 0 (words5 (mixed_mode_body_x_words true Int.zero x y z u v)) /\
  fe_at mf bx 40 (words5 (mixed_mode_body_y_words true Int.zero x y z u v)) /\
  fe_at mf bx 80 (words5 (mixed_mode_body_z_words true Int.zero x y z u v)) /\
  Mem.load Mint32 mf bx 120=Some (Vint (mixed_mode_body_flag true Int.zero x y z u v)) /\
  square_input_bounds (mixed_mode_body_x_words true Int.zero x y z u v) /\
  square_input_bounds (mixed_mode_body_y_words true Int.zero x y z u v) /\
  square_input_bounds (mixed_mode_body_z_words true Int.zero x y z u v) /\
  Mem.range_perm mf bx 0 128 Cur Freeable /\Mem.range_perm mf bp 0 88 Cur Freeable /\
  lframe (fun b _=>b<>bx /\b<>bp) m mf /\readonly_preserved m mf /\
  secp_sha_startup mf /\swu_startup mf /\(forall prefix,generator_sha_prefix_state prefix mf).
Proof.
  intros Acc Add Fun Apart BX BY BZ BU BV X Y Z Flag U V FlagB FX FP SHA SWU Prefixes.
  destruct (eval_mixed_function_xy x y z u v Int.zero m bx bp Apart BX BY BZ BU BV Flag FlagB X Y Z U V FX FP)
    as (mf & Call & XO & YO & ZO & FlagO & FXF & FPF & BXO & BYO & BZO & Frame).
  pose proof (mixed_function_readonly _ _ _ _ _ Call) as Read.
  exists mf;split.
  - rewrite generator_add_source;change le with (set_opttemp None Vundef le) at 2.
    eapply exec_Scall with (vf:=Vptr (secp_symbol_block _secp256k1_gej_add_ge_var) Ptrofs.zero)
      (vargs:=[Vptr bx Ptrofs.zero;Vptr bx Ptrofs.zero;Vptr bp Ptrofs.zero;Vlong Int64.zero])
      (f:=Internal f_secp256k1_gej_add_ge_var) (vres:=Vundef).
    + reflexivity.
    + eapply eval_Elvalue;[apply eval_Evar_global;[exact Fun|exact generator_add_symbol]|apply deref_loc_reference;reflexivity].
    + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Acc|reflexivity|].
      eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Acc|reflexivity|].
      eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Add|reflexivity|].
      eapply eval_Econs;[eapply eval_Ecast;[constructor|reflexivity]|reflexivity|constructor].
    + exact generator_add_funct.
    + reflexivity.
    + exact Call.
  - split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];
      split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];split;[exact FXF|];split;[exact FPF|];
      split;[exact Frame|];split;[exact Read|];split.
    + eapply secp_sha_startup_preserved;[exact SHA|exact Read|exact Frame|].
      pose proof (proj1 (secp_sha_startup_separate m bx 128 SHA ltac:(lia) FX)) as DX.
      pose proof (proj1 (secp_sha_startup_separate m bp 88 SHA ltac:(lia) FP)) as DP.
      intro pos;split;congruence.
    + split;[eapply swu_startup_preserved;[exact SWU|exact Read]|].
      intro prefix;eapply generator_sha_prefix_preserved;[apply Prefixes|exact Read].
Qed.
