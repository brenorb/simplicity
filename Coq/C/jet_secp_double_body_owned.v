(** Execution of the exact original arithmetic statement suffix from owned
    initial storage, discharging every helper-call premise internally. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp
  C.jet_secp_double_statements C.jet_secp_double_all_calls C.jet_secp_double_prefix
  C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem exec_double_arithmetic_owned le x y z m ba bs bl bt :
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  ba<>bs -> ba<>bl -> ba<>bt -> bs<>bl -> bs<>bt -> bl<>bt ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
  Mem.range_perm m bl 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge (double_helper_env bl bs bt) le m double_arithmetic_body E0 le mf Out_normal /\
  fe_at mf ba 0 (words5 (double_output_x_words x y)) /\
  fe_at mf ba 40 (words5 (double_output_y_words x y)) /\
  fe_at mf ba 80 (words5 (double_output_z_words y z)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  Mem.range_perm mf bl 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
  square_input_bounds (double_output_x_words x y) /\
  square_input_bounds (double_output_y_words x y) /\
  square_input_bounds (double_output_z_words y z) /\
  lframe (fun b pos => double_work_frame ba bs bl b pos /\ b<>bt) m mf.
Proof.
  intros HA HR BX BY BZ HAS HAL HAT HSL HST HLT HX HY HZ HFA HFS HFL HFT.
  destruct (double_all_arithmetic_calls x y z m ba bs bl bt BX BY BZ HAS HAL HAT HSL HST HLT
    HX HY HZ HFA HFS HFL HFT)
    as (m1 & m2 & m3 & m4 & m5 & m6 & m7 & m8 & m9 & m10 & m11 & m12 & m13 & m14 & mf &
      C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 &
      XF & YF & ZF & AF & SF & LF & TF & BXF & BYF & BZF & HF).
  exists mf;split.
  - eapply exec_double_arithmetic_from_calls;
      [exact HA|exact HR|exact C1|exact C2|exact C3|exact C4|exact C5|exact C6|
       exact C7|exact C8|exact C9|exact C10|exact C11|exact C12|exact C13|exact C14|exact C15].
  - split;[exact XF|];split;[exact YF|];split;[exact ZF|].
    split;[exact AF|];split;[exact SF|];split;[exact LF|];split;[exact TF|].
    split;[exact BXF|];split;[exact BYF|];split;[exact BZF|exact HF].
Qed.
