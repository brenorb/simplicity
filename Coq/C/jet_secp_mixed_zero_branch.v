(** The H=0 early-return paths in the original mixed-addition helper.
    Derive the I test, doubling or infinity initialization from owned storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_field_zero_owned C.jet_secp_mixed_zero C.jet_secp_double_var_owned
  C.jet_secp_double_var_statements C.jet_secp_double_all_calls C.jet_secp_gej_infinity_owned
  C.jet_secp_local_regions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition mixed_double_call := curve_call _secp256k1_gej_double_var f_secp256k1_gej_double_var None
  [Etempvar _r (tptr (Tstruct __6123 noattr));Etempvar _a (tptr (Tstruct __6123 noattr));
   Etempvar _rzr (tptr curve_fe_type)].
Definition mixed_inverse_body := match mixed_i_zero_branch with
  | Sifthenelse _ _ branch => branch | _ => Sskip end.
Definition mixed_infinity_call := curve_call _secp256k1_gej_set_infinity f_secp256k1_gej_set_infinity None
  [Etempvar _r (tptr (Tstruct __6123 noattr))].
Lemma mixed_i_dispatch_source : mixed_i_zero_branch=
  Sifthenelse (Etempvar _t'1 tint) mixed_double_call mixed_inverse_body.
Proof. reflexivity. Qed.
Lemma mixed_inverse_source : mixed_inverse_body=
  Ssequence (Sifthenelse double_var_null_test
    (curve_call _secp256k1_fe_set_int f_secp256k1_fe_set_int None
      [Etempvar _rzr (tptr curve_fe_type);Econst_int Int.zero tint]) Sskip) mixed_infinity_call.
Proof. reflexivity. Qed.

Local Ltac keep_branch_field HF Frame :=
  eapply field_at_lframe;[exact HF|exact Frame|];intro pos;congruence.
Local Ltac keep_branch_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;congruence.
Local Ltac original_pure := unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
Local Ltac keep_temp H := rewrite PTree.gso by discriminate;exact H.

Theorem exec_mixed_equal_branch e le m bp bi x y z i :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_i=Some (bi,curve_fe_type) -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
  e!_secp256k1_gej_double_var=None -> bp<>bi ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds i ->
  radix_value i mod feP=0 -> Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) -> fe_at m bi 0 (words5 i) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m mixed_zero_branch E0 (PTree.set _t'1 (Vint Int.one) le) mf (Out_return None) /\
  fe_at mf bp 0 (words5 (double_output_x_words x y)) /\
  fe_at mf bp 40 (words5 (double_output_y_words x y)) /\
  fe_at mf bp 80 (words5 (double_output_z_words y z)) /\
  Mem.load Mint32 mf bp 120=Some (Vint (double_var_zflag y z)) /\
  fe_at mf bi 0 (words5 i) /\ Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  square_input_bounds (double_output_x_words x y) /\ square_input_bounds (double_output_y_words x y) /\
  square_input_bounds (double_output_z_words y z) /\ lframe (fun bx _=>bx<>bp /\ bx<>bi) m mf.
Proof.
  intros HA HR HN EI EN ED Sep BX BY BZ BI IZ Flag X Y Z I PF IF.
  destruct (exec_mixed_zero_call true i e le m bi EI EN BI I IF)
    as (mz & CI & IZ0 & IF0 & FI).
  assert (VI : field_zero_result i=Int.one) by (unfold field_zero_result;rewrite IZ;reflexivity).
  rewrite VI in CI.
  assert (XZ : fe_at mz bp 0 (words5 x)) by (keep_branch_field X FI).
  assert (YZ : fe_at mz bp 40 (words5 y)) by (keep_branch_field Y FI).
  assert (ZZ : fe_at mz bp 80 (words5 z)) by (keep_branch_field Z FI).
  assert (PFZ : Mem.range_perm mz bp 0 128 Cur Freeable) by (keep_branch_free PF FI).
  assert (FlagZ : Mem.load Mint32 mz bp 120=Some (Vint Int.zero)).
  { rewrite (proj1 FI Mint32 bp 120);[exact Flag| |intros pos HP;exact Sep].
    eapply Mem.perm_valid_block;apply (PF 0);lia. }
  destruct (eval_double_var_finite x y z mz bp BX BY BZ FlagZ XZ YZ ZZ PFZ)
    as (mf & CD & XO & YO & ZO & FlagO & PFO & BXO & BYO & BZO & FD).
  assert (IO : fe_at mf bi 0 (words5 i)) by (keep_branch_field IZ0 FD).
  assert (IFO : Mem.range_perm mf bi 0 40 Cur Freeable) by (keep_branch_free IF0 FD).
  assert (Frame : lframe (fun bx _=>bx<>bp /\ bx<>bi) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FI|];intros bx pos [_ HI] HV;exact HI.
    - eapply lframe_implies;[exact FD|];intros bx pos [HP HI] HV;exact HP. }
  exists mf;split.
  - rewrite mixed_i_zero_source.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'1 (Vint Int.one) le).
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=PTree.set _t'1 (Vint Int.one) le).
      * exact CI.
      * rewrite mixed_i_dispatch_source;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
        -- apply eval_Etempvar;apply PTree.gss.
        -- reflexivity.
        -- unfold mixed_double_call;eapply exec_curve_call with
             (vargs:=[Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vlong Int64.zero]) (v:=Vundef).
           ++ original_pure.
           ++ exact ED.
           ++ eapply eval_Econs;[apply eval_Etempvar;keep_temp HR|reflexivity|].
              eapply eval_Econs;[apply eval_Etempvar;keep_temp HA|reflexivity|].
              eapply eval_Econs;[apply eval_Etempvar;keep_temp HN|reflexivity|constructor].
           ++ exact CD.
    + apply exec_Sreturn_none.
  - repeat (first [assumption|split]).
Qed.

Theorem exec_mixed_inverse_branch e le m bp bi i :
  le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_i=Some (bi,curve_fe_type) -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
  e!_secp256k1_gej_set_infinity=None -> bp<>bi ->
  square_input_bounds i -> radix_value i mod feP<>0 -> fe_at m bi 0 (words5 i) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m mixed_zero_branch E0 (PTree.set _t'1 (Vint Int.zero) le) mf (Out_return None) /\
  fe_at mf bp 0 (repeat Int64.zero 5) /\ fe_at mf bp 40 (repeat Int64.zero 5) /\
  fe_at mf bp 80 (repeat Int64.zero 5) /\ Mem.load Mint32 mf bp 120=Some (Vint Int.one) /\
  fe_at mf bi 0 (words5 i) /\ Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
  lframe (fun bx _=>bx<>bp /\ bx<>bi) m mf.
Proof.
  intros HR HN EI EN EF Sep BI INZ I PF IF.
  destruct (exec_mixed_zero_call true i e le m bi EI EN BI I IF)
    as (mz & CI & IZ & IFZ & FI).
  assert (VI : field_zero_result i=Int.zero).
  { unfold field_zero_result;apply Z.eqb_neq in INZ;rewrite INZ;reflexivity. }
  rewrite VI in CI.
  assert (PFZ : Mem.range_perm mz bp 0 128 Cur Freeable) by (keep_branch_free PF FI).
  destruct (eval_gej_infinity_initializer_owned mz bp 0 ltac:(lia) ltac:(exists 0;reflexivity)
    ltac:(change (128<=18446744073709551615);lia) (freeable_range_writable _ _ _ _ PFZ))
    as (mf & CF & XO & YO & ZO & FlagO & LF & Perm & Valid).
  assert (FF : lframe (fun bx _=>bx<>bp) mz mf).
  { split.
    - intros ch bx pos HV HP;apply LF;left;apply (HP pos);pose proof (size_chunk_pos ch);lia.
    - split;[intros bx pos k p HV HP HQ;apply (proj2 (Perm bx pos k p));exact HQ|exact Valid]. }
  assert (IO : fe_at mf bi 0 (words5 i)) by (keep_branch_field IZ FF).
  assert (IFO : Mem.range_perm mf bi 0 40 Cur Freeable) by (keep_branch_free IFZ FF).
  assert (PFO : Mem.range_perm mf bp 0 128 Cur Freeable).
  { intros pos HP;apply (proj2 (Perm bp pos Cur Freeable));apply PFZ;exact HP. }
  assert (Frame : lframe (fun bx _=>bx<>bp /\ bx<>bi) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FI|];intros bx pos [_ HI] HV;exact HI.
    - eapply lframe_implies;[exact FF|];intros bx pos [HP HI] HV;exact HP. }
  exists mf;split.
  - rewrite mixed_i_zero_source.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'1 (Vint Int.zero) le).
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=PTree.set _t'1 (Vint Int.zero) le).
      * exact CI.
      * rewrite mixed_i_dispatch_source;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
        -- apply eval_Etempvar;apply PTree.gss.
        -- reflexivity.
        -- rewrite mixed_inverse_source.
           eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mz) (le1:=PTree.set _t'1 (Vint Int.zero) le).
           ++ eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
              ** apply eval_double_var_null_test;keep_temp HN.
              ** reflexivity.
              ** apply exec_Sskip.
           ++ unfold mixed_infinity_call;eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero]) (v:=Vundef).
              ** original_pure.
              ** exact EF.
              ** eapply eval_Econs;[apply eval_Etempvar;keep_temp HR|reflexivity|constructor].
              ** exact CF.
    + apply exec_Sreturn_none.
  - repeat (first [assumption|split]).
Qed.
