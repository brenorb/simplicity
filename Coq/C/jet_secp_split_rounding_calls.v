(** Both original split-lambda coefficient calls, at their actual Scall
    statements. Intermediate executions and exact outputs are derived from
    the rounded-product proof and the literal coefficient bridge. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_statement_prefix C.jet_secp_scalar_constant C.jet_secp_split_multipliers
 C.jet_secp_split_coefficient C.jet_secp_split_round_literal C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_reader_support
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge split_multiplier_block.

Definition split_local_id (first:bool) := if first then _c1 else _c2.
Definition split_local_env bc1 bc2 := PTree.set _c2 (bc2,Tstruct __5826 noattr)
 (PTree.set _c1 (bc1,Tstruct __5826 noattr) empty_env).
Definition split_parts := split_statement_last (fn_body f_secp256k1_scalar_split_lambda).
Definition split_coefficient_statement (first:bool) := nth (if first then 3 else 4)%nat (fst split_parts) Sskip.
Definition split_rounding_prefix := statement_sequence (firstn 5 (fst split_parts)) Sskip.
Definition split_rounding_frame bk bc1 bc2 b (_:Z) := b<>bc1 /\ b<>bc2 /\ b<>bk /\
 b<>split_multiplier_block true /\ b<>split_multiplier_block false.

Lemma split_coefficient_call_source first : split_coefficient_statement first=
 curve_call _secp256k1_scalar_mul_shift_var f_secp256k1_scalar_mul_shift_var None
 [Eaddrof (Evar (split_local_id first) (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
  Etempvar _k (tptr (Tstruct __5826 noattr));
  Eaddrof (Evar (split_multiplier_id first) (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
  Econst_int (Int.repr 384) tint].
Proof. destruct first;reflexivity. Qed.

Lemma exec_split_coefficient_call (first:bool) bc1 bc2 le m mf bk : le!_k=Some (Vptr bk Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul_shift_var)
 [Vptr (if first then bc1 else bc2) Ptrofs.zero;Vptr bk Ptrofs.zero;
  Vptr (split_multiplier_block first) Ptrofs.zero;Vint (Int.repr 384)] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (split_local_env bc1 bc2) le m (split_coefficient_statement first) E0 le mf Out_normal.
Proof.
 intros K Call;rewrite split_coefficient_call_source.
 eapply (exec_curve_call _secp256k1_scalar_mul_shift_var f_secp256k1_scalar_mul_shift_var None _
  [Vptr (if first then bc1 else bc2) Ptrofs.zero;Vptr bk Ptrofs.zero;
   Vptr (split_multiplier_block first) Ptrofs.zero;Vint (Int.repr 384)] Vundef).
 - unfold secp_pure;repeat (first [left;reflexivity|right]).
 - reflexivity.
 - eapply eval_Econs with (v1:=Vptr (if first then bc1 else bc2) Ptrofs.zero);
   [apply eval_Eaddrof;apply eval_Evar_local;destruct first;reflexivity|reflexivity|].
   eapply eval_Econs;[apply eval_Etempvar;exact K|reflexivity|].
   eapply eval_Econs with (v1:=Vptr (split_multiplier_block first) Ptrofs.zero);
    [apply eval_Eaddrof;apply eval_Evar_global;
    [destruct first;reflexivity|apply split_multiplier_symbol]|reflexivity|].
   eapply eval_Econs;[constructor|reflexivity|constructor].
 - exact Call.
Qed.

Lemma exec_split_initial_noops e le m :
 Clight2.exec_stmt secp_ge e le m (statement_sequence (firstn 3 (fst split_parts)) Sskip) E0 le m Out_normal.
Proof.
 repeat (eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le);
  [eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le)
   (out1:=Out_normal) (out2:=Out_break);constructor|]);constructor.
Qed.

Theorem exec_split_rounding_prefix (k:Ty.tySem (Word 8)) le m bk bc1 bc2 :
 split_multipliers_ready m -> le!_k=Some (Vptr bk Ptrofs.zero) ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m bc1 0 32 Cur Freeable ->
 Mem.range_perm m bc2 0 32 Cur Freeable -> bc1<>bc2 -> bc1<>bk -> bc2<>bk ->
 exists mf,Clight2.exec_stmt secp_ge (split_local_env bc1 bc2) le m split_rounding_prefix E0 le mf Out_normal /\
 scalar_at mf bc1 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (@literal_split_coefficient true Alg.CoreFunSem k)))) /\
 scalar_at mf bc2 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (@literal_split_coefficient false Alg.CoreFunSem k)))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 8) k))) /\
 Mem.range_perm mf bc1 0 32 Cur Freeable /\ Mem.range_perm mf bc2 0 32 Cur Freeable /\
 Mem.range_perm mf bk 0 32 Cur Freeable /\ split_multipliers_ready mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (split_rounding_frame bk bc1 bc2) m mf.
Proof.
 intros Ready K Input FK F1 F2 Separate C1K C2K.
 destruct (eval_split_coefficient_literal true k m bk bc1 Ready Input FK F1 C1K)
  as (m1 & Call1 & Out1 & Input1 & F11 & FK1 & Ready1 & Keep1 & Preserve1 & Frame1).
 assert (F21:Mem.range_perm m1 bc2 0 32 Cur Freeable) by (intros pos Range;apply Keep1,F2;exact Range).
 destruct (eval_split_coefficient_literal false k m1 bk bc2 Ready1 Input1 FK1 F21 C2K)
  as (mf & Call2 & Out2 & InputF & F2F & FKF & ReadyF & Keep2 & Preserve2 & Frame2).
 assert (C1G2:bc1<>split_multiplier_block false) by
  (eapply scalar_constant_separate;[apply Ready1|exact F11]).
 assert (Out1F:scalar_at mf bc1 0
  (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (@literal_split_coefficient true Alg.CoreFunSem k))))).
 { eapply scalar_at_lframe;[exact Out1|exact Frame2|];intros;repeat split;assumption. }
 exists mf;split.
 - change (Clight2.exec_stmt secp_ge (split_local_env bc1 bc2) le m
    (statement_sequence (firstn 3 (fst split_parts)) (Ssequence (split_coefficient_statement true)
     (Ssequence (split_coefficient_statement false) Sskip))) E0 le mf Out_normal).
   eapply exec_statement_prefix_then_last;[apply exec_split_initial_noops|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
   + apply exec_split_coefficient_call with (bk:=bk);assumption.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
     * apply exec_split_coefficient_call with (bk:=bk);assumption.
     * constructor.
 - split;[exact Out1F|];split;[exact Out2|];split;[exact InputF|];split.
   + intros pos Range;apply Keep2,F11;exact Range.
   + split;[exact F2F|];split;[exact FKF|];split;[exact ReadyF|];split.
     * intros b pos kind perm Perm;apply Keep2,Keep1;exact Perm.
     * split;[eapply preserved_trans;[exact Preserve1|exact Preserve2]|].
       eapply lframe_trans.
       -- eapply lframe_implies;[exact Frame1|];unfold split_rounding_frame;intros;tauto.
       -- eapply lframe_implies;[exact Frame2|];unfold split_rounding_frame;intros;tauto.
Qed.
