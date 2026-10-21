(** Actual H/I zero-test call nodes and the nonzero-H dispatch. The tests
    execute from owned storage and compute zero modulo p, not raw-limb zero. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
  C.jet_secp_curve_statements C.jet_secp_mixed_difference C.jet_secp_field_zero_owned.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition mixed_zero_call (i : bool) := curve_call _secp256k1_fe_normalizes_to_zero_var
  f_secp256k1_fe_normalizes_to_zero_var (Some (if i then _t'1 else _t'2))
  [curve_local_address (if i then _i else _h)].
Definition mixed_zero_head := match mixed_after_difference with
  | Ssequence head _ => head | _ => Sskip end.
Definition mixed_after_zero := match mixed_after_difference with
  | Ssequence _ rest => rest | _ => Sskip end.
Definition mixed_zero_branch := match mixed_zero_head with
  | Ssequence _ (Sifthenelse _ branch _) => branch | _ => Sskip end.
Definition mixed_i_zero_branch := match mixed_zero_branch with
  | Ssequence (Ssequence _ branch) _ => branch | _ => Sskip end.
Lemma mixed_zero_source : mixed_after_difference=
  Ssequence (Ssequence (mixed_zero_call false)
    (Sifthenelse (Etempvar _t'2 tint) mixed_zero_branch Sskip)) mixed_after_zero.
Proof. reflexivity. Qed.
Lemma mixed_i_zero_source : mixed_zero_branch=
  Ssequence (Ssequence (mixed_zero_call true) mixed_i_zero_branch) (Sreturn None).
Proof. reflexivity. Qed.

Theorem exec_mixed_zero_call (i : bool) w e le m b :
  e!(if i then _i else _h)=Some (b,curve_fe_type) ->
  e!_secp256k1_fe_normalizes_to_zero_var=None ->
  square_input_bounds w -> fe_at m b 0 (words5 w) -> Mem.range_perm m b 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (mixed_zero_call i) E0
    (PTree.set (if i then _t'1 else _t'2) (Vint (field_zero_result w)) le) mf Out_normal /\
  fe_at mf b 0 (words5 w) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
  lframe (fun bx _=>bx<>b) m mf.
Proof.
  intros EB EN BW HF HP.
  destruct (eval_field_zero_owned w m b BW HF HP) as (mf & HC & HO & HFree & HL).
  exists mf;split;[|split;[exact HO|];split;assumption].
  unfold mixed_zero_call;eapply exec_curve_call with (vargs:=[Vptr b Ptrofs.zero]) (v:=Vint (field_zero_result w)).
  - unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
  - exact EN.
  - eapply eval_Econs;[apply eval_curve_local;exact EB|reflexivity|constructor].
  - exact HC.
Qed.

Theorem exec_mixed_nonzero_guard h e le m bh :
  e!_h=Some (bh,curve_fe_type) -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
  square_input_bounds h -> radix_value h mod feP<>0 ->
  fe_at m bh 0 (words5 h) -> Mem.range_perm m bh 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m mixed_zero_head E0
    (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal /\
  fe_at mf bh 0 (words5 h) /\ Mem.range_perm mf bh 0 40 Cur Freeable /\
  lframe (fun bx _=>bx<>bh) m mf.
Proof.
  intros EH EN BH HNZ HF HP.
  destruct (exec_mixed_zero_call false h e le m bh EH EN BH HF HP)
    as (mf & HC & HO & HFree & HL).
  assert (HZ : field_zero_result h=Int.zero).
  { unfold field_zero_result;apply Z.eqb_neq in HNZ;rewrite HNZ;reflexivity. }
  rewrite HZ in HC;exists mf;split;[|split;[exact HO|];split;assumption].
  change (Clight2.exec_stmt secp_ge e le m
    (Ssequence (mixed_zero_call false) (Sifthenelse (Etempvar _t'2 tint) mixed_zero_branch Sskip)) E0
    (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal).
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'2 (Vint Int.zero) le).
  - exact HC.
  - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
    + apply eval_Etempvar;apply PTree.gss.
    + reflexivity.
    + apply exec_Sskip.
Qed.
