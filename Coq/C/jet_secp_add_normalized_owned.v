(** Actual C helper execution from both normalized field stores.
    This is an intermediate boundary: the public readers still must produce
    these stores from the initial input frame, without assuming their calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Integers Values Memory Clight ClightBigstep Events.
Require Import Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_word_repr C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_canonical_normalize C.jet_secp_field_add C.jet_secp_field_add_initial.
Require Import C.jet_secp_field_add_values C.jet_secp_field_add_storage C.jet_secp_field_add_owned.
Require Import C.jet_secp_field_add_numeric C.jet_secp_add_reader_environment.
Require Import C.jet_secp_literal_add_program C.jet_secp_add_literal_writer C.jet_secp_write_fe_wide_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition normalized_add_rho (a b : Ty.tySem (Word 8)) : nat -> int64 :=
  add_reader_rho (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem a))
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem b)).

Lemma normalized_add_reader_facts a b :
  (forall n, (n < 5)%nat ->
    Int64.unsigned (normalized_add_rho a b (S n)) <= 2 ^ 52 - 1 /\
    Int64.unsigned (normalized_add_rho a b ((6 + n)%nat)) <= 2 ^ 52 - 1) /\
  field_input_value (normalized_add_rho a b) 1 =
    @toZ (WordToZ 8) a mod canonical_field_order /\
  field_input_value (normalized_add_rho a b) 6 =
    @toZ (WordToZ 8) b mod canonical_field_order.
Proof.
  unfold normalized_add_rho.
  assert (HA : 0 <= @toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem a) < 2 ^ 256)
    by apply word_toZ_range.
  assert (HB : 0 <= @toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem b) < 2 ^ 256)
    by apply word_toZ_range.
  split; [apply add_reader_bounds; assumption|].
  destruct (add_reader_values _ _ HA HB) as [VA VB].
  rewrite VA, VB, !canonical_fe_normalize_numeric. split; reflexivity.
Qed.

Theorem eval_field_add_from_normalized_fields m ba bb
    (a b : Ty.tySem (Word 8)) :
  ba <> bb ->
  fe_at m ba 0 (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem a)))) ->
  fe_at m bb 0 (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem b)))) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
      [Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero] E0 mf Vundef /\
    fe_at mf ba 0 (add_values (normalized_add_rho a b)) /\
    wide_fe_output (add_value (normalized_add_rho a b) 0)
      (add_value (normalized_add_rho a b) 1) (add_value (normalized_add_rho a b) 2)
      (add_value (normalized_add_rho a b) 3) (add_value (normalized_add_rho a b) 4) =
      @literal_fe_add Alg.CoreFunSem (a,b) /\
    Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
    lframe (fun b' pos => ~ foot [(ba,0);(bb,0)]
      (map rshape field_add_initial_regs) b' pos) m mf.
Proof.
  intros HSeparate HA HB HFreeA HFreeB.
  assert (HA' : fe_at m ba 0 (field_values (normalized_add_rho a b) 1)).
  { unfold normalized_add_rho. rewrite add_reader_field_first. exact HA. }
  assert (HB' : fe_at m bb 0 (field_values (normalized_add_rho a b) 6)).
  { unfold normalized_add_rho. rewrite add_reader_field_second. exact HB. }
  destruct (eval_field_add_owned m ba bb (normalized_add_rho a b)
    HSeparate HA' HB' HFreeA HFreeB) as (mf & HCall & HField & HFA & HFB & HFrame).
  destruct (normalized_add_reader_facts a b) as (HBounds & HVA & HVB).
  exists mf. split; [exact HCall|]. split; [exact HField|].
  split; [apply add_writer_literal_output; assumption|].
  split; [exact HFA|]. split; assumption.
Qed.
Print Assumptions normalized_add_reader_facts.
Print Assumptions eval_field_add_from_normalized_fields.
