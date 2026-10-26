(** Actual field oddness on owned machine limbs, including unreduced digests.
    No canonicality or mathematical parity modulo p is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem
  C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_field_predicates C.jet_secp_field_add_initial C.jet_secp_local_regions
  C.jet_secp_local_call C.jet_secp_curve_tail_values C.jet_secp_closed_helpers
  C.jet_secp_field_cmov C.jet_secp_multiply_normalize_bridge C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition field_words_odd (w:nat->int64) := Z.testbit (Int64.unsigned (w 0%nat)) 0.
Lemma field_words_odd_value w :
  Int64.unsigned (Int64.and (w 0%nat) Int64.one)=Z.b2z (field_words_odd w).
Proof.
  unfold Int64.and,field_words_odd.
  change (Int64.unsigned (Int64.repr (Z.land (Int64.unsigned (w 0%nat)) 1))=
    Z.b2z (Z.testbit (Int64.unsigned (w 0%nat)) 0)).
  replace 1 with (2^1-1) at 1 by reflexivity;rewrite land_ones_mod by lia.
  rewrite Int64.unsigned_repr by
    (pose proof (Z.mod_pos_bound (Int64.unsigned (w 0%nat)) (2^1) ltac:(lia));
      change Int64.max_unsigned with 18446744073709551615;lia).
  change (Int64.unsigned (w 0%nat) mod 2=Z.b2z (Z.testbit (Int64.unsigned (w 0%nat)) 0)).
  rewrite Z.bit0_mod;reflexivity.
Qed.

Lemma field_odd_words_initial w m b : fe_at m b 0 (words5 w) ->
  Mem.range_perm m b 0 40 Cur Freeable ->
  rep (curve_shift_words w) [(b,0)] local_write_initial_regs m.
Proof.
  intros Field Free;apply (rep_add _ [] [] m b 0);[apply rep_nil|cbn;tauto|].
  apply region_with_freeable.
  - apply field_region_from_values;rewrite curve_shift_field;exact Field.
  - reflexivity.
  - reflexivity.
  - exact Free.
  - apply field_region_storage_size.
Qed.

Theorem eval_field_odd_words w m b : fe_at m b 0 (words5 w) ->
  Mem.range_perm m b 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_odd)
    [Vptr b Ptrofs.zero] E0 mf (Vint (cmov_int (field_words_odd w))) /\
  Mem.range_perm mf b 0 40 Cur Freeable /\
  lframe (fun bx _=>bx<>b) m mf /\ readonly_preserved m mf.
Proof.
  intros Field Free.
  destruct (eval_field_odd_from_owned_region m [(b,0)] (curve_shift_words w)
    (field_odd_words_initial w m b Field Free)) as (mf & Call & Final & Frame).
  change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_odd)
    [Vptr b Ptrofs.zero] E0 mf
      (Vint (Int.repr (Int64.unsigned (Int64.and (w 0%nat) Int64.one))))) in Call.
  rewrite field_words_odd_value in Call.
  assert (Flag:Int.repr (Z.b2z (field_words_odd w))=cmov_int (field_words_odd w)) by
    (destruct (field_words_odd w);reflexivity).
  rewrite Flag in Call.
  pose proof (rep_free_region _ _ _ _ 0 40 Final ltac:(cbn;lia) eq_refl) as [_ FreeF].
  exists mf;split;[exact Call|];split;[exact FreeF|];split.
  - eapply lframe_implies;[exact Frame|];intros bx pos Other Valid;apply no_local_write_foot;exact Other.
  - eapply (secp_closed_function_preserved f_secp256k1_fe_is_odd);[reflexivity|reflexivity|exact Call].
Qed.
