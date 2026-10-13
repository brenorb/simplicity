(** Complete actual multiplication from the two reader stores, retaining both
    caller-owned scalar regions for the later real wrapper cleanup. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar_negate.
Require Import C.jet_secp_canonical_scalar.
Require Import C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
  C.jet_secp_scalar_writer_run.
Require Import C.jet_secp_scalar_mul_caller_alloc.
Require Import C.jet_secp_scalar_mul_reader_bridge.
Require Import C.jet_secp_scalar_mul_literal_both_owned.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_scalar_mul_from_normalized_scalars m ba bb (a b : Ty.tySem (Word 8)) :
  ba <> bb ->
  scalar_at m ba 0 (map Int64.repr (scalar_limbs_of
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem a)))) ->
  scalar_at m bb 0 (map Int64.repr (scalar_limbs_of
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem b)))) ->
  Mem.range_perm m ba 0 32 Cur Freeable -> Mem.range_perm m bb 0 32 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul)
      [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef /\
    rep (scalar_limb_rho (@toZ (WordToZ 8)
      (@canonical_scalar_multiply Alg.CoreFunSem (a,b)))) [(ba,0)] scalar_writer_initial_regs mf /\
    Mem.range_perm mf ba 0 32 Cur Freeable /\ Mem.range_perm mf bb 0 32 Cur Freeable /\
    lframe (fun block ofs => ~ foot [(ba,0);(bb,0)]
      (map rshape scalar_mul_caller_inputs) block ofs) m mf.
Proof.
  intros Hneq HA HB PA PB.
  pose proof (scalar_mul_initial_rep_from_storage _ _ m ba bb HA HB PA PB Hneq) as HR.
  destruct (scalar_mul_normalized_input_values a b) as [VA VB].
  exact (eval_scalar_mul_literal_both_owned (scalar_mul_normalized_rho a b)
    [(ba,0);(bb,0)] m a b HR VA VB).
Qed.
