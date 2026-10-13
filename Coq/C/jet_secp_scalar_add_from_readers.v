(** Actual helper-to-literal execution from both concrete normalized reader
    stores. The public reader and writer calls remain separate obligations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_numeric.
Require Import C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_writer_run.
Require Import C.jet_secp_scalar_add_run C.jet_secp_scalar_add_numeric.
Require Import C.jet_secp_scalar_add_initial C.jet_secp_scalar_add_reader_environment.
Require Import C.jet_secp_canonical_scalar_add C.jet_secp_scalar_add_literal_owned.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_scalar_add_from_normalized_scalars m ba bb (a b : Ty.tySem (Word 8)) :
  ba <> bb ->
  scalar_at m ba 0 (map Int64.repr (scalar_limbs_of
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem a)))) ->
  scalar_at m bb 0 (map Int64.repr (scalar_limbs_of
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem b)))) ->
  Mem.range_perm m ba 0 32 Cur Freeable -> Mem.range_perm m bb 0 32 Cur Freeable ->
  exists mf ret,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_add)
      [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero] E0 mf (Vint ret) /\
    rep (scalar_limb_rho (@toZ (WordToZ 8) (@canonical_scalar_add Alg.CoreFunSem (a,b))))
      [(ba,0)] scalar_writer_initial_regs mf /\
    Mem.range_perm mf ba 0 32 Cur Freeable /\ Mem.range_perm mf bb 0 32 Cur Freeable /\
    lframe (fun block ofs => ~ foot [(ba,0);(bb,0)]
      (map rshape scalar_add_initial_regs) block ofs) m mf.
Proof.
  intros HSeparate HA HB HFreeA HFreeB.
  assert (HRep : rep (scalar_add_normalized_rho a b) [(ba,0);(bb,0)] scalar_add_initial_regs m).
  { apply scalar_add_initial_from_owned_scalars; [exact HSeparate| | |exact HFreeA|exact HFreeB].
    - unfold scalar_add_normalized_rho; rewrite scalar_add_reader_values_first; exact HA.
    - unfold scalar_add_normalized_rho; rewrite scalar_add_reader_values_second; exact HB. }
  destruct (scalar_add_normalized_reader_values a b) as [HVA HVB].
  destruct (eval_scalar_add_literal_owned (scalar_add_normalized_rho a b) [(ba,0);(bb,0)]
    m a b HRep HVA HVB) as (mf & HCall & HWriter & HFA & HFB & HFrame).
  cbn [blk bas lay nth fst snd] in HCall, HWriter, HFA, HFB.
  exists mf, (b2i (Z.leb canonical_group_order (scalar_add_input_value (scalar_add_normalized_rho a b)))).
  split; [exact HCall|]; split; [exact HWriter|]; split; [exact HFA|]; split; assumption.
Qed.
