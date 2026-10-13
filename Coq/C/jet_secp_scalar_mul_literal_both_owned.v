(** Complete original multiplication helper against the literal Core result.
    Reader normalization equalities are intermediate bridge inputs; the public
    wrapper must still establish them from its two actual reader calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar
  C.jet_secp_canonical_scalar_negate.
Require Import C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_writer_run.
Require Import C.jet_secp_scalar_mul512_low C.jet_secp_scalar_mul512_accumulate.
Require Import C.jet_secp_scalar_mul_caller_alloc
  C.jet_secp_scalar_mul_caller_function C.jet_secp_scalar_mul_caller_observed.
Require Import C.jet_secp_scalar_mul_writer_bridge C.jet_secp_scalar_mul_literal_numeric.
Require Import C.jet_secp_scalar_mul_owned_observed.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque scalar_mul_caller_words scalar_mul_caller_output.

Theorem eval_scalar_mul_literal_both_owned rho beta m (a b : Ty.tySem (Word 8)) :
  rep rho beta scalar_mul_caller_inputs m ->
  scalar_mul512_input_value rho 0 =
    @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem a) ->
  scalar_mul512_input_value rho 4 =
    @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem b) ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
    rep (scalar_limb_rho (@toZ (WordToZ 8)
      (@canonical_scalar_multiply Alg.CoreFunSem (a,b))))
      [(blk beta 0,bas beta 0)] scalar_writer_initial_regs mf /\
    Mem.range_perm mf (blk beta 0) 0 32 Cur Freeable /\
    Mem.range_perm mf (blk beta 1) 0 32 Cur Freeable /\
    lframe (fun block ofs => ~ foot beta (map rshape scalar_mul_caller_inputs) block ofs) m mf.
Proof.
  intros HR HA HB.
  destruct (eval_scalar_mul_call_second_owned_observed rho beta m HR)
    as (mf & HC & HL & HV & HP & HBFree & HF).
  pose proof (scalar_writer_initial_rep_from_mul rho beta mf HP HL) as HW.
  rewrite HA,HB,canonical_scalar_multiply_normalized_value in HV.
  rewrite HV in HW.
  destruct (scalar_mul_output_owned rho beta mf HP) as (_ & HO).
  exists mf. exact (conj HC (conj HW (conj HO (conj HBFree HF)))).
Qed.
