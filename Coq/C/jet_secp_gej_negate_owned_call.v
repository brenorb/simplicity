(** Full original helper function execution, including entry and empty free.
    Internal result: unchanged X/Z and general public framing still separate. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_write_fe_numeric C.jet_secp_field_negate_storage.
Require Import C.jet_secp_gej_negate_flag C.jet_secp_gej_negate_owned_body.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem eval_gej_negate_owned_call m b value flag :
  0 <= value < 2^256 ->
  fe_at m b 40 (map Int64.repr (fe_limbs_of value)) ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  Mem.load Mint32 m b 120 = Some (Vint flag) ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_neg)
      [Vptr b Ptrofs.zero;Vptr b Ptrofs.zero] E0 mf Vundef /\
    fe_at mf b 40 (negate_values (write_fe_rho value 0)) /\
    Mem.range_perm mf b 0 128 Cur Freeable /\
    Mem.load Mint32 mf b 120 = Some (Vint flag).
Proof.
  intros HV HField HFree HFlag.
  destruct (exec_gej_negate_body_owned (gej_negate_helper_temps b 0) m b value flag
    (gej_negate_helper_temp_r b 0) (gej_negate_helper_temp_a b 0)
    HV HField HFree HFlag) as (mf & HBody & HFieldF & HFreeF & HFlagF).
  exists mf; split.
  - eapply eval_funcall_internal with (e := empty_env)
      (le1 := gej_negate_helper_temps b 0)
      (le2 := PTree.set _t'1 (Vint flag) (gej_negate_helper_temps b 0))
      (m1 := m) (m2 := mf) (out := Out_normal).
    + apply gej_negate_helper_entry.
    + exact HBody.
    + reflexivity.
    + reflexivity.
  - split; [exact HFieldF|]; split; assumption.
Qed.
Timeout 60 Print Assumptions eval_gej_negate_owned_call.
