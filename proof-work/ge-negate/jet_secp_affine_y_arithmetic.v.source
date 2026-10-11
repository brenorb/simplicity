(** Both original affine Y arithmetic calls, with actual ownership and framing. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_write_fe_numeric C.jet_secp_field_negate_storage.
Require Import C.jet_secp_affine_weak_exec C.jet_secp_affine_weak_owned C.jet_secp_affine_negate_owned.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem affine_y_arithmetic_calls m b value :
  0 <= value < 2^256 ->
  fe_at m b 40 (map Int64.repr (fe_limbs_of value)) ->
  Mem.range_perm m b 0 88 Cur Freeable ->
  exists mw mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
      [Vptr b (Ptrofs.repr 40)] E0 mw Vundef /\
    Clight2.eval_funcall secp_ge mw (Internal f_secp256k1_fe_negate)
      [Vptr b (Ptrofs.repr 40);Vptr b (Ptrofs.repr 40);Vint Int.one] E0 mf Vundef /\
    fe_at mf b 40 (negate_values (write_fe_rho value 0)) /\
    Mem.range_perm mf b 0 88 Cur Freeable /\
    lframe (fun bx pos => ~ foot [(b,0)] (map rshape (affine_initial_regs AffineY)) bx pos) m mf.
Proof.
  intros HV HField HFree.
  destruct (eval_affine_weak_reader_owned AffineY m b value HV HField HFree)
    as (mw & HWeak & HWeakField & HWeakFree & HWeakFrame).
  destruct (eval_affine_negate_reader_owned AffineY mw b value HWeakField HWeakFree)
    as (mf & HNegate & HNegateField & HNegateFree & HNegateFrame).
  exists mw,mf; split; [exact HWeak|]; split; [exact HNegate|].
  split; [exact HNegateField|]; split; [exact HNegateFree|].
  eapply lframe_trans; eassumption.
Qed.
Timeout 60 Print Assumptions affine_y_arithmetic_calls.
