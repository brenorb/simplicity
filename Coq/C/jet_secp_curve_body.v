(** Actual complete finite-affine ge_is_valid_var body, not a replacement
    numeric specification. Public literal semantics and function entry follow. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns.
Require Import C.jet_secp_curve_calls C.jet_secp_curve_statements.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition curve_result (x y : nat -> int64) :=
  if Z.eqb ((radix_value y * radix_value y) mod feP)
    ((radix_value x * radix_value x * radix_value x+7) mod feP) then Int.one else Int.zero.
Definition curve_body_temps le x y :=
  PTree.set _t'1 (Vint (curve_result x y)) (PTree.set _t'2 (Vint Int.zero) le).

Theorem exec_curve_finite_body_readback le x y m ba b_y2 bx :
  le!_a = Some (Vptr ba Ptrofs.zero) -> Mem.load Mint32 m ba 80 = Some (Vint Int.zero) ->
  square_input_bounds x -> square_input_bounds y -> ba<>b_y2 -> ba<>bx -> b_y2<>bx ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) ->
  Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m b_y2 0 40 Cur Freeable -> Mem.range_perm m bx 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge (curve_helper_env b_y2 bx) le m (fn_body f_secp256k1_ge_is_valid_var)
    E0 (curve_body_temps le x y) mf (Out_return (Some (Vint (curve_result x y),tint))) /\
  fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
  Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf b_y2 0 40 Cur Freeable /\ Mem.range_perm mf bx 0 40 Cur Freeable /\
  lframe (fun b _ => b<>ba /\ b<>b_y2 /\ b<>bx) m mf /\
  Mem.load Mint32 mf ba 80=Mem.load Mint32 m ba 80.
Proof.
  intros HA HFlag BX BY HAY HAX HYX HX HY HFA HFY HFX.
  destruct (curve_six_arithmetic_calls_readback x y m ba b_y2 bx BX BY HAY HAX HYX HX HY HFA HFY HFX)
    as (m1 & m2 & m3 & m4 & m5 & mf & C1 & C2 & C3 & C4 & C5 & C6 & HXF & HYF & HAF & HYFree & HXFree & HF & FlagReadback).
  change (Clight2.eval_funcall secp_ge m5 (Internal f_secp256k1_fe_equal_var)
    [Vptr b_y2 Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf (Vint (curve_result x y))) in C6.
  assert (HA' : (PTree.set _t'2 (Vint Int.zero) le)!_a = Some (Vptr ba Ptrofs.zero)).
  { rewrite PTree.gso by discriminate; exact HA. }
  exists mf. split.
  - rewrite curve_valid_body_source. unfold curve_body_temps.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'2 (Vint Int.zero) le).
    + apply exec_curve_flag_finite with (ba:=ba); assumption.
    + exact (exec_curve_arithmetic_from_calls (PTree.set _t'2 (Vint Int.zero) le)
        m m1 m2 m3 m4 m5 mf ba b_y2 bx (curve_result x y) HA' C1 C2 C3 C4 C5 C6).
  - split; [exact HXF|]. split; [exact HYF|]. split; [exact HAF|].
    split; [exact HYFree|]. split; [exact HXFree|]. split;[exact HF|exact FlagReadback].
Qed.

Theorem exec_curve_finite_body le x y m ba b_y2 bx :
  le!_a = Some (Vptr ba Ptrofs.zero) -> Mem.load Mint32 m ba 80 = Some (Vint Int.zero) ->
  square_input_bounds x -> square_input_bounds y -> ba<>b_y2 -> ba<>bx -> b_y2<>bx ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) ->
  Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m b_y2 0 40 Cur Freeable -> Mem.range_perm m bx 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge (curve_helper_env b_y2 bx) le m (fn_body f_secp256k1_ge_is_valid_var)
    E0 (curve_body_temps le x y) mf (Out_return (Some (Vint (curve_result x y),tint))) /\
  fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
  Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf b_y2 0 40 Cur Freeable /\ Mem.range_perm mf bx 0 40 Cur Freeable /\
  lframe (fun b _ => b<>ba /\ b<>b_y2 /\ b<>bx) m mf.
Proof.
 intros HA HFlag BX BY HAY HAX HYX HX HY HFA HFY HFX.
 destruct (exec_curve_finite_body_readback le x y m ba b_y2 bx HA HFlag BX BY HAY HAX HYX HX HY HFA HFY HFX)
   as (mf & Rest).
 exists mf;tauto.
Qed.
