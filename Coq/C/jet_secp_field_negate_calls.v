(** Original helper calls and canonical field representation. These calls are
    intermediate steps inside the real wrapper/writer, not a public jet proof. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp.
Require Import C.jet_sx_state C.jet_sx_mem C.jet_secp_local_regions.
Require Import C.jet_secp_field_negate_storage C.jet_secp_field_negate_values.
Require Import C.jet_secp_field_negate_normalize C.jet_secp_canonical_negate.
Require Import C.jet_secp_canonical_normalize.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma negate_normalizer_bounds rho :
  fe_limbs_ok (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat))
    (Int64.unsigned (rho 5%nat)) ->
  forall n, (n < 5)%nat -> Int64.unsigned (negate_value rho n) <= 2 ^ 60.
Proof.
  intros Hok n Hn. unfold fe_limbs_ok in Hok.
  assert (HInput : Int64.unsigned (rho (S n)) <=
    (if Nat.eqb n 4 then 281474976710655 else 4503599627370495)).
  { do 5 (destruct n as [|n]; [cbn; lia|]). lia. }
  rewrite (negate_value_unsigned rho n Hn HInput).
  pose proof (Int64.unsigned_range_2 (rho (S n))) as HUnsigned.
  change (2 ^ 60) with 1152921504606846976.
  do 5 (destruct n as [|n]; [cbn [negate_mask]; lia|]). lia.
Qed.

Theorem eval_negate_normalization_calls m b rho (x : Ty.tySem (Word 8)) :
  rep rho [(b,0)] local_write_initial_regs m ->
  fe_limbs_ok (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat))
    (Int64.unsigned (rho 5%nat)) ->
  fe_val (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat))
    (Int64.unsigned (rho 5%nat)) = @toZ (WordToZ 8) x ->
  @toZ (WordToZ 8) x < feP ->
  exists mn mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
      [Vptr b Ptrofs.zero; Vptr b Ptrofs.zero; Vint Int.one] E0 mn Vundef /\
    Clight2.eval_funcall secp_ge mn (Internal f_secp256k1_fe_normalize_var)
      [Vptr b Ptrofs.zero] E0 mf Vundef /\
    fe_at mf b 0 (map Int64.repr
      (fe_limbs_of (@toZ (WordToZ 8) (@canonical_fe_negate Alg.CoreFunSem x)))) /\
    Mem.range_perm mn b 0 40 Cur Freeable /\
    lframe (fun b' pos => ~ foot [(b,0)] (map rshape local_write_initial_regs) b' pos) m mn /\
    lframe (fun b' pos => ~ (b' = b /\ 0 <= pos < 40)) mn mf.
Proof.
  intros HRep Hok HValue Hlt.
  destruct (eval_field_negate_to_field m b rho HRep)
    as (mn & HNeg & HField & HFree & HFrame).
  pose proof (negate_normalizer_bounds rho Hok) as HB.
  destruct (eval_fe_normalize_var mn b 0 (negate_value rho 0)
    (negate_value rho 1) (negate_value rho 2) (negate_value rho 3)
    (negate_value rho 4) HField (HB 0%nat ltac:(lia)) (HB 1%nat ltac:(lia))
    (HB 2%nat ltac:(lia)) (HB 3%nat ltac:(lia)) (HB 4%nat ltac:(lia)))
    as (mf & HNorm & HResult & HNormFrame).
  rewrite (fe_negate_machine_normalized rho Hok ltac:(rewrite HValue; exact Hlt)) in HResult.
  rewrite HValue in HResult.
  rewrite <- canonical_field_order_matches_limb_model in HResult.
  rewrite <- canonical_fe_negate_numeric in HResult.
  exists mn, mf. split; [exact HNeg|]. split; [exact HNorm|].
  split; [exact HResult|]. split; [exact HFree|].
  split; assumption.
Qed.
Print Assumptions eval_negate_normalization_calls.
