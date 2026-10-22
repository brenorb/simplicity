(** Actual weak normalization of loose limbs, retaining its changed output.
    In particular, point-negation outputs need not be positioned or canonical. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_field_add_initial C.jet_secp_curve_weak
 C.jet_secp_curve_weak_math C.jet_secp_field_weak_tight C.jet_secp_curve_frame
 C.jet_secp_local_regions C.jet_secp_field_mul_small C.jet_secp_field_negate_separate
 C.jet_secp_field_negate_values C.jet_secp_field_negate_storage C.jet_secp_write_fe_numeric
 C.jet_secp_b32_exec C.jet_secp_multiply_finish_product.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition weak_loose_words (w : nat -> int64) i := Int64.repr (nth i
 (curve_weak_math_list (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
  (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat))) 0).

Lemma weak_loose_words_list w : words5 (weak_loose_words w)=map Int64.repr
 (curve_weak_math_list (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
  (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat))).
Proof.
 unfold words5,weak_loose_words,curve_weak_math_list.
 destruct (curve_weak_math (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
  (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat))) as [[[[r0 r1] r2] r3] r4].
 reflexivity.
Qed.

Lemma weak_loose_numeric w : (forall i,(i<5)%nat -> Int64.unsigned (w i)<=2^60) ->
 radix_value (weak_loose_words w) mod feP=radix_value w mod feP /\ mul_small_input_bounds (weak_loose_words w).
Proof.
 intro Bound.
 assert (Range : forall i,(i<5)%nat -> 0<=Int64.unsigned (w i)<=2^60)
  by (intros;split;[apply Int64.unsigned_range_2|apply Bound;assumption]).
 pose proof (curve_weak_math_spec _ _ _ _ _ (Range 0%nat ltac:(lia)) (Range 1%nat ltac:(lia))
  (Range 2%nat ltac:(lia)) (Range 3%nat ltac:(lia)) (Range 4%nat ltac:(lia))) as Spec.
 unfold weak_loose_words,curve_weak_math_list.
 destruct (curve_weak_math (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
  (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat))) as [[[[r0 r1] r2] r3] r4].
 destruct Spec as (Val & B0 & B1 & B2 & B3 & B4).
 assert (Machine : forall r,0<=r<=281474976710912 \/ 0<=r<=4503599627370495 -> 0<=r<=Int64.max_unsigned)
  by (intros;change Int64.max_unsigned with 18446744073709551615;lia).
 split.
 - rewrite !radix_value_matches_normalizer.
   change (fe_val (Int64.unsigned (Int64.repr r0)) (Int64.unsigned (Int64.repr r1))
    (Int64.unsigned (Int64.repr r2)) (Int64.unsigned (Int64.repr r3)) (Int64.unsigned (Int64.repr r4)) mod feP=
    fe_val (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat)) (Int64.unsigned (w 2%nat))
     (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat)) mod feP).
   rewrite !Int64.unsigned_repr by (apply Machine;tauto);exact Val.
 - intros i HI;destruct i as [|[|[|[|[|i]]]]];try lia;
    cbn [nth Nat.eqb];rewrite Int64.unsigned_repr by (apply Machine;tauto);lia.
Qed.

Theorem eval_field_weak_loose w m b :
 (forall i,(i<5)%nat -> Int64.unsigned (w i)<=2^60) ->
 fe_at m b 0 (words5 w) -> Mem.range_perm m b 0 40 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
  [Vptr b Ptrofs.zero] E0 mf Vundef /\
 fe_at mf b 0 (words5 (weak_loose_words w)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
 radix_value (weak_loose_words w) mod feP=radix_value w mod feP /\
 mul_small_input_bounds (weak_loose_words w) /\ lframe (fun bx _=>bx<>b) m mf.
Proof.
 intros Bound Field Free.
 assert (ShiftBound : forall n,(1<=n<=5)%nat -> Int64.unsigned (weak_shift_words w n)<=2^60).
 { intros [|i] HI;[lia|cbn [weak_shift_words];apply Bound;lia]. }
 rewrite <-weak_shift_values in Field.
 destruct (eval_curve_weak_owned (weak_shift_words w) m b Field Free ShiftBound)
  as (mf & Call & Result & FreeF & FrameF).
 change (fe_at mf b 0 (map Int64.repr (curve_weak_math_list (Int64.unsigned (w 0%nat))
  (Int64.unsigned (w 1%nat)) (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat))))) in Result.
 rewrite <-weak_loose_words_list in Result.
 destruct (weak_loose_numeric w Bound) as [Value Tight].
 exists mf;split;[exact Call|];split;[exact Result|];split;[exact FreeF|];split;[exact Value|];split;[exact Tight|].
 eapply curve_frame_one with (regs:=local_write_initial_regs);[reflexivity|exact FrameF].
Qed.

Lemma negate_reader_words value :
 negate_values (write_fe_rho value 0)=words5 (negate_sep_words (limb_rho value)).
Proof. reflexivity. Qed.

Lemma negate_reader_loose_bound value : 0<=value<2^256 ->
 forall i,(i<5)%nat -> Int64.unsigned (negate_sep_words (limb_rho value) i)<=2^60.
Proof.
 intros Value.
 assert (Input : mul_small_input_bounds (limb_rho value)).
 { intros i HI;rewrite limb_rho_unsigned by exact Value.
   pose proof (proj1 (fe_limbs_of_ok value Value)) as Bounds;unfold fe_limbs_ok in Bounds.
   destruct i as [|[|[|[|[|i]]]]];try lia;cbn [nth fe_limbs_of Nat.eqb];lia. }
 intros i HI;rewrite negate_sep_unsigned by assumption.
 pose proof (Int64.unsigned_range_2 (limb_rho value i)).
 destruct i as [|[|[|[|[|i]]]]];try lia;cbn [negate_mask];lia.
Qed.
