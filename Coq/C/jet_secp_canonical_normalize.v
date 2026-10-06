(** Literal fe_normalize port from pinned Programs/LibSecp256k1.hs:467-469.
    This is a canonical-program bridge, not a C jet equivalence theorem. *)
From Coq Require Import ZArith Lia List.
Import ListNotations.
From compcert Require Import Integers AST Clight ClightBigstep Events.
Require Import C.jet_secp_linkage C.jet_secp_fe_nv C.jet_sx_mem C.jets_secp.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ C.jet_predicate_spec C.jet_subtract_spec C.jet_secp_fe_math.
Local Open Scope Z_scope.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

(** fieldOrder is the literal 0xffff...fffffefffffc2f in the pinned Haskell. *)
Definition canonical_field_order : Z :=
  115792089237316195423570985008687907853269984665640564039457584007908834671663.
Definition canonical_field_word : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) canonical_field_order.
Definition canonical_fe_normalize {term : Alg.Core.Algebra} : term (Word 8) (Word 8) :=
  ((iden &&& (unit >>> Alg.scribe canonical_field_word) >>> @subtract_word_spec term 8) &&& iden)
  >>> (O O H &&& (O I H &&& I H))
  >>> cond (I H) (O H).

Lemma canonical_field_order_matches_limb_model : canonical_field_order = feP.
Proof. vm_compute; reflexivity. Qed.
Lemma canonical_field_order_range :
  0 < canonical_field_order < word_modulus 8 /\
  word_modulus 8 < 2 * canonical_field_order.
Proof. vm_compute; repeat split; discriminate. Qed.
Lemma canonical_field_word_value :
  @toZ (WordToZ 8) canonical_field_word = canonical_field_order.
Proof.
  unfold canonical_field_word; rewrite to_fromZ.
  apply Z.mod_small.
  change (0 <= canonical_field_order < word_modulus 8).
  pose proof canonical_field_order_range; lia.
Qed.
Local Opaque subtract_word_spec canonical_field_word.

Lemma canonical_fe_normalize_step (x : Ty.tySem (Word 8)) :
  @canonical_fe_normalize Alg.CoreFunSem x =
  let z := @subtract_word_spec Alg.CoreFunSem 8 (x, canonical_field_word) in
  match fst z with inl _ => snd z | inr _ => x end.
Proof.
  change ((let z := @subtract_word_spec Alg.CoreFunSem 8
      (x, @Alg.scribe Ty.Unit (Word 8) canonical_field_word Alg.CoreFunSem tt) in
    match fst z with inl _ => snd z | inr _ => x end) =
    (let z := @subtract_word_spec Alg.CoreFunSem 8 (x, canonical_field_word) in
     match fst z with inl _ => snd z | inr _ => x end)).
  rewrite Alg.scribe_correct; reflexivity.
Qed.

Theorem canonical_fe_normalize_numeric (x : Ty.tySem (Word 8)) :
  @toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem x) =
    @toZ (WordToZ 8) x mod canonical_field_order.
Proof.
  rewrite canonical_fe_normalize_step.
  set (v := @toZ (WordToZ 8) x).
  set (payload := @fromZ (WordToZ 8) (v - canonical_field_order)).
  assert (HSub : @subtract_word_spec Alg.CoreFunSem 8 (x, canonical_field_word) =
    ((if v <? canonical_field_order then inr tt else inl tt), payload)).
  { symmetry.
    rewrite <- canonical_field_word_value at 1.
    apply subtract_representation_matches.
    unfold payload; rewrite to_fromZ, canonical_field_word_value; reflexivity. }
  rewrite HSub; cbn [fst snd].
  pose proof (word_value_bounds 8 x) as HX; fold v in HX.
  destruct canonical_field_order_range as [[HP HM] HTwice].
  destruct (v <? canonical_field_order) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. symmetry; apply Z.mod_small; lia.
  - apply Z.ltb_ge in Hlt.
    unfold payload; rewrite to_fromZ.
    fold (word_modulus 8).
    rewrite Z.mod_small by lia.
    replace v with ((v - canonical_field_order) + 1 * canonical_field_order)%Z at 2 by ring.
    rewrite Z.mod_add by lia; rewrite Z.mod_small by lia; reflexivity.
Qed.

Local Open Scope Z_scope.

Lemma canonical_fe_normalize_limb_bridge (x : Ty.tySem (Word 8)) z0 z1 z2 z3 z4 :
  0 <= z0 <= 2 ^ 60 -> 0 <= z1 <= 2 ^ 60 -> 0 <= z2 <= 2 ^ 60 ->
  0 <= z3 <= 2 ^ 60 -> 0 <= z4 <= 2 ^ 60 ->
  fe_val z0 z1 z2 z3 z4 = @toZ (WordToZ 8) x ->
  nvz_list z0 z1 z2 z3 z4 =
    fe_limbs_of (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem x)).
Proof.
  intros B0 B1 B2 B3 B4 HValue.
  pose proof (nvz_spec z0 z1 z2 z3 z4 B0 B1 B2 B3 B4) as HSpec.
  unfold nvz_list.
  destruct (nvz z0 z1 z2 z3 z4) as [[[[r0 r1] r2] r3] r4] eqn:HResult.
  destruct HSpec as [HBounds HMod].
  apply fe_limbs_unique; [exact HBounds|].
  rewrite canonical_fe_normalize_numeric, canonical_field_order_matches_limb_model.
  rewrite <- HValue; exact HMod.
Qed.

(** Actual normalization helper -> canonical program. Byte/frame reader and
    writer lifecycles are still required for the public fe_normalize jet. *)
Theorem eval_fe_normalize_var_against_canonical_program m b ofs
    t0 t1 t2 t3 t4 (x : Ty.tySem (Word 8)) :
  fe_at m b ofs [t0; t1; t2; t3; t4] ->
  Int64.unsigned t0 <= 2 ^ 60 -> Int64.unsigned t1 <= 2 ^ 60 ->
  Int64.unsigned t2 <= 2 ^ 60 -> Int64.unsigned t3 <= 2 ^ 60 ->
  Int64.unsigned t4 <= 2 ^ 60 ->
  fe_val (Int64.unsigned t0) (Int64.unsigned t1) (Int64.unsigned t2)
    (Int64.unsigned t3) (Int64.unsigned t4) = @toZ (WordToZ 8) x ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Ctypes.Internal f_secp256k1_fe_normalize_var)
      [Values.Vptr b (Ptrofs.repr ofs)] E0 mf Values.Vundef /\
    fe_at mf b ofs
      (List.map Int64.repr
        (fe_limbs_of (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem x)))) /\
    lframe (fun other pos => ~ (other = b /\ ofs <= pos < ofs + 40)) m mf.
Proof.
  intros HFe B0 B1 B2 B3 B4 HValue.
  destruct (eval_fe_normalize_var m b ofs t0 t1 t2 t3 t4 HFe B0 B1 B2 B3 B4)
    as [mf [HExec [HOutput HFrame]]].
  exists mf; split; [exact HExec|]; split; [|exact HFrame].
  assert (HBridge : nvz_list (Int64.unsigned t0) (Int64.unsigned t1)
      (Int64.unsigned t2) (Int64.unsigned t3) (Int64.unsigned t4) =
    fe_limbs_of (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem x))).
  { apply canonical_fe_normalize_limb_bridge; try exact HValue.
    all: split; [apply Int64.unsigned_range|assumption]. }
  rewrite HBridge in HOutput; exact HOutput.
Qed.

(** read_fe can normalize an out-of-field input, then write_fe normalizes
    again. This identity is needed for that actual C lifecycle. *)
Lemma canonical_fe_normalize_idempotent (x : Ty.tySem (Word 8)) :
  @canonical_fe_normalize Alg.CoreFunSem
    (@canonical_fe_normalize Alg.CoreFunSem x) =
  @canonical_fe_normalize Alg.CoreFunSem x.
Proof.
  apply (toZ_injective (WordToZ 8)).
  rewrite !canonical_fe_normalize_numeric.
  apply Z.mod_mod; pose proof canonical_field_order_range; lia.
Qed.
