(** Derive the helper representation and values from two actual scalar stores.
    Storage/ownership premises are discharged by the public reader composition. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_word_repr C.jet_secp_canonical_scalar.
Require Import C.jet_secp_local_regions C.jet_secp_scalar_get_b32_numeric
  C.jet_secp_b32_exec
  C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_overflow_numeric
  C.jet_secp_scalar_negate_canonical C.jet_secp_scalar_writer_run
  C.jet_secp_scalar_writer_storage.
Require Import C.jet_sx_u64_transport C.jet_secp_scalar_mul512_low.
Require Import C.jet_secp_scalar_mul_caller_alloc.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_mul_reader_rho (va vb : Z) (n : nat) : int64 :=
  if (n <? 4)%nat then scalar_limb_rho va n else scalar_limb_rho vb (n-4)%nat.
Definition scalar_mul_normalized_rho (a b : Ty.tySem (Word 8)) :=
  scalar_mul_reader_rho
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem a))
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem b)).

Lemma scalar_mul_reader_input_values va vb :
  0 <= va < 2 ^ 256 -> 0 <= vb < 2 ^ 256 ->
  scalar_mul512_input_value (scalar_mul_reader_rho va vb) 0 = va /\
  scalar_mul512_input_value (scalar_mul_reader_rho va vb) 4 = vb.
Proof.
  intros HA HB.
  assert (HF : forall rho, scalar_mul512_input_value rho 0 = scalar_limb_value rho).
  { intro rho. unfold scalar_mul512_input_value,scalar_limb_value. cbn [Nat.add].
    change Int64.modulus with (2 ^ 64).
    assert (H2 : 2 ^ 128 = (2 ^ 64) ^ 2) by (vm_compute; reflexivity).
    assert (H3 : 2 ^ 192 = (2 ^ 64) ^ 3) by (vm_compute; reflexivity).
    rewrite H2,H3. ring. }
  assert (HS : scalar_mul512_input_value (scalar_mul_reader_rho va vb) 4 =
    scalar_mul512_input_value (scalar_limb_rho vb) 0) by reflexivity.
  rewrite HS,!HF.
  change (scalar_limb_value (scalar_limb_rho va) = va /\
    scalar_limb_value (scalar_limb_rho vb) = vb).
  split; apply scalar_limb_rho_value; assumption.
Qed.

Lemma scalar_mul_normalized_input_values (a b : Ty.tySem (Word 8)) :
  scalar_mul512_input_value (scalar_mul_normalized_rho a b) 0 =
    @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem a) /\
  scalar_mul512_input_value (scalar_mul_normalized_rho a b) 4 =
    @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem b).
Proof.
  unfold scalar_mul_normalized_rho. apply scalar_mul_reader_input_values;
    apply word_toZ_range.
Qed.

Theorem scalar_mul_initial_rep_from_storage va vb m ba bb :
  scalar_at m ba 0 (map Int64.repr (scalar_limbs_of va)) ->
  scalar_at m bb 0 (map Int64.repr (scalar_limbs_of vb)) ->
  Mem.range_perm m ba 0 32 Cur Freeable ->
  Mem.range_perm m bb 0 32 Cur Freeable -> ba <> bb ->
  rep (scalar_mul_reader_rho va vb) [(ba,0);(bb,0)] scalar_mul_caller_inputs m.
Proof.
  intros SA SB PA PB Hneq.
  pose proof (scalar_writer_initial_rep_from_storage va m ba SA PA) as RA.
  pose proof (scalar_writer_initial_rep_from_storage vb m bb SB PB) as RB.
  apply two_region_rep_separate; [reflexivity|exact Hneq| |].
  - eapply region_u64_transport with (rho := scalar_limb_rho va)
      (beta := [(ba,0)]) (r := 0%nat) (xs := [XLv 0;XLv 1;XLv 2;XLv 3])
      (ys := [XLv 0;XLv 1;XLv 2;XLv 3]) (w := true) (owned := Some 32).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact (rep_region _ _ _ m 0 _ RA eq_refl).
  - eapply region_u64_transport with (rho := scalar_limb_rho vb)
      (beta := [(bb,0)]) (r := 0%nat) (xs := [XLv 0;XLv 1;XLv 2;XLv 3])
      (ys := [XLv 4;XLv 5;XLv 6;XLv 7]) (w := true) (owned := Some 32).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact (rep_region _ _ _ m 0 _ RB eq_refl).
Qed.
