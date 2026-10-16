(** Derive borrowed multiplication inputs from the actual reader and global. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_word_repr C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_sx_u64_transport
  C.jet_secp_b32_exec C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
  C.jet_secp_scalar_writer_run C.jet_secp_scalar_writer_storage
  C.jet_secp_scalar_mul512_low C.jet_secp_scalar_mul_reader_bridge.
Require Import C.jet_secp_scalar_mul_borrowed_alloc C.jet_secp_scalar_mul_borrowed_function
  C.jet_secp_scalar_lambda_global C.jet_secp_scalar_lambda_region.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque scalar_lambda_block.

Theorem scalar_lambda_inputs_from_storage va m ba :
  scalar_at m ba 0 (map Int64.repr (scalar_limbs_of va)) ->
  Mem.range_perm m ba 0 32 Cur Freeable -> ba <> scalar_lambda_block ->
  scalar_lambda_global_rep m ->
  rep (scalar_lambda_mixed_rho (scalar_limb_rho va))
    [(ba,0);(scalar_lambda_block,0)] scalar_mul_borrowed_inputs m.
Proof.
  intros SA PA Hneq HG.
  pose proof (scalar_writer_initial_rep_from_storage va m ba SA PA) as RA.
  apply two_region_rep_separate; [reflexivity|exact Hneq| |].
  - eapply region_u64_transport with (rho := scalar_limb_rho va) (beta := [(ba,0)])
      (r := 0%nat) (xs := [XLv 0;XLv 1;XLv 2;XLv 3])
      (ys := [XLv 0;XLv 1;XLv 2;XLv 3]) (w := true) (owned := Some 32).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact (rep_region _ _ _ m 0 _ RA eq_refl).
  - exact (scalar_lambda_borrowed_region (scalar_limb_rho va)
      [(ba,0);(scalar_lambda_block,0)] m 1 eq_refl HG).
Qed.

Lemma scalar_lambda_mixed_normalized_value (value : Ty.tySem (Word 8)) :
  scalar_mul512_input_value (scalar_lambda_mixed_rho (scalar_limb_rho
    (@toZ (WordToZ 8) (@C.jet_secp_canonical_scalar.canonical_scalar_normalize Alg.CoreFunSem value)))) 0 =
  @toZ (WordToZ 8) (@C.jet_secp_canonical_scalar.canonical_scalar_normalize Alg.CoreFunSem value).
Proof.
  set (v := @toZ (WordToZ 8) (@C.jet_secp_canonical_scalar.canonical_scalar_normalize Alg.CoreFunSem value)).
  change (scalar_mul512_input_value (scalar_mul_reader_rho v v) 0 = v).
  exact (proj1 (scalar_mul_reader_input_values v v
    (word_toZ_range 8 (@C.jet_secp_canonical_scalar.canonical_scalar_normalize Alg.CoreFunSem value))
    (word_toZ_range 8 (@C.jet_secp_canonical_scalar.canonical_scalar_normalize Alg.CoreFunSem value)))).
Qed.
Lemma scalar_lambda_mixed_global_value rho :
  scalar_mul512_input_value (scalar_lambda_mixed_rho rho) 4 = canonical_lambda_value.
Proof. vm_compute; reflexivity. Qed.

Lemma scalar_lambda_global_from_region rho ba m :
  region_ok (scalar_lambda_mixed_rho rho) [(ba,0);(scalar_lambda_block,0)] m 1
    scalar_mul_borrowed_rhs -> scalar_lambda_global_rep m.
Proof.
  intros HR; pose proof HR as (_ & HV & _ & HC & _).
  change (Mem.valid_block m scalar_lambda_block) in HV.
  assert (HP : forall i x, nth_error [XLv 4;XLv 5;XLv 6;XLv 7] i = Some x ->
    Mem.range_perm m scalar_lambda_block (8 * Z.of_nat i) (8 * Z.of_nat i + 8) Cur Readable).
  { intros i x HX.
    pose proof (u64_cells_nth [XLv 4;XLv 5;XLv 6;XLv 7] 0 i x HX) as Hcell.
    pose proof (proj1 (Forall_forall _ _) HC _ Hcell) as (_ & _ & HP & _).
    change (Mem.range_perm m scalar_lambda_block (0+(0+8*Z.of_nat i))
      (0+(0+8*Z.of_nat i)+8) Cur Readable) in HP.
    rewrite !Z.add_0_l in HP; exact HP. }
  unfold scalar_lambda_global_rep; split; [exact HV|]. split.
  - intros ofs Ho.
    destruct (Z_lt_ge_dec ofs 8) as [H8|H8]; [apply (HP 0%nat (XLv 4) eq_refl); cbn; lia|].
    destruct (Z_lt_ge_dec ofs 16) as [H16|H16]; [apply (HP 1%nat (XLv 5) eq_refl); cbn; lia|].
    destruct (Z_lt_ge_dec ofs 24) as [H24|H24]; [apply (HP 2%nat (XLv 6) eq_refl); cbn; lia|].
    apply (HP 3%nat (XLv 7) eq_refl); cbn; lia.
  - intros i w Hnth.
    assert (HX : nth_error [XLv 4;XLv 5;XLv 6;XLv 7] i = Some (XLv (i+4)%nat)).
    { destruct i as [|[|[|[|i]]]]; try reflexivity;
        cbn [scalar_lambda_words nth_error] in Hnth; destruct i; discriminate. }
    pose proof (u64_cells_nth [XLv 4;XLv 5;XLv 6;XLv 7] 0 i (XLv (i+4)%nat) HX) as Hcell.
    pose proof (region_load _ _ _ _ _ _ _ _ HR Hcell) as HL.
    change (Mem.load Mint64 m scalar_lambda_block (0+(0+8*Z.of_nat i)) =
      Some (Vlong (scalar_lambda_mixed_rho rho (i+4)%nat))) in HL.
    rewrite !Z.add_0_l,(scalar_lambda_mixed_rhs rho i w Hnth) in HL; exact HL.
Qed.
