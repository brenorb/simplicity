(** Restore the inverse caller's representation from the original divstep
    stores and return. This starts at the terminal matrix-store boundary;
    it does not assume or prove execution of the complete batch or CTZ. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_sx_region_lframe C.jet_sx_u64_transport.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions C.jet_secp_fe_nv.
Require Import C.jet_secp_modinfo_fe_global C.jet_secp_modinv_var_seed C.jet_secp_modinv_var_de.
Require Import C.jet_secp_modinv_var_invariant C.jet_secp_div62_invariant C.jet_secp_div62_finish C.jet_secp_div62_exit C.divstep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition inv_batch_result_rho st (rho : nat->int64) n :=
  if (n <? 25)%nat then rho n
  else if (n <? 29)%nat then div62_exit_words st (n-25)%nat else rho n.

Lemma inv_batch_result_prefix st rho n : (n<25)%nat -> inv_batch_result_rho st rho n=rho n.
Proof.
  intro N;unfold inv_batch_result_rho;destruct (n <? 25)%nat eqn:E;
    [reflexivity|apply Nat.ltb_ge in E;lia].
Qed.

Lemma inv_batch_result_matrix st rho : inv_matrix_matches (inv_batch_result_rho st rho) st.
Proof.
  change (Int64.signed (Int64.repr (Trans.u (Trans.transN 62 st)))=Trans.u (Trans.transN 62 st) /\
    Int64.signed (Int64.repr (Trans.v (Trans.transN 62 st)))=Trans.v (Trans.transN 62 st) /\
    Int64.signed (Int64.repr (Trans.q (Trans.transN 62 st)))=Trans.q (Trans.transN 62 st) /\
    Int64.signed (Int64.repr (Trans.r (Trans.transN 62 st)))=Trans.r (Trans.transN 62 st)).
  repeat split.
  - exact (div62_matrix_field_signed st 0 ltac:(lia)).
  - exact (div62_matrix_field_signed st 1 ltac:(lia)).
  - exact (div62_matrix_field_signed st 2 ltac:(lia)).
  - exact (div62_matrix_field_signed st 3 ltac:(lia)).
Qed.

Lemma inv_batch_matrix_region st rho beta m : bas beta 6=0 ->
  Mem.range_perm m (blk beta 6) 0 32 Cur Freeable ->
  (forall j,(j<4)%nat -> Mem.load Mint64 m (blk beta 6) (8*Z.of_nat j)=Some(Vlong(div62_exit_words st j))) ->
  region_ok (inv_batch_result_rho st rho) beta m 6
    (mkreg (u64_cells 0 [XLv 25;XLv 26;XLv 27;XLv 28]) true (Some 32)).
Proof.
  intros Base Free Loads.
  apply (region_with_freeable _ _ _ _ (mkreg (u64_cells 0 [XLv 25;XLv 26;XLv 27;XLv 28]) true None) 32).
  - apply region_u64;try rewrite Base.
    + lia.
    + exists 0;reflexivity.
    + change (0+8*4<=18446744073709551615);lia.
    + eapply Mem.perm_valid_block;apply (Free 0);lia.
    + change (Mem.range_perm m (blk beta 6) 0 32 Cur Writable);now apply freeable_range_writable.
    + intros j x At.
      assert (J : (j<4)%nat) by
        (change (j<length [XLv 25;XLv 26;XLv 27;XLv 28])%nat;apply nth_error_Some;rewrite At;discriminate).
      destruct j as [|[|[|[|j]]]];try lia;injection At as <-;
        (split;[apply Loads;lia|reflexivity]).
  - exact Base.
  - reflexivity.
  - exact Free.
  - repeat constructor;cbn;lia.
Qed.

Lemma inv_batch_restore st rho beta m mf : rep rho beta inv_seed_regs m ->
  Mem.range_perm mf (blk beta 6) 0 32 Cur Freeable ->
  (forall j,(j<4)%nat -> Mem.load Mint64 mf (blk beta 6) (8*Z.of_nat j)=Some(Vlong(div62_exit_words st j))) ->
  lframe (fun b _=>b<>blk beta 6) m mf -> rep (inv_batch_result_rho st rho) beta inv_loop_regs mf.
Proof.
  intros Rep Free Loads Frame;pose proof Rep as (Len & Sep & Regions).
  assert (Base : bas beta 6=0).
  { exact (proj1 (rep_free_region rho beta inv_seed_regs m 6 32 Rep ltac:(change (6<7)%nat;lia) eq_refl)). }
  assert (Others : forall r reg,nth_error inv_seed_regs r=Some reg -> r<>6%nat ->
    region_ok rho beta mf r reg).
  { intros r reg At Ne;eapply region_ok_lframe;[exact Frame| |exact (Regions _ _ At)].
    intros pos;destruct (Sep r 6%nat reg inv_seed_matrix Ne At eq_refl) as [Different|(_ & NoOwner & _)];
      [exact Different|discriminate NoOwner]. }
  split;[exact Len|];split.
  - apply (rsep_shape beta inv_seed_regs);[reflexivity|exact Sep].
  - intros r reg At;assert (R : (r<7)%nat) by
      (change (r<length inv_loop_regs)%nat;apply nth_error_Some;rewrite At;discriminate).
    destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;
      cbn [inv_loop_regs nth_error] in At;injection At as <-.
    + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=0%nat) (xs:=vars5 0) (ys:=vars5 0);
        try reflexivity;apply Others;[reflexivity|discriminate].
    + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=1%nat)
        (xs:=map XLc modinfo_fe_words) (ys:=map XLc modinfo_fe_words);
        try reflexivity;apply Others;[reflexivity|discriminate].
    + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=2%nat) (xs:=vars5 5) (ys:=vars5 5);
        try reflexivity;apply Others;[reflexivity|discriminate].
    + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=3%nat) (xs:=vars5 10) (ys:=vars5 10);
        try reflexivity;apply Others;[reflexivity|discriminate].
    + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=4%nat) (xs:=vars5 15) (ys:=vars5 15);
        try reflexivity;apply Others;[reflexivity|discriminate].
    + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=5%nat) (xs:=vars5 20) (ys:=vars5 20);
        try reflexivity;apply Others;[reflexivity|discriminate].
    + apply inv_batch_matrix_region;assumption.
Qed.

Theorem exec_inv_batch_exit le m rho beta st precision :
  -683<=eta st<683 -> rep rho beta inv_seed_regs m ->
  div62_loop_invariant st precision 62 0 (blk beta 6) le -> exists lef mf,
  Clight2.exec_stmt secp_ge empty_env le m div62_finish E0 lef mf
    (Out_return (Some(Vlong(Int64.repr(eta(fst(stepN 62 st)))),tlong))) /\
  rep (inv_batch_result_rho st rho) beta inv_loop_regs mf /\
  inv_matrix_matches (inv_batch_result_rho st rho) st /\
  Int64.signed(Int64.repr(eta(fst(stepN 62 st))))=eta(fst(stepN 62 st)) /\
  lframe (fun b _=>b<>blk beta 6) m mf.
Proof.
  intros Eta Rep Inv.
  destruct (rep_free_region rho beta inv_seed_regs m 6 32 Rep ltac:(change (6<7)%nat;lia) eq_refl)
    as (Base & Free).
  destruct (exec_div62_exit le m st precision (blk beta 6) Eta Inv Free)
    as (lef & mf & Run & Loads & Returned & Owned & Frame).
  assert (Exact : forall j,(j<4)%nat ->
    Mem.load Mint64 mf (blk beta 6) (8*Z.of_nat j)=Some(Vlong(div62_exit_words st j))).
  { intros j J;destruct (Loads j J) as (w & Load & Signed).
    rewrite div62_exit_words_field by exact J;rewrite <-Signed,Int64.repr_signed;exact Load. }
  exists lef,mf;split;[exact Run|];split.
  - exact (inv_batch_restore st rho beta m mf Rep Owned Exact Frame).
  - split;[apply inv_batch_result_matrix|];split;assumption.
Qed.
