(** Actual by-copy field assignment r2 = a.x in gej_eq_x_var. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_b32_exec.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_gej_infinity_layout.
Require Import C.jet_struct_copy_loads C.jet_secp_local_regions.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition x_equiv_copy_stmt :=
  Sassign (Evar _r2 (Tstruct __5467 noattr))
    (Efield (Ederef (Etempvar _a (tptr (Tstruct __6123 noattr)))
      (Tstruct __6123 noattr)) _x (Tstruct __5467 noattr)).

Lemma eval_x_equiv_point_x e le m ba : le!_a = Some (Vptr ba Ptrofs.zero) ->
  eval_lvalue secp_ge e le m
    (Efield (Ederef (Etempvar _a (tptr (Tstruct __6123 noattr)))
      (Tstruct __6123 noattr)) _x (Tstruct __5467 noattr)) ba Ptrofs.zero Full.
Proof.
  intro HA. destruct (gej_infinity_field_layout _x 0 ltac:(left;reflexivity)) as (co & HC & HO).
  change Ptrofs.zero with (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0)).
  eapply eval_Efield_struct with (co:=co) (delta:=0).
  - eapply eval_Elvalue.
    + apply eval_Ederef. apply eval_Etempvar; exact HA.
    + apply deref_loc_copy; reflexivity.
  - reflexivity.
  - exact HC.
  - exact HO.
Qed.

Theorem exec_x_equiv_copy_owned e le m ba br2 w :
  e!_r2 = Some (br2,Tstruct __5467 noattr) ->
  le!_a = Some (Vptr ba Ptrofs.zero) -> ba<>br2 ->
  fe_at m ba 0 (words5 w) -> Mem.range_perm m br2 0 40 Cur Freeable ->
  exists mf,
    Clight2.exec_stmt secp_ge e le m x_equiv_copy_stmt E0 le mf Out_normal /\
    fe_at mf br2 0 (words5 w) /\ Mem.range_perm mf br2 0 40 Cur Freeable /\
    lframe (fun b _ => b<>br2) m mf.
Proof.
  intros HR2 HA HNe HField HFree.
  pose proof HField as (H0 & HAlign & HMax & HPerm & HLoads).
  assert (HReadable : Mem.range_perm m ba 0 40 Cur Readable).
  { intros pos HPos; eapply Mem.perm_implies; [apply HPerm;exact HPos|constructor]. }
  destruct (Mem.range_perm_loadbytes m ba 0 40 HReadable) as (bytes & HL).
  pose proof (Mem.loadbytes_length _ _ _ _ _ HL) as HLen.
  assert (HW : Mem.range_perm m br2 0 (0+Z.of_nat (length bytes)) Cur Writable).
  { rewrite HLen. change (Mem.range_perm m br2 0 40 Cur Writable).
    apply freeable_range_writable; exact HFree. }
  destruct (Mem.range_perm_storebytes m br2 0 bytes HW) as (mf & HS).
  assert (HDest : Mem.loadbytes mf br2 0 40 = Some bytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HS) as HD.
    rewrite HLen in HD; exact HD. }
  exists mf. split.
  - unfold x_equiv_copy_stmt. eapply exec_Sassign_copy with (b:=br2) (ofs:=Ptrofs.zero)
      (b':=ba) (ofs':=Ptrofs.zero) (v:=Vptr ba Ptrofs.zero).
    + apply eval_Evar_local; exact HR2.
    + eapply eval_Elvalue.
      * apply eval_x_equiv_point_x; exact HA.
      * apply deref_loc_copy; reflexivity.
    + reflexivity.
    + eapply assign_loc_copy with (b':=ba) (ofs':=Ptrofs.zero) (bytes:=bytes).
      * reflexivity.
      * intros _; change (8|0); exists 0; reflexivity.
      * intros _; change (8|0); exists 0; reflexivity.
      * left; congruence.
      * exact HL.
      * exact HS.
  - split.
    + split; [lia|]. split; [exists 0; reflexivity|].
      split; [change (40<=18446744073709551615);lia|]. split.
      * intros pos HPos; eapply Mem.perm_storebytes_1; [exact HS|].
        eapply Mem.perm_implies; [apply HFree;exact HPos|constructor].
      * intros i x HN.
        assert (HIdx : (i<5)%nat).
        { change (i<length (words5 w))%nat; apply nth_error_Some; rewrite HN;discriminate. }
        assert (HZ : 0<=Z.of_nat i<5) by (pose proof (Nat2Z.is_nonneg i);lia).
        eapply equal_loadbytes_field with (m1:=m) (b1:=ba) (base1:=0) (n:=40) (bytes:=bytes).
        -- lia.
        -- change (size_chunk Mint64) with 8;lia.
        -- exact HL.
        -- exact HDest.
        -- change (8 | 0+8*Z.of_nat i); exists (Z.of_nat i);ring.
        -- exact (HLoads i x HN).
    + split.
      * intros pos HPos; eapply Mem.perm_storebytes_1; [exact HS|apply HFree;exact HPos].
      * apply lframe_unchanged; eapply Mem.storebytes_unchanged_on; [exact HS|].
        intros pos HPos HNot; apply HNot; reflexivity.
Qed.
Print Assumptions exec_x_equiv_copy_owned.
