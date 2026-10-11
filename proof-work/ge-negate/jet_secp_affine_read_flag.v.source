(** Original affine reader's zero flag store, derived from real 88-byte ownership. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Values Maps.
Require Import C.jet_secp_linkage C.jets_secp C.jet_sx_mem C.jet_secp_affine_fields.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition affine_read_flag_stmt : statement :=
  Sassign (Efield (Ederef (Etempvar _r (tptr (Tstruct __6121 noattr)))
    (Tstruct __6121 noattr)) _infinity tint) (Econst_int Int.zero tint).

Lemma exec_affine_read_flag_store le m mf b :
  le!_r = Some (Vptr b Ptrofs.zero) ->
  Mem.store Mint32 m b 80 (Vint Int.zero) = Some mf ->
  Clight2.exec_stmt secp_ge empty_env le m affine_read_flag_stmt E0 le mf Out_normal.
Proof.
  intros HR HS; unfold affine_read_flag_stmt.
  eapply exec_Sassign with (loc := b) (ofs := Ptrofs.repr 80)
    (bf := Full) (v2 := Vint Int.zero) (v := Vint Int.zero).
  - exact (eval_affine_pointer_field le m b 0 _r _infinity 80 tint
      ltac:(cbn;tauto) ltac:(lia) ltac:(change (88 <= 18446744073709551615);lia) HR).
  - apply eval_Econst_int.
  - reflexivity.
  - eapply assign_loc_value with (chunk := Mint32); [reflexivity|].
    unfold Mem.storev; change (Mem.store Mint32 m b 80 (Vint Int.zero) = Some mf); exact HS.
Qed.

Theorem exec_affine_read_flag_owned le m b :
  le!_r = Some (Vptr b Ptrofs.zero) -> Mem.range_perm m b 0 88 Cur Freeable ->
  exists mf,
    Clight2.exec_stmt secp_ge empty_env le m affine_read_flag_stmt E0 le mf Out_normal /\
    Mem.load Mint32 mf b 80 = Some (Vint Int.zero) /\
    Mem.range_perm mf b 0 88 Cur Freeable /\
    (forall chunk bx ofs, bx <> b \/ ofs+size_chunk chunk <= 80 \/ 84 <= ofs ->
      Mem.load chunk mf bx ofs = Mem.load chunk m bx ofs) /\
    lframe (fun bx _ => bx <> b) m mf.
Proof.
  intros HR HP.
  assert (HAccess : Mem.valid_access m Mint32 b 80 Writable).
  { split.
    - intros pos HPos; eapply Mem.perm_implies; [apply HP|constructor].
      change (size_chunk Mint32) with 4 in HPos; lia.
    - change (4 | 80); exists 20; reflexivity. }
  destruct (Mem.valid_access_store m Mint32 b 80 (Vint Int.zero) HAccess) as [mf HS].
  assert (HLoads : forall chunk bx ofs, bx <> b \/ ofs+size_chunk chunk <= 80 \/ 84 <= ofs ->
    Mem.load chunk mf bx ofs = Mem.load chunk m bx ofs).
  { intros chunk bx ofs HOther; eapply Mem.load_store_other; [exact HS|].
    change (size_chunk Mint32) with 4; exact HOther. }
  exists mf; split; [eapply exec_affine_read_flag_store; eassumption|].
  split; [exact (Mem.load_store_same _ _ _ _ _ _ HS)|]. split.
  - intros pos HPos; eapply Mem.perm_store_1; [exact HS|apply HP;exact HPos].
  - split; [exact HLoads|]. split.
    + intros chunk bx ofs HV HOther; apply HLoads; left.
      apply (HOther ofs); pose proof (size_chunk_pos chunk); lia.
    + split.
      * intros bx ofs kind perm HV HOther HPerm; eapply Mem.perm_store_1; eassumption.
      * intros bx HV; eapply Mem.store_valid_block_1; eauto.
Qed.
Print Assumptions exec_affine_read_flag_owned.
