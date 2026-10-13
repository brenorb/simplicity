(** Actual final assignment in read_gej; its store is derived from ownership. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Values Maps.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_gej_infinity_layout.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma exec_gej_read_flag_store le m mi b base flag :
  0 <= base -> base + 128 <= Ptrofs.max_unsigned ->
  le!_r = Some (Vptr b (Ptrofs.repr base)) ->
  le!_t'1 = Some (Vint flag) ->
  Mem.store Mint32 m b (base + 120) (Vint flag) = Some mi ->
  Clight2.exec_stmt secp_ge empty_env le m
    (Sassign
      (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
        (Tstruct __6123 noattr)) _infinity tint)
      (Etempvar _t'1 tint)) E0 le mi Out_normal.
Proof.
  intros HB HM HR HT HS.
  eapply exec_Sassign with (loc := b) (ofs := Ptrofs.repr (base + 120))
    (bf := Full) (v2 := Vint flag) (v := Vint flag).
  - apply eval_gej_infinity_field; [right;right;right;left;reflexivity|assumption|assumption|assumption].
  - apply eval_Etempvar; exact HT.
  - reflexivity.
  - eapply assign_loc_value with (chunk := Mint32); [reflexivity|].
    unfold Mem.storev. rewrite Ptrofs.unsigned_repr by lia. exact HS.
Qed.

Theorem exec_gej_read_flag_owned le m b base flag :
  0 <= base -> (8 | base) -> base + 128 <= Ptrofs.max_unsigned ->
  le!_r = Some (Vptr b (Ptrofs.repr base)) ->
  le!_t'1 = Some (Vint flag) ->
  Mem.range_perm m b base (base + 128) Cur Freeable ->
  exists mi,
    Clight2.exec_stmt secp_ge empty_env le m
      (Sassign
        (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
          (Tstruct __6123 noattr)) _infinity tint)
        (Etempvar _t'1 tint)) E0 le mi Out_normal /\
    Mem.load Mint32 mi b (base + 120) = Some (Vint flag) /\
    Mem.range_perm mi b base (base + 128) Cur Freeable /\
    (forall chunk b' ofs,
      b' <> b \/ ofs + size_chunk chunk <= base + 120 \/ base + 124 <= ofs ->
      Mem.load chunk mi b' ofs = Mem.load chunk m b' ofs) /\
    (forall b' ofs k p, Mem.perm mi b' ofs k p <-> Mem.perm m b' ofs k p) /\
    (forall b', Mem.valid_block m b' -> Mem.valid_block mi b').
Proof.
  intros HB HA HM HR HT HP.
  assert (HAccess : Mem.valid_access m Mint32 b (base + 120) Writable).
  { split.
    - intros ofs HOfs. eapply Mem.perm_implies; [apply HP|constructor].
      change (size_chunk Mint32) with 4 in HOfs; lia.
    - change (4 | base + 120). destruct HA as [k HK]. exists (2 * k + 30); lia. }
  destruct (Mem.valid_access_store m Mint32 b (base + 120) (Vint flag) HAccess)
    as [mi HS].
  exists mi; split.
  - eapply exec_gej_read_flag_store; eassumption.
  - split.
    + exact (Mem.load_store_same _ _ _ _ _ _ HS).
    + split.
      * intros ofs HOfs. eapply Mem.perm_store_1; [exact HS|apply HP;exact HOfs].
      * split.
        -- intros chunk b' ofs HOther. eapply Mem.load_store_other; [exact HS|].
           change (size_chunk Mint32) with 4.
           replace (base + 120 + 4) with (base + 124) by lia; exact HOther.
        -- split.
           ++ intros b' ofs k p; split.
              ** eapply Mem.perm_store_2; exact HS.
              ** eapply Mem.perm_store_1; exact HS.
           ++ intros b' HV. eapply Mem.store_valid_block_1; eauto.
Qed.
Print Assumptions exec_gej_read_flag_owned.
