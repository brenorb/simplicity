(** Execute the actual compound-context byte stores, including all 64 writes.
    The left-associated statement template matches clightgen's initializer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_sha256_context_fields.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition sha_ctx_local_field k := Efield (Evar ___compound (Tstruct _sha256_context noattr))
  (sha256_context_field k) (sha256_context_field_type k).
Definition sha_ctx_zero_stmt i := Sassign
  (Ederef (Ebinop Oadd (sha_ctx_local_field CtxBlock)
    (Econst_int (Int.repr (Z.of_nat i)) tint) (tptr tuchar)) tuchar) (Econst_int Int.zero tint).
Fixpoint sha_ctx_zero_prefix prefix n := match n with
  | O => prefix | S n => Ssequence (sha_ctx_zero_prefix prefix n) (sha_ctx_zero_stmt n) end.

Lemma eval_sha_ctx_local_field k e le m bc :
  e!___compound = Some (bc,Tstruct _sha256_context noattr) ->
  eval_lvalue ge0 e le m (sha_ctx_local_field k) bc (Ptrofs.repr (sha256_context_offset k)) Full.
Proof.
  intros HE. rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr (sha256_context_offset k))).
  eapply eval_Efield_struct.
  - eapply eval_Elvalue; [apply eval_Evar_local; exact HE|apply deref_loc_copy; reflexivity].
  - reflexivity.
  - vm_compute; reflexivity.
  - destruct k; vm_compute; reflexivity.
Qed.

Lemma exec_sha_ctx_zero_store e le m mf bc i :
  e!___compound = Some (bc,Tstruct _sha256_context noattr) -> (i < 64)%nat ->
  Mem.store Mint8unsigned m bc (16 + Z.of_nat i) (Vint Int.zero) = Some mf ->
  Clight2.exec_stmt ge0 e le m (sha_ctx_zero_stmt i) E0 le mf Out_normal.
Proof.
  intros HE HI HS.
  assert (Hsigned : Int.signed (Int.repr (Z.of_nat i)) = Z.of_nat i).
  { apply Int.signed_repr. change (-2147483648 <= Z.of_nat i <= 2147483647); lia. }
  eapply exec_Sassign_value with (v := Vint Int.zero) (v2 := Vint Int.zero)
    (b := bc) (ofs := Ptrofs.repr (16 + Z.of_nat i)).
  - apply eval_Ederef. eapply eval_Ebinop with (v1 := Vptr bc (Ptrofs.repr 16)) (v2 := Vint (Int.repr (Z.of_nat i))).
    + eapply eval_Elvalue; [apply eval_sha_ctx_local_field; exact HE|apply deref_loc_reference; reflexivity].
    + apply eval_Econst_int.
    + change (Some (Vptr bc (Ptrofs.add (Ptrofs.repr 16)
        (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr (Z.of_nat i)))))) =
        Some (Vptr bc (Ptrofs.repr (16 + Z.of_nat i)))).
      unfold Ptrofs.of_ints. rewrite Hsigned. unfold Ptrofs.mul, Ptrofs.add.
      change (Ptrofs.unsigned (Ptrofs.repr 16)) with 16.
      change (Ptrofs.unsigned (Ptrofs.repr 1)) with 1.
      rewrite (Ptrofs.unsigned_repr (Z.of_nat i)) by (change (0 <= Z.of_nat i <= 18446744073709551615); lia).
      rewrite Z.mul_1_l. rewrite (Ptrofs.unsigned_repr (Z.of_nat i)) by (change (0 <= Z.of_nat i <= 18446744073709551615); lia).
      reflexivity.
  - apply eval_Econst_int.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint8unsigned); [reflexivity|].
    unfold Mem.storev. rewrite Ptrofs.unsigned_repr by (change (0 <= 16 + Z.of_nat i <= 18446744073709551615); lia).
    exact HS.
Qed.

Theorem exec_sha_ctx_zero_prefix prefix n e le m mp bc :
  (n <= 64)%nat -> e!___compound = Some (bc,Tstruct _sha256_context noattr) ->
  Clight2.exec_stmt ge0 e le m prefix E0 le mp Out_normal ->
  Mem.range_perm mp bc 16 80 Cur Writable ->
  exists mf,
    Clight2.exec_stmt ge0 e le m (sha_ctx_zero_prefix prefix n) E0 le mf Out_normal /\
    (forall chunk b ofs, b <> bc \/ ofs + size_chunk chunk <= 16 \/ 16 + Z.of_nat n <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk mp b ofs) /\
    (forall b ofs kind p, Mem.perm mp b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block mp b -> Mem.valid_block mf b).
Proof.
  intros Hn HE HP HR. induction n as [|n IH].
  - exists mp. split; [exact HP|]. split; [intros; reflexivity|]. split; auto.
  - destruct (IH ltac:(lia)) as (mn & Hexec & Hloads & Hperm & Hvalid).
    assert (HW : Mem.valid_access mn Mint8unsigned bc (16 + Z.of_nat n) Writable).
    { split.
      - intros ofs Hrange. apply Hperm, HR. change (size_chunk Mint8unsigned) with 1 in Hrange; lia.
      - change (1 | 16 + Z.of_nat n). exists (16 + Z.of_nat n); lia. }
    destruct (Mem.valid_access_store mn Mint8unsigned bc (16 + Z.of_nat n) (Vint Int.zero) HW) as (mf & HS).
    exists mf. split.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mn);
        [exact Hexec|eapply exec_sha_ctx_zero_store; [exact HE|lia|exact HS]].
    + split.
      * intros chunk b ofs HO. erewrite Mem.load_store_other; [apply Hloads|exact HS|];
          change (size_chunk Mint8unsigned) with 1; rewrite Nat2Z.inj_succ in HO; lia.
      * split.
        -- intros b ofs kind p H. eapply Mem.perm_store_1; [exact HS|apply Hperm; exact H].
        -- intros b H. eapply Mem.store_valid_block_1; [exact HS|apply Hvalid; exact H].
Qed.
