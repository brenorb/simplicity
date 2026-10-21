(** Actual left-associated stores of a 32-byte zero compound literal.
    The initial memory is only writable; zero contents are established by
    execution, not assumed. Used by issuance_hash's new-issuance branch. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_exec C.jets_elements C.jet_elements_linkage.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_sha_program.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64 sha_ge elements_ge.
Set Default Timeout 15.

Definition eis_zero_byte_stmt (id : ident) (j : nat) : statement :=
  Sassign
    (Ederef (Ebinop Oadd (Evar id (tarray tuchar 32))
      (Econst_int (Int.repr (Z.of_nat j)) tint) (tptr tuchar)) tuchar)
    (Econst_int Int.zero tint).

Fixpoint eis_zero_array_prefix (id : ident) (n : nat) : statement :=
  match n with
  | O => Sskip
  | S k => match k with
           | O => eis_zero_byte_stmt id O
           | S _ => Ssequence (eis_zero_array_prefix id k) (eis_zero_byte_stmt id k)
           end
  end.

Lemma exec_eis_zero_byte e le m mf id b j :
  e!id = Some (b, tarray tuchar 32) -> (j < 32)%nat ->
  Mem.store Mint8unsigned m b (Z.of_nat j) (Vint Int.zero) = Some mf ->
  Clight2.exec_stmt sha_ge e le m (eis_zero_byte_stmt id j) E0 le mf Out_normal.
Proof.
  intros HE HJ HS.
  assert (HJZ : 0 <= Z.of_nat j <= 31) by lia.
  assert (Hsigned : Int.signed (Int.repr (Z.of_nat j)) = Z.of_nat j).
  { apply Int.signed_repr. change (-2147483648 <= Z.of_nat j <= 2147483647). lia. }
  assert (Haddr : Ptrofs.add Ptrofs.zero
      (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr (Z.of_nat j)))) = Ptrofs.repr (Z.of_nat j)).
  { unfold Ptrofs.of_ints. rewrite Hsigned. unfold Ptrofs.mul, Ptrofs.add.
    change (Ptrofs.unsigned Ptrofs.zero) with 0.
    change (Ptrofs.unsigned (Ptrofs.repr 1)) with 1.
    rewrite (Ptrofs.unsigned_repr (Z.of_nat j)) by
      (change Ptrofs.max_unsigned with 18446744073709551615; lia).
    rewrite Z.mul_1_l, Ptrofs.unsigned_repr by
      (change Ptrofs.max_unsigned with 18446744073709551615; lia).
    reflexivity. }
  unfold eis_zero_byte_stmt.
  eapply exec_Sassign_value with (v := Vint Int.zero) (v2 := Vint Int.zero)
    (b := b) (ofs := Ptrofs.repr (Z.of_nat j)).
  - apply eval_Ederef. eapply eval_Ebinop with (v1 := Vptr b Ptrofs.zero)
      (v2 := Vint (Int.repr (Z.of_nat j))).
    + eapply eval_Elvalue; [apply eval_Evar_local; exact HE|].
      apply deref_loc_reference; reflexivity.
    + apply eval_Econst_int.
    + change (Some (Vptr b (Ptrofs.add Ptrofs.zero
        (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr (Z.of_nat j)))))) =
        Some (Vptr b (Ptrofs.repr (Z.of_nat j)))).
      rewrite Haddr. reflexivity.
  - constructor.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint8unsigned); [reflexivity|].
    unfold Mem.storev. rewrite Ptrofs.unsigned_repr by
      (change Ptrofs.max_unsigned with 18446744073709551615; lia).
    exact HS.
Qed.

Definition eis_array_init_actual : statement :=
  ltac:(let body := eval cbv delta [f_simplicity_issuance_hash fn_body] beta iota in
      (fn_body f_simplicity_issuance_hash) in
    let rec seek s :=
      lazymatch s with
      | Ssequence ?l (Scall _ (Evar _sha256_uchars _) _) => exact l
      | Ssequence ?l ?r => first [seek l | seek r]
      | Sifthenelse _ ?l ?r => first [seek l | seek r]
      end in seek body).

Lemma eis_zero_array_shape :
  eis_array_init_actual = eis_zero_array_prefix ___compound__3 32.
Proof. reflexivity. Qed.

Theorem exec_eis_zero_array_prefix e le id b n :
  e!id = Some (b, tarray tuchar 32) -> (n <= 32)%nat ->
  forall m, Mem.range_perm m b 0 32 Cur Writable ->
  exists mf,
    Clight2.exec_stmt sha_ge e le m (eis_zero_array_prefix id n) E0 le mf Out_normal /\
    (forall j, (j < n)%nat -> Mem.load Mint8unsigned mf b (Z.of_nat j) = Some (Vint Int.zero)) /\
    (forall ch bb off, bb <> b \/ off + size_chunk ch <= 0 \/ 32 <= off ->
      Mem.load ch mf bb off = Mem.load ch m bb off) /\
    (forall bb off k p, Mem.perm m bb off k p -> Mem.perm mf bb off k p) /\
    (forall bb, Mem.valid_block m bb -> Mem.valid_block mf bb).
Proof.
  intros HE HN. induction n as [|n IH]; intros m HP.
  - exists m. split; [apply exec_Sskip|]. split; [intros j HJ; lia|].
    split; [intros; reflexivity|]. split; auto.
  - destruct (IH ltac:(lia) m HP) as (ms & EX & ZS & LS & PS & VS).
    assert (HW : Mem.valid_access ms Mint8unsigned b (Z.of_nat n) Writable).
    { split; [|change (1 | Z.of_nat n); exists (Z.of_nat n); lia].
      intros off HO. apply PS, HP. change (size_chunk Mint8unsigned) with 1 in HO. lia. }
    destruct (Mem.valid_access_store ms Mint8unsigned b (Z.of_nat n) (Vint Int.zero) HW) as [mf ST].
    pose proof (exec_eis_zero_byte e le ms mf id b n HE ltac:(lia) ST) as ES.
    exists mf. split.
    { destruct n as [|n].
      - inversion EX; subst. exact ES.
      - change (Clight2.exec_stmt sha_ge e le m
          (Ssequence (eis_zero_array_prefix id (S n)) (eis_zero_byte_stmt id (S n))) E0 le mf Out_normal).
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ms) (le1 := le); eassumption. }
    split.
    { intros j HJ. destruct (Nat.eq_dec j n) as [->|Hne].
      - exact (Mem.load_store_same _ _ _ _ _ _ ST).
      - rewrite (Mem.load_store_other _ _ _ _ _ _ ST).
        + apply ZS; lia.
        + right. change (Z.of_nat j + 1 <= Z.of_nat n \/ Z.of_nat n + 1 <= Z.of_nat j). lia. }
    split.
    { intros ch bb off HO. rewrite (Mem.load_store_other _ _ _ _ _ _ ST).
      - apply LS; exact HO.
      - change (size_chunk Mint8unsigned) with 1. lia. }
    split.
    { intros bb off k p P. eapply Mem.perm_store_1; [exact ST|apply PS; exact P]. }
    intros bb V. eapply Mem.store_valid_block_1; [exact ST|apply VS; exact V].
Qed.
