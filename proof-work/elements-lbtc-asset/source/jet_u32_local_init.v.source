(** Direct uint32 constant stores into a local array, with a continuation.
    The address lemma is discharged from the local C expression by consumers;
    there is no helper-execution or desired-output premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Memory Events.
From compcert Require Import ClightBigstep.
Require Import C.jet_exec C.jet_uint32_array_init.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition u32_local_lhs (arr : expr) (i : nat) :=
  Ederef (Ebinop Oadd arr (Econst_int (Int.repr (Z.of_nat i)) tint) (tptr tuint)) tuint.

Fixpoint u32_local_prefix (arr : expr) (i : nat) (xs : list int) (tail : statement) : statement :=
  match xs with
  | [] => tail
  | x :: rest => Ssequence (Sassign (u32_local_lhs arr i) (Econst_int x tuint))
                           (u32_local_prefix arr (S i) rest tail)
  end.

Theorem exec_u32_local_prefix (ge : Clight.genv) e le m arr b base i xs :
  (forall m' j, (j < i + length xs)%nat ->
    eval_lvalue ge e le m' (u32_local_lhs arr j) b (Ptrofs.repr (base + 4 * Z.of_nat j)) Full) ->
  0 <= base -> base + 4 * (Z.of_nat i + Z.of_nat (length xs)) <= Ptrofs.max_unsigned ->
  (4 | base) ->
  Mem.range_perm m b (base + 4 * Z.of_nat i)
    (base + 4 * (Z.of_nat i + Z.of_nat (length xs))) Cur Writable ->
  exists mi,
    uint32_array_at mi b (base + 4 * Z.of_nat i) xs /\
    (forall chunk bb ofs, bb <> b \/ ofs + size_chunk chunk <= base + 4 * Z.of_nat i \/
       base + 4 * (Z.of_nat i + Z.of_nat (length xs)) <= ofs ->
       Mem.load chunk mi bb ofs = Mem.load chunk m bb ofs) /\
    (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mi bb ofs kind p) /\
    (forall bb, Mem.valid_block m bb -> Mem.valid_block mi bb) /\
    (forall tail le' mf out, Clight2.exec_stmt ge e le mi tail E0 le' mf out ->
       Clight2.exec_stmt ge e le m (u32_local_prefix arr i xs tail) E0 le' mf out).
Proof.
  revert m i. induction xs as [|x xs IH]; intros m i Haddr HB HM HA HR.
  - exists m. split; [intros j v H; destruct j; discriminate|].
    split; [intros; reflexivity|]. split; [auto|]. split; [auto|]. intros; exact H.
  - assert (HW : Mem.valid_access m Mint32 b (base + 4 * Z.of_nat i) Writable).
    { split.
      - intros ofs Ho. apply HR. change (size_chunk Mint32) with 4 in Ho. cbn [length]. lia.
      - change (4 | base + 4 * Z.of_nat i). destruct HA as [k HK]. exists (k + Z.of_nat i). lia. }
    destruct (Mem.valid_access_store m Mint32 b (base + 4 * Z.of_nat i) (Vint x) HW) as [ms HS].
    assert (HStore : Clight2.exec_stmt ge e le m
      (Sassign (u32_local_lhs arr i) (Econst_int x tuint)) E0 le ms Out_normal).
    { eapply exec_Sassign_value with (v := Vint x) (v2 := Vint x)
        (b := b) (ofs := Ptrofs.repr (base + 4 * Z.of_nat i)).
      - apply Haddr. cbn [length]. lia.
      - constructor.
      - reflexivity.
      - apply assign_loc_value with (chunk := Mint32); [reflexivity|].
        unfold Mem.storev. rewrite Ptrofs.unsigned_repr by (cbn [length] in HM; lia). exact HS. }
    assert (HFirst : Mem.load Mint32 ms b (base + 4 * Z.of_nat i) = Some (Vint x))
      by exact (Mem.load_store_same _ _ _ _ _ _ HS).
    assert (HRNext : Mem.range_perm ms b (base + 4 * Z.of_nat (S i))
      (base + 4 * (Z.of_nat (S i) + Z.of_nat (length xs))) Cur Writable).
    { intros ofs Ho. eapply Mem.perm_store_1; [exact HS|]. apply HR. cbn [length]. lia. }
    destruct (IH ms (S i) ltac:(intros; apply Haddr; cbn [length]; lia) HB
      ltac:(cbn [length] in HM; lia) HA HRNext)
      as (mi & HArray & HLoads & HPerm & HValid & HRest).
    exists mi. split.
    { intros [|j] v Hj.
      - cbn in Hj. injection Hj as <-. replace (base + 4 * Z.of_nat i + 4 * Z.of_nat 0)
          with (base + 4 * Z.of_nat i) by lia.
        rewrite HLoads; [exact HFirst|right; left]. change (size_chunk Mint32) with 4. lia.
      - cbn in Hj. replace (base + 4 * Z.of_nat i + 4 * Z.of_nat (S j)) with
          (base + 4 * Z.of_nat (S i) + 4 * Z.of_nat j) by lia. exact (HArray j v Hj). }
    split.
    { intros chunk bb ofs Ho. rewrite HLoads.
      - eapply Mem.load_store_other; [exact HS|].
        change (bb <> b \/ ofs + size_chunk chunk <= base + 4 * Z.of_nat i \/
          base + 4 * Z.of_nat i + 4 <= ofs). cbn [length] in Ho. lia.
      - cbn [length] in Ho. lia. }
    split; [intros; apply HPerm; eapply Mem.perm_store_1; eauto|].
    split; [intros; apply HValid; eapply Mem.store_valid_block_1; eauto|].
    intros tail le' mf out HT. cbn [u32_local_prefix].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ms) (le1 := le);
      [exact HStore|apply HRest; exact HT].
Qed.
