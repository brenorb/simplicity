(** Initial-only execution and memory contracts for constant uint32_t arrays.
    The statement template retains the generated unsigned-long-to-uint cast.
    Its first concrete consumer is the actual sha256_iv C helper. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition uint32_init_value z := Int64.loword (Int64.repr z).
Definition uint32_init_stmt i z :=
  Sassign (Ederef (Ebinop Oadd (Etempvar _iv (tptr tuint))
    (Econst_int (Int.repr (Z.of_nat i)) tint) (tptr tuint)) tuint)
    (Econst_long (Int64.repr z) tulong).
Fixpoint uint32_init_stmts i zs :=
  match zs with
  | [] => Sskip
  | z :: rest => match rest with
    | [] => uint32_init_stmt i z
    | _ => Ssequence (uint32_init_stmt i z) (uint32_init_stmts (S i) rest)
    end
  end.
Definition uint32_array_at m b base (xs : list int) :=
  forall i x, nth_error xs i = Some x ->
    Mem.load Mint32 m b (base + 4 * Z.of_nat i) = Some (Vint x).

Lemma exec_uint32_init_store m mf le b base i z :
  le!_iv = Some (Vptr b (Ptrofs.repr base)) ->
  0 <= base -> base + 4 * Z.of_nat i <= Ptrofs.max_unsigned ->
  Z.of_nat i <= 2147483647 ->
  Mem.store Mint32 m b (base + 4 * Z.of_nat i) (Vint (uint32_init_value z)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m (uint32_init_stmt i z) E0 le mf Out_normal.
Proof.
  intros HL HB HM HI HS.
  assert (Hsigned : Int.signed (Int.repr (Z.of_nat i)) = Z.of_nat i).
  { apply Int.signed_repr. change (-2147483648 <= Z.of_nat i <= 2147483647); lia. }
  assert (Haddr : Ptrofs.add (Ptrofs.repr base)
      (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr (Z.of_nat i)))) =
      Ptrofs.repr (base + 4 * Z.of_nat i)).
  { unfold Ptrofs.of_ints. rewrite Hsigned.
    unfold Ptrofs.mul, Ptrofs.add.
    change (Ptrofs.unsigned (Ptrofs.repr 4)) with 4.
    rewrite (Ptrofs.unsigned_repr base) by lia.
    rewrite (Ptrofs.unsigned_repr (Z.of_nat i)) by lia.
    rewrite (Ptrofs.unsigned_repr (4 * Z.of_nat i)) by lia. reflexivity. }
  unfold uint32_init_stmt.
  eapply exec_Sassign_value with (v := Vint (uint32_init_value z))
    (v2 := Vlong (Int64.repr z)) (b := b) (ofs := Ptrofs.repr (base + 4 * Z.of_nat i)).
  - eapply eval_Ederef. eapply eval_Ebinop with
      (v1 := Vptr b (Ptrofs.repr base)) (v2 := Vint (Int.repr (Z.of_nat i))).
    + apply eval_Etempvar; exact HL.
    + apply eval_Econst_int.
    + change (Some (Vptr b (Ptrofs.add (Ptrofs.repr base)
        (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr (Z.of_nat i)))))) =
        Some (Vptr b (Ptrofs.repr (base + 4 * Z.of_nat i)))). rewrite Haddr; reflexivity.
  - apply eval_Econst_long.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint32); [reflexivity|].
    unfold Mem.storev. rewrite Ptrofs.unsigned_repr by lia. exact HS.
Qed.

Theorem exec_uint32_init_array m le b base i zs :
  le!_iv = Some (Vptr b (Ptrofs.repr base)) ->
  0 <= base -> base + 4 * (Z.of_nat i + Z.of_nat (length zs)) <= Ptrofs.max_unsigned ->
  Z.of_nat i + Z.of_nat (length zs) <= 2147483647 -> (4 | base) ->
  Mem.range_perm m b (base + 4 * Z.of_nat i)
    (base + 4 * (Z.of_nat i + Z.of_nat (length zs))) Cur Writable ->
  exists mf,
    Clight2.exec_stmt ge0 empty_env le m (uint32_init_stmts i zs) E0 le mf Out_normal /\
    uint32_array_at mf b (base + 4 * Z.of_nat i) (map uint32_init_value zs) /\
    (forall chunk bb ofs,
      bb <> b \/ ofs + size_chunk chunk <= base + 4 * Z.of_nat i \/
        base + 4 * (Z.of_nat i + Z.of_nat (length zs)) <= ofs ->
      Mem.load chunk mf bb ofs = Mem.load chunk m bb ofs) /\
    (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mf bb ofs kind p) /\
    (forall bb, Mem.valid_block m bb -> Mem.valid_block mf bb).
Proof.
  revert m i. induction zs as [|z zs IH]; intros m i HL HB HM HI HA HR.
  - exists m. split; [apply exec_Sskip|]. split.
    + intros j x Hj. destruct j; discriminate.
    + split; [intros; reflexivity|]. split; auto.
  - assert (HW : Mem.valid_access m Mint32 b (base + 4 * Z.of_nat i) Writable).
    { split.
      - intros ofs HO. apply HR. cbn [length] in HM, HI |- *. change (size_chunk Mint32) with 4 in HO. lia.
      - change (4 | base + 4 * Z.of_nat i). destruct HA as [k HK]. exists (k + Z.of_nat i). lia. }
    destruct (Mem.valid_access_store m Mint32 b (base + 4 * Z.of_nat i)
      (Vint (uint32_init_value z)) HW) as [ms HS].
    assert (HStore : Clight2.exec_stmt ge0 empty_env le m (uint32_init_stmt i z) E0 le ms Out_normal).
    { eapply exec_uint32_init_store; eauto; cbn [length] in HM, HI; lia. }
    assert (HFirst : Mem.load Mint32 ms b (base + 4 * Z.of_nat i) =
      Some (Vint (uint32_init_value z))).
    { exact (Mem.load_store_same _ _ _ _ _ _ HS). }
    assert (HRNext : Mem.range_perm ms b (base + 4 * Z.of_nat (S i))
      (base + 4 * (Z.of_nat (S i) + Z.of_nat (length zs))) Cur Writable).
    { intros ofs HO. eapply Mem.perm_store_1; [exact HS|]. apply HR.
      cbn [length]. lia. }
    destruct (IH ms (S i) HL HB ltac:(cbn [length] in HM; lia)
      ltac:(cbn [length] in HI; lia) HA HRNext)
      as [mf [HRest [HArray [HLoads [HPerm HValid]]]]].
    assert (HFields : uint32_array_at mf b (base + 4 * Z.of_nat i)
      (map uint32_init_value (z :: zs))).
    { intros [|j] x Hj.
      - cbn in Hj. injection Hj as <-.
        replace (base + 4 * Z.of_nat i + 4 * Z.of_nat 0) with
          (base + 4 * Z.of_nat i) by lia.
        rewrite HLoads; [exact HFirst|right; left]. change (size_chunk Mint32) with 4. lia.
      - cbn [map nth_error] in Hj.
        replace (base + 4 * Z.of_nat i + 4 * Z.of_nat (S j)) with
          (base + 4 * Z.of_nat (S i) + 4 * Z.of_nat j) by lia.
        exact (HArray j x Hj). }
    assert (HMemory : forall chunk bb ofs,
      bb <> b \/ ofs + size_chunk chunk <= base + 4 * Z.of_nat i \/
        base + 4 * (Z.of_nat i + Z.of_nat (length (z :: zs))) <= ofs ->
      Mem.load chunk mf bb ofs = Mem.load chunk m bb ofs).
    { intros chunk bb ofs HO. rewrite HLoads.
      - eapply Mem.load_store_other; [exact HS|].
        change (bb <> b \/ ofs + size_chunk chunk <= base + 4 * Z.of_nat i \/
          base + 4 * Z.of_nat i + 4 <= ofs). cbn [length] in HO. lia.
      - cbn [length] in HO. lia. }
    exists mf. split.
    + destruct zs as [|y zs].
      * change (Clight2.exec_stmt ge0 empty_env le ms Sskip E0 le mf Out_normal) in HRest.
        inversion HRest; subst. exact HStore.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ms) (le1 := le); eauto.
    + split; [exact HFields|]. split; [exact HMemory|]. split.
      * intros bb ofs kind p HP. apply HPerm. eapply Mem.perm_store_1; eauto.
      * intros bb HV. apply HValid. eapply Mem.store_valid_block_1; eauto.
Qed.
