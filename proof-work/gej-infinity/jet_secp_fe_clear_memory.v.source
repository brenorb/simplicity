(** Derive the real clear-loop stores from initial field storage.
    No execution or computed output is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Values.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_sx_mem.
Require Import C.jet_secp_fe_clear_loop.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma construct_fe_clear_stores n : forall m b base i,
  0 <= base -> (8 | base) -> base + 40 <= Ptrofs.max_unsigned ->
  0 <= i -> i + Z.of_nat n <= 5 ->
  Mem.range_perm m b base (base + 40) Cur Writable ->
  exists mf,
    fe_clear_stores n b base i m mf /\
    (forall j, (j < n)%nat ->
      Mem.load Mint64 mf b (base + 8 * (i + Z.of_nat j)) = Some (Vlong Int64.zero)) /\
    (forall chunk b' ofs,
      b' <> b \/ ofs + size_chunk chunk <= base + 8 * i \/
      base + 8 * (i + Z.of_nat n) <= ofs ->
      Mem.load chunk mf b' ofs = Mem.load chunk m b' ofs) /\
    (forall b' ofs k p, Mem.perm mf b' ofs k p <-> Mem.perm m b' ofs k p) /\
    (forall b', Mem.valid_block m b' -> Mem.valid_block mf b').
Proof.
  induction n as [|n IH]; intros m b base i HB HA HM Hi HN HP.
  - exists m; split; [reflexivity|].
    split; [intros j Hj; lia|]. split; [reflexivity|].
    split; [intros; reflexivity|intros; assumption].
  - assert (HAccess : Mem.valid_access m Mint64 b (base + 8 * i) Writable).
    { split.
      - intros ofs HOfs. apply HP. change (size_chunk Mint64) with 8 in HOfs.
        rewrite Nat2Z.inj_succ in HN; pose proof (Nat2Z.is_nonneg n); lia.
      - change (8 | base + 8 * i). destruct HA as [k HK]. exists (k + i); lia. }
    destruct (Mem.valid_access_store m Mint64 b (base + 8 * i) (Vlong Int64.zero) HAccess)
      as [mi HS].
    assert (HPI : Mem.range_perm mi b base (base + 40) Cur Writable).
    { intros ofs HOfs. eapply Mem.perm_store_1; [exact HS|apply HP; exact HOfs]. }
    destruct (IH mi b base (i + 1) HB HA HM ltac:(lia)
      ltac:(rewrite Nat2Z.inj_succ in HN; lia) HPI)
      as [mf [HR [HL [HF [HPerm HV]]]]].
    exists mf; split.
    + exists mi; split; assumption.
    + split.
      * intros [|j] Hj.
        -- replace (base + 8 * (i + Z.of_nat 0)) with (base + 8 * i) by lia.
           rewrite HF by (right; left; change (size_chunk Mint64) with 8; lia).
           pose proof (Mem.load_store_same _ _ _ _ _ _ HS) as HE.
           exact HE.
        -- replace (base + 8 * (i + Z.of_nat (S j))) with
             (base + 8 * ((i + 1) + Z.of_nat j)) by (rewrite Nat2Z.inj_succ; lia).
           apply HL; lia.
      * split.
        -- intros chunk b' ofs HOther.
           rewrite HF by (destruct HOther as [HOther|[HOther|HOther]];
             [left; exact HOther|right; left; lia|right; right;
              rewrite Nat2Z.inj_succ in HOther; lia]).
           eapply Mem.load_store_other; [exact HS|].
           destruct HOther as [HOther|[HOther|HOther]];
             [left; exact HOther|right; left; exact HOther|right; right].
           change (size_chunk Mint64) with 8.
           rewrite Nat2Z.inj_succ in HOther; pose proof (Nat2Z.is_nonneg n); lia.
        -- split.
           ++ intros b' ofs k p. rewrite HPerm; split.
              ** eapply Mem.perm_store_2; exact HS.
              ** eapply Mem.perm_store_1; exact HS.
           ++ intros b' HB'. apply HV. eapply Mem.store_valid_block_1; eauto.
Qed.

Theorem eval_fe_clear_owned m b base :
  0 <= base -> (8 | base) -> base + 40 <= Ptrofs.max_unsigned ->
  Mem.range_perm m b base (base + 40) Cur Writable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_clear)
      [Vptr b (Ptrofs.repr base)] E0 mf Vundef /\
    fe_at mf b base (repeat Int64.zero 5) /\
    (forall chunk b' ofs,
      b' <> b \/ ofs + size_chunk chunk <= base \/ base + 40 <= ofs ->
      Mem.load chunk mf b' ofs = Mem.load chunk m b' ofs) /\
    (forall b' ofs k p, Mem.perm mf b' ofs k p <-> Mem.perm m b' ofs k p) /\
    (forall b', Mem.valid_block m b' -> Mem.valid_block mf b').
Proof.
  intros HB HA HM HP.
  destruct (construct_fe_clear_stores 5 m b base 0 HB HA HM ltac:(lia) ltac:(lia) HP)
    as [mf [HR [HL [HF [HPerm HV]]]]].
  exists mf; split; [apply eval_fe_clear_from_stores; assumption|].
  split.
  - split; [exact HB|]. split; [exact HA|]. split; [exact HM|]. split.
    + intros ofs HOfs. apply (proj2 (HPerm b ofs Cur Writable)); apply HP; exact HOfs.
    + intros j x HJ. assert (HIndex : (j < 5)%nat).
      { pose proof (proj1 (nth_error_Some (repeat Int64.zero 5) j)
          ltac:(rewrite HJ; discriminate)) as HH.
        rewrite repeat_length in HH; exact HH. }
      assert (HX : x = Int64.zero).
      { rewrite (nth_error_repeat Int64.zero (m := 5%nat) (n := j) HIndex) in HJ; congruence. }
      subst x. replace (base + 8 * Z.of_nat j) with (base + 8 * (0 + Z.of_nat j)) by lia.
      apply HL; exact HIndex.
  - replace (base + 8 * 0) with base in HF by lia.
    replace (base + 8 * (0 + Z.of_nat 5)) with (base + 40) in HF by lia.
    split; [exact HF|]. split; assumption.
Qed.
Print Assumptions eval_fe_clear_owned.
