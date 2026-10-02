(** Actual local-block order and initial-permission-derived cleanup for the
    four-local DivMod128_64 function. No free execution is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps Memory.
Require Import C.jet_exec C.jet_divmod128_entry.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma divmod128_blocks_of_env bl bqh bql br :
  blocks_of_env ge0 (divmod128_env bl bqh bql br) =
    [(bl,0,16); (bqh,0,8); (bql,0,8); (br,0,8)].
Proof. reflexivity. Qed.

Theorem free_divmod128_locals m bl bqh bql br :
  bl <> bqh -> bl <> bql -> bl <> br -> bqh <> bql -> bqh <> br -> bql <> br ->
  Mem.range_perm m bl 0 16 Cur Freeable -> Mem.range_perm m bqh 0 8 Cur Freeable ->
  Mem.range_perm m bql 0 8 Cur Freeable -> Mem.range_perm m br 0 8 Cur Freeable ->
  exists mf,
    Mem.free_list m (blocks_of_env ge0 (divmod128_env bl bqh bql br)) = Some mf /\
    (forall chunk bb addr, bb <> bl -> bb <> bqh -> bb <> bql -> bb <> br ->
      Mem.load chunk mf bb addr = Mem.load chunk m bb addr) /\
    (forall bb addr kind p, bb <> bl -> bb <> bqh -> bb <> bql -> bb <> br ->
      Mem.perm m bb addr kind p -> Mem.perm mf bb addr kind p) /\
    Mem.nextblock mf = Mem.nextblock m.
Proof.
  intros HH HL HR HHL HHR HLR PL PH PQ PR.
  destruct (Mem.range_perm_free m bl 0 16 PL) as [m1 HF1].
  assert (PH1 : Mem.range_perm m1 bqh 0 8 Cur Freeable).
  { intros addr Haddr. eapply Mem.perm_free_1; [exact HF1|left; congruence|apply PH; exact Haddr]. }
  assert (PQ1 : Mem.range_perm m1 bql 0 8 Cur Freeable).
  { intros addr Haddr. eapply Mem.perm_free_1; [exact HF1|left; congruence|apply PQ; exact Haddr]. }
  assert (PR1 : Mem.range_perm m1 br 0 8 Cur Freeable).
  { intros addr Haddr. eapply Mem.perm_free_1; [exact HF1|left; congruence|apply PR; exact Haddr]. }
  destruct (Mem.range_perm_free m1 bqh 0 8 PH1) as [m2 HF2].
  assert (PQ2 : Mem.range_perm m2 bql 0 8 Cur Freeable).
  { intros addr Haddr. eapply Mem.perm_free_1; [exact HF2|left; congruence|apply PQ1; exact Haddr]. }
  assert (PR2 : Mem.range_perm m2 br 0 8 Cur Freeable).
  { intros addr Haddr. eapply Mem.perm_free_1; [exact HF2|left; congruence|apply PR1; exact Haddr]. }
  destruct (Mem.range_perm_free m2 bql 0 8 PQ2) as [m3 HF3].
  assert (PR3 : Mem.range_perm m3 br 0 8 Cur Freeable).
  { intros addr Haddr. eapply Mem.perm_free_1; [exact HF3|left; congruence|apply PR2; exact Haddr]. }
  destruct (Mem.range_perm_free m3 br 0 8 PR3) as [mf HF4].
  exists mf. split.
  - rewrite divmod128_blocks_of_env. cbn [Mem.free_list].
    rewrite HF1, HF2, HF3, HF4. reflexivity.
  - split.
    + intros chunk bb addr HB1 HB2 HB3 HB4.
      erewrite Mem.load_free; [|exact HF4|auto].
      erewrite Mem.load_free; [|exact HF3|auto].
      erewrite Mem.load_free; [|exact HF2|auto].
      erewrite Mem.load_free; [reflexivity|exact HF1|auto].
    + split.
      * intros bb addr kind p HB1 HB2 HB3 HB4 HP.
        eapply Mem.perm_free_1; [exact HF4|auto|].
        eapply Mem.perm_free_1; [exact HF3|auto|].
        eapply Mem.perm_free_1; [exact HF2|auto|].
        eapply Mem.perm_free_1; [exact HF1|auto|exact HP].
      * rewrite (Mem.nextblock_free _ _ _ _ _ HF4), (Mem.nextblock_free _ _ _ _ _ HF3),
          (Mem.nextblock_free _ _ _ _ _ HF2), (Mem.nextblock_free _ _ _ _ _ HF1). reflexivity.
Qed.
