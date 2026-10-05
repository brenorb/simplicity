(** Reusable memory effect of an initialized word copied as bytes.
    This is support for the original libc call, not a proof of an added C
    helper or of the external library implementation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Import Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma copy_word_storebytes_effect m m' bi src bw dst v bytes :
  Mem.load Mint64 m bi src = Some (Vlong v) ->
  Mem.loadbytes m bi src 8 = Some bytes ->
  Mem.storebytes m bw dst bytes = Some m' ->
  (align_chunk Mint64 | dst) ->
  Mem.load Mint64 m' bw dst = Some (Vlong v) /\
  (forall chunk b ofs, b <> bw \/ ofs + size_chunk chunk <= dst \/ dst + 8 <= ofs ->
    Mem.load chunk m' b ofs = Mem.load chunk m b ofs) /\
  (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm m' b ofs kind p) /\
  (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HL HB HS HA.
  assert (Hlen : length bytes = 8%nat) by (apply (Mem.loadbytes_length _ _ _ _ _ HB)).
  destruct (Mem.load_loadbytes _ _ _ _ _ HL) as [original [HB0 Hdec]].
  change (size_chunk Mint64) with 8 in HB0.
  rewrite HB in HB0. inversion HB0; subst original.
  assert (HL' : Mem.loadbytes m' bw dst 8 = Some bytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HS) as Hsame.
    rewrite Hlen in Hsame. exact Hsame. }
  split.
  - rewrite (Mem.loadbytes_load Mint64 m' bw dst bytes HL' HA).
    rewrite <- Hdec. reflexivity.
  - split.
    + intros chunk b ofs Hout. eapply Mem.load_storebytes_other; [exact HS|].
      rewrite Hlen. change (Z.of_nat 8) with 8.
      destruct Hout as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia].
    + split.
      * intros b ofs kind p HP. eapply Mem.perm_storebytes_1; eauto.
      * intros b HV. eapply Mem.storebytes_valid_block_1; eauto.
Qed.
