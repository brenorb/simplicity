(** Self-copy preserves all observable memory, not necessarily the memory
    record: finite-map storage may gain explicit entries equal to defaults. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps AST Memory.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Transparent Mem.loadbytes.

Lemma self_copy_setN_getN n p (c : ZMap.t memval) q :
  ZMap.get q (Mem.setN (Mem.getN n p c) p c) = ZMap.get q c.
Proof.
  revert p c q; induction n as [|n IH]; intros p c q.
  - reflexivity.
  - cbn [Mem.getN Mem.setN].
    assert (HNext : Mem.getN n (p+1) c =
      Mem.getN n (p+1) (ZMap.set p (ZMap.get p c) c)).
    { apply Mem.getN_exten. intros i HI.
      rewrite ZMap.gso by lia. reflexivity. }
    rewrite HNext, IH.
    rewrite ZMap.gsspec. destruct (ZIndexed.eq q p); subst; reflexivity.
Qed.

Lemma self_copy_storebytes_unchanged m b ofs n bytes mf :
  Mem.loadbytes m b ofs n = Some bytes ->
  Mem.storebytes m b ofs bytes = Some mf ->
  Mem.unchanged_on (fun _ _ => True) m mf.
Proof.
  intros HL HS.
  assert (HBytes : bytes = Mem.getN (Z.to_nat n) ofs (PMap.get b (Mem.mem_contents m))).
  { unfold Mem.loadbytes in HL.
    destruct (Mem.range_perm_dec m b ofs (ofs+n) Cur Readable);
      inversion HL; reflexivity. }
  constructor.
  - rewrite (Mem.nextblock_storebytes _ _ _ _ _ HS); apply Ple_refl.
  - intros b0 o k p _ _. split; intro HP.
    + eapply Mem.perm_storebytes_1; eassumption.
    + eapply Mem.perm_storebytes_2; eassumption.
  - intros b0 o _ _.
    erewrite Mem.storebytes_mem_contents by exact HS.
    rewrite PMap.gsspec; destruct (peq b0 b); [subst b0|reflexivity].
    rewrite HBytes. apply self_copy_setN_getN.
Qed.
Print Assumptions self_copy_storebytes_unchanged.
