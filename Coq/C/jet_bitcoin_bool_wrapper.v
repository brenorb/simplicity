(** Lifecycle of the Bitcoin jets that only test a condition:
      [copy src; REST]  with REST returning a C boolean and writing nothing
    outside the local by-value copy of the source frame. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec C.jet_bitcoin_wrapper.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

Definition bool_val_int (b : bool) : val := Vint (if b then Int.one else Int.zero).

Theorem bitcoin_bool_wrapper f rest env m bd dbase bs sbase bytes (b : bool) :
  bitcoin_wrapper_shape f rest ->
  frame_base_valid sbase -> (8 | sbase) -> Mem.loadbytes m bs sbase 16 = Some bytes ->
  (forall ma mc bl,
     Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
     Mem.storebytes ma bl 0 bytes = Some mc ->
     exists le1 me,
       Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl)
         (bitcoin_wrapper_temps f env bd dbase bs sbase) mc rest E0 le1 me
         (Out_return (Some (Val.of_bool b, tint))) /\
       (forall chunk b' ofs, b' <> bl -> Mem.load chunk me b' ofs = Mem.load chunk mc b' ofs) /\
       (forall b' ofs kind p, Mem.perm mc b' ofs kind p -> Mem.perm me b' ofs kind p)) ->
  exists mf,
    Clight2.eval_funcall bitcoin_ge m (Internal f)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (bool_val_int b) /\
    (forall chunk b' ofs, Mem.valid_block m b' -> Mem.load chunk mf b' ofs = Mem.load chunk m b' ofs).
Proof.
  intros HShape HSbase HSAlign HB.
  assert (HVs : Mem.valid_block m bs).
  { eapply Mem.perm_valid_block. eapply (Mem.loadbytes_range_perm _ _ _ _ _ HB sbase); lia. }
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA. intros HMid.
  assert (HLs : bl <> bs).
  { intro Heq; subst bs. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HVs). }
  assert (HBa : Mem.loadbytes ma bs sbase 16 = Some bytes).
  { erewrite Mem.loadbytes_alloc_unchanged; eauto. }
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hlen.
  assert (PL : Mem.range_perm ma bl 0 16 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_alloc_2; eauto. }
  assert (PLW : Mem.range_perm ma bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlen. change (Mem.range_perm ma bl 0 16 Cur Writable).
    intros ofs Hrange. eapply Mem.perm_implies; [apply PL; exact Hrange|constructor]. }
  destruct (Mem.range_perm_storebytes ma bl 0 bytes PLW) as [mc SC].
  destruct (HMid ma mc bl eq_refl HBa SC) as (le1 & me & HExec & Hmemory & Hperm).
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. eapply Mem.perm_storebytes_1; [exact SC|]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  pose proof HShape as (HRet & HVars & HParams & HBody & HDisj).
  exists mf. split.
  - eapply eval_funcall_internal with (e := bitcoin_version_locals bl)
      (le1 := bitcoin_wrapper_temps f env bd dbase bs sbase) (le2 := le1)
      (m1 := ma) (m2 := me) (out := Out_return (Some (Val.of_bool b, tint))).
    + eapply bitcoin_wrapper_entry; eassumption.
    + rewrite HBody. unfold bitcoin_wrapper_body, bitcoin_copy_stmt.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
        (le1 := bitcoin_wrapper_temps f env bd dbase bs sbase).
      * eapply exec_bitcoin_version_copy; [exact HSbase|exact HSAlign|exact HLs| |exact HBa|exact SC].
        unfold bitcoin_wrapper_temps. rewrite PTree.gso by discriminate.
        apply PTree.gss.
      * exact HExec.
    + rewrite HRet. destruct b; cbn; split; try discriminate; reflexivity.
    + change (Mem.free_list me [(bl,0,16)] = Some mf). cbn. rewrite HF; reflexivity.
  - intros chunk b' ofs HV.
    assert (Hbl : b' <> bl).
    { intro Heq; subst b'. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
    erewrite Mem.load_free; [|exact HF|auto].
    rewrite Hmemory by assumption.
    erewrite Mem.load_storebytes_other; [|exact SC|auto].
    eapply Mem.load_alloc_unchanged; eauto.
Qed.
