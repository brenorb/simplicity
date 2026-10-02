(** Complete actual verify call: copy the by-value source, read one bit,
    return that Boolean and free the source copy. No output writer occurs. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_readBit_layout C.jet_writeBit C.jet_increment8_exec C.jet_complement1_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma verify_body : fn_body f_simplicity_verify =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr))
      (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence bit_jet_read (Sreturn (Some (Etempvar _t'1 tbool)))).
Proof. reflexivity. Qed.

Lemma eval_verify_composes env m ma mc mr mf bl bd dbase bs sbase bytes bit :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr (Vint (bit_int bit)) ->
  Mem.free mr bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_verify)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint (bit_int bit)).
Proof.
  intros HB HS HD HA Hbytes SC Hread HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env f_simplicity_verify bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := PTree.set _t'1 (Vint (bit_int bit))
      (le_arith8_layout env f_simplicity_verify bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase)))
    (m1 := ma) (m2 := mr) (out := Out_return (Some (Vint (bit_int bit), tbool))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_t'1]).
    intros id1 id2 H1 H2 Heq. cbn in H1, H2. subst id2.
    destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|H2];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite verify_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
      * apply call_bit_jet_read. exact Hread.
      * apply exec_Sreturn_some. eapply eval_Etempvar; reflexivity.
  - cbn. split; [discriminate|]. unfold bit_int. destruct bit; reflexivity.
  - change (Mem.free_list mr [(bl, 0, 16)] = Some mf). cbn; rewrite HF; reflexivity.
Qed.
