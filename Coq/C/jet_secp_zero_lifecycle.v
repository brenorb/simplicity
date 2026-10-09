(** Complete execution and cleanup of the unchanged public fe_is_zero jet. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_exec C.jet_readBit_layout C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_encoding C.jet_frame_inv.
Require Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg Simplicity.Translate.
Require Import C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_public_lifecycle.
Require Import C.jet_secp_predicate_entry C.jet_secp_odd_body C.jet_secp_zero_body C.jet_secp_zero_entry C.jet_secp_zero_rest C.jet_secp_canonical_zero.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_is_zero Simplicity.Translate.encode.
Theorem eval_secp_fe_zero_canonical v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word.Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 1 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_fe_is_zero)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (Simplicity.Translate.encode (@canonical_fe_is_zero Alg.CoreFunSem value)) /\
    lframe (fun b _ => ~ extA m0 bd bw bi b) m0 mf.
Proof.
  intros HOutput HCapacity HBase HAlign HFields HInput HCursor HMax.
  destruct (Mem.alloc m0 0 16) as [ma bl] eqn:HA.
  destruct (Mem.alloc ma 0 40) as [mb ba] eqn:HB.
  destruct (secp_prepare_predicate_locals (secp_odd_temps v_env bd dbase bs sbase) m0 ma bl ba mb bd dbase bs sbase bw outedge cursor N bi edge rc value
    HA HB HOutput HCapacity HBase HAlign HFields eq_refl)
    as [mc [HCopy [HFreeA [HFreeL [HLocalFields [HSeparate [HSep [HInv [HPrepFrame [HFreshA HFreshL]]]]]]]]]].
  destruct (exec_secp_fe_zero_rest_canonical (secp_odd_temps v_env bd dbase bs sbase)
    m0 bd dbase bw outedge cursor N bi edge rc value mc ba bl
    eq_refl HOutput HInput HCursor HMax HFreeA HFreeL HLocalFields HSeparate HSep HInv)
    as [mw [HRest [HFinal [HFinalFreeA [HFinalFreeL HRestFrame]]]]].
  destruct (secp_free_public_locals mw bl ba HSeparate HFinalFreeL HFinalFreeA)
    as [mf [HFree HFreeFrame]].
  assert (HFreeExt : eqext m0 bd bw bi mw mf).
  { eapply lframe_implies; [exact HFreeFrame|].
    intros b pos [_ HValid] _; split; intro HEqual; subst b; contradiction. }
  exists mf; split.
  - eapply eval_funcall_internal with (e := secp_public_env bl ba)
      (le1 := secp_odd_temps v_env bd dbase bs sbase)
      (le2 := PTree.set jets_secp._t'1
        (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem value))))
        (secp_odd_temps v_env bd dbase bs sbase)) (m1 := mb) (m2 := mw)
      (out := Out_return (Some (Vint Int.one, tint))).
    + eapply secp_fe_zero_entry; eassumption.
    + rewrite secp_fe_zero_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
        (le1 := secp_odd_temps v_env bd dbase bs sbase); eassumption.
    + cbn; split; [discriminate|reflexivity].
    + exact HFree.
  - split.
    + eapply finv_stable; [exact HOutput|exact HFinal|exact HFreeExt].
    + assert (HOutside : lframe (fun b _ => Mem.valid_block m0 b /\ ~ extA m0 bd bw bi b) m0 mf).
      { eapply lframe_trans.
        - eapply lframe_implies; [exact HPrepFrame|].
          intros b pos [HValid _] _; split; intro HEqual; subst b; contradiction.
        - eapply lframe_trans.
          + eapply lframe_implies; [exact HRestFrame|].
            intros b pos [HValid HExt] _; unfold secp_locals_outside.
            split; [intro HEqual; subst b; contradiction|]; split; [intro HEqual; subst b; contradiction|exact HExt].
          + eapply lframe_implies; [exact HFreeFrame|].
            intros b pos [HValid _] _; split; intro HEqual; subst b; contradiction. }
      eapply lframe_implies; [exact HOutside|]; intros b pos HExt HValid; split; assumption.
Qed.
