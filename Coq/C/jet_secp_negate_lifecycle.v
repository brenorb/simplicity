(** Complete original negation function entry, source copy and local release. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout C.jet_encoding C.jet_frame_inv.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Translate.
Require Import C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_public_lifecycle.
Require Import C.jet_secp_canonical_negate C.jet_secp_negate_body C.jet_secp_negate_rest.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_negate Simplicity.Translate.encode.
Lemma secp_fe_negate_entry v_env m ma mb bl ba bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 40 = (mb, ba) ->
  function_entry2 secp_ge f_simplicity_fe_negate
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] m
    (secp_public_env bl ba) (secp_public_temps v_env bd dbase bs sbase) mb.
Proof.
  intros HA HB; constructor.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy; cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in Hxy; discriminate|congruence].
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma, bl)); exact HA.
    + eapply alloc_variables_cons with (m1 := mb) (b1 := ba).
      * change (Mem.alloc ma 0 40 = (mb, ba)); exact HB.
      * constructor.
  - reflexivity.
Qed.
Theorem eval_secp_fe_negate_canonical v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word.Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 256 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_fe_negate)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (Simplicity.Translate.encode (@canonical_fe_negate Alg.CoreFunSem value)) /\
    lframe (fun b _ => ~ extA m0 bd bw bi b) m0 mf.
Proof.
  intros HOutput HCapacity HBase HAlign HFields HInput HCursor HMax.
  destruct (Mem.alloc m0 0 16) as [ma bl] eqn:HA.
  destruct (Mem.alloc ma 0 40) as [mb ba] eqn:HB.
  destruct (secp_prepare_public_locals v_env m0 ma bl ba mb bd dbase bs sbase bw outedge cursor N bi edge rc value
    HA HB HOutput HCapacity HBase HAlign HFields)
    as [mc [HCopy [HFreeA [HFreeL [HLocalFields [HSeparate [HSep [HInv [HPrepFrame [HFreshA HFreshL]]]]]]]]]].
  destruct (exec_secp_fe_negate_rest_canonical (secp_public_temps v_env bd dbase bs sbase)
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
      (le1 := secp_public_temps v_env bd dbase bs sbase)
      (le2 := secp_public_temps v_env bd dbase bs sbase) (m1 := mb) (m2 := mw)
      (out := Out_return (Some (Vint Int.one, tint))).
    + eapply secp_fe_negate_entry; eassumption.
    + rewrite secp_fe_negate_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
        (le1 := secp_public_temps v_env bd dbase bs sbase); eassumption.
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

Print Assumptions eval_secp_fe_negate_canonical.
