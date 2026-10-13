From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_gej_public_prepare C.jet_secp_gej_public_lifecycle C.jet_secp_gej_public_entry C.jet_secp_gej_public_body C.jet_secp_gej_public_rest C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_literal_infinity.
Require Simplicity.Alg Simplicity.Translate.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_infinity Simplicity.Translate.encode.
Theorem eval_gej_infinity_literal_public v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    :
  write_frame_at m0 bd dbase bw outedge cursor N -> 768 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_gej_infinity)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_gej_infinity Alg.CoreFunSem tt)) /\
    lframe (fun b _ => ~ extA m0 bd bw bi b) m0 mf.
Proof.
  intros HOutput HCapacity HBase HAlign HFields.
  destruct (Mem.alloc m0 0 16) as [ma bl] eqn:HA.
  destruct (Mem.alloc ma 0 128) as [mb ba] eqn:HB.
  destruct (gej_prepare_public_locals v_env m0 ma bl ba mb bd dbase bs sbase bw outedge cursor N bi edge rc
    HA HB HOutput HCapacity HBase HAlign HFields)
    as [mc [HCopy [HFreeA [HFreeL [HLocalFields [HSeparate [HSep [HInv [HPrepFrame [HFreshA HFreshL]]]]]]]]]].
  destruct (exec_gej_public_rest_owned (secp_public_temps v_env bd dbase bs sbase)
    m0 bd dbase bw outedge cursor N bi rc mc ba bl
    eq_refl HOutput HCapacity HInv HFreeA HFreeL HSeparate HSep)
    as [mw [HRest [HFinal [HFinalFreeA [HFinalFreeL HRestFrame]]]]].
  destruct (gej_free_public_locals mw bl ba HSeparate HFinalFreeL HFinalFreeA)
    as [mf [HFree HFreeFrame]].
  assert (HFreeExt : eqext m0 bd bw bi mw mf).
  { eapply lframe_implies; [exact HFreeFrame|].
    intros b pos [_ HValid] _; split; intro HEqual; subst b; contradiction. }
  exists mf; split.
  - eapply eval_funcall_internal with (e := gej_public_env bl ba)
      (le1 := secp_public_temps v_env bd dbase bs sbase)
      (le2 := secp_public_temps v_env bd dbase bs sbase) (m1 := mb) (m2 := mw)
      (out := Out_return (Some (Vint Int.one, tint))).
    + eapply gej_infinity_public_entry; eassumption.
    + rewrite gej_public_body.
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
Print Assumptions eval_gej_infinity_literal_public.
