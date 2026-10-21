(** Entire unchanged public projective on-curve jet: reader, helper, writer,
    by-value source copy, actual entry, return conversion and local frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jet_exec C.jet_readBit_layout C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_public_body C.jet_secp_public_copy C.jet_secp_wrapper_run.
Require Import C.jet_secp_owned_public_lifecycle C.jet_secp_owned_public_prepare.
Require Import C.jet_secp_ge_negate_boundary C.jet_secp_curve_literal.
Require Import C.jet_secp_gej_public_entry C.jet_secp_gej_curve_public_statements C.jet_secp_gej_curve_public_rest.
Import Clightdefs ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_is_on_curve Simplicity.Translate.encode.

Theorem eval_gej_curve_literal_public v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (x y z : tySem (Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 1<=N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits z)) ->
  0<=rc -> rc+768<=Int64.max_unsigned ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_gej_is_on_curve)
      [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_gej_is_on_curve Alg.CoreFunSem ((x,y),z))) /\
    lframe (fun b _ => ~ extA m0 bd bw bi b) m0 mf.
Proof.
  intros HO HN HBase HAlign HFields HX HY HZ Hrc HM.
  destruct (Mem.alloc m0 0 16) as [ma bl] eqn:HA.
  destruct (Mem.alloc ma 0 128) as [mb ba] eqn:HB.
  set (le := gej_curve_public_temps v_env bd dbase bs sbase).
  destruct (owned_public_prepare_locals (Tstruct __6123 noattr) 128
    le m0 ma bl ba mb bd dbase bs sbase bw outedge cursor N bi edge rc
    HA HB ltac:(unfold le,gej_curve_public_temps;rewrite PTree.gso by discriminate;apply PTree.gss)
    HO HBase HAlign HFields)
    as (mc & HCopy & HFreeA & HFreeL & HLocalFields & HSeparate & HSep & HFin &
        HPrepFrame & HFreshA & HFreshL).
  destruct (exec_gej_curve_public_rest_owned le m0 bd dbase bw outedge cursor N bi edge rc
    x y z mc ba bl ltac:(unfold le,gej_curve_public_temps;rewrite !PTree.gso by discriminate;apply PTree.gss)
    HO HN HX HY HZ Hrc HM HFreeA HFreeL HLocalFields HSeparate HSep HFin)
    as (mw & HRest & HFinal & HFinalFreeA & HFinalFreeL & HRestFrame).
  destruct (owned_public_free_locals (Tstruct __6123 noattr) 128 mw bl ba
    eq_refl HSeparate HFinalFreeL HFinalFreeA) as (mf & HFree & HFreeFrame).
  assert (HFreeExt : eqext m0 bd bw bi mw mf).
  { eapply lframe_implies; [exact HFreeFrame|].
    intros b pos [_ HValid] _; split; intro HE; subst b; contradiction. }
  exists mf; split.
  - eapply eval_funcall_internal with (e:=gej_public_env bl ba) (le1:=le)
      (le2:=PTree.set _t'1
        (Vint (bit_int (Bit.toBool (@literal_gej_is_on_curve Alg.CoreFunSem ((x,y),z))))) le)
      (m1:=mb) (m2:=mw) (out:=Out_return (Some (Vint Int.one,tint))).
    + eapply gej_curve_public_entry; eassumption.
    + rewrite gej_curve_public_source.
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=le); eassumption.
    + cbn; split; [discriminate|reflexivity].
    + exact HFree.
  - split.
    + eapply finv_stable; [exact HO|exact HFinal|exact HFreeExt].
    + assert (HF : lframe (fun b _ => Mem.valid_block m0 b /\ ~ extA m0 bd bw bi b) m0 mf).
      { eapply lframe_trans.
        - eapply lframe_implies; [exact HPrepFrame|].
          intros b pos [HV _] _; split; intro HE; subst b; contradiction.
        - eapply lframe_trans.
          + eapply lframe_implies; [exact HRestFrame|].
            intros b pos [HV HE] _; unfold secp_locals_outside.
            split; [intro HEq;subst b;contradiction|].
            split; [intro HEq;subst b;contradiction|exact HE].
          + eapply lframe_implies; [exact HFreeFrame|].
            intros b pos [HV _] _; split; intro HE; subst b; contradiction. }
      eapply lframe_implies; [exact HF|]; intros b pos HE HV; split; assumption.
Qed.
Print Assumptions eval_gej_curve_literal_public.
