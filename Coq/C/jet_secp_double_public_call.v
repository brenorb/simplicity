(** Actual public doubling lifecycle; no assumed output, execution or free. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jet_exec C.jet_encoding C.jet_readBit_layout C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_gej_public_lifecycle C.jet_secp_gej_public_entry C.jet_secp_public_body.
Require Import C.jet_secp_public_copy.
Require Import C.jet_secp_wrapper_run C.jet_secp_canonical_zero.
Require Import C.jet_secp_gej_owned_prepare C.jet_secp_double_public_boundary.
Require Import C.jet_secp_double_literal C.jet_secp_double_public_rest.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_is_zero Simplicity.Translate.encode.

Theorem eval_gej_double_literal_public v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (x y z : Ty.tySem (Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 768 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits z)) ->
  0 <= rc -> rc+768 <= Int64.max_unsigned ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_gej_double)
      [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_gej_double Alg.CoreFunSem ((x,y),z))) /\
    lframe (fun b _ => ~ extA m0 bd bw bi b) m0 mf.
Proof.
  intros HO HN HBase HAlign HFields HX HY HZ Hrc HM.
  destruct (Mem.alloc m0 0 16) as [ma bl] eqn:HA.
  destruct (Mem.alloc ma 0 128) as [mb ba] eqn:HB.
  set (le := secp_public_temps v_env bd dbase bs sbase).
  destruct (gej_prepare_owned_locals le m0 ma bl ba mb bd dbase bs sbase bw outedge cursor N bi edge rc
    HA HB ltac:(unfold le,secp_public_temps;rewrite PTree.gso by discriminate;apply PTree.gss)
    HO HBase HAlign HFields)
    as (mc & HCopy & HFreeA & HFreeL & HLocalFields & HSeparate & HSep & HFin &
        HPrepFrame & HFreshA & HFreshL).
  assert (HI : invA m0 bd dbase bw outedge cursor N bi rc false [] 768
    (read_fe_rho (frame_input_word_bits x) rc) [] mc).
  { split; [reflexivity|]. split; [exact HFin|]. split; [exact HN|cbn;lia]. }
  destruct (exec_double_rest_owned le m0 bd dbase bw outedge cursor N bi edge rc
    x y z mc ba bl ltac:(unfold le,secp_public_temps;rewrite !PTree.gso by discriminate;apply PTree.gss)
    HO HX HY HZ Hrc HM HFreeA HFreeL HLocalFields HSeparate HSep HI)
    as (mw & HRest & HFinal & HFinalFreeA & HFinalFreeL & HRestFrame).
  destruct (gej_free_public_locals mw bl ba HSeparate HFinalFreeL HFinalFreeA)
    as (mf & HFree & HFreeFrame).
  assert (HFreeExt : eqext m0 bd bw bi mw mf).
  { eapply lframe_implies; [exact HFreeFrame|].
    intros b pos [_ HValid] _; split; intro HE; subst b; contradiction. }
  exists mf; split.
  - eapply eval_funcall_internal with (e := gej_public_env bl ba)
      (le1 := le)
      (le2 := le)
      (m1 := mb) (m2 := mw) (out := Out_return (Some (Vint Int.one, tint))).
    + eapply gej_double_public_entry; eassumption.
    + rewrite gej_double_public_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le); eassumption.
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
            split; [intro HEqual;subst b;contradiction|].
            split; [intro HEqual;subst b;contradiction|exact HE].
          + eapply lframe_implies; [exact HFreeFrame|].
            intros b pos [HV _] _; split; intro HE; subst b; contradiction. }
      eapply lframe_implies; [exact HF|]; intros b pos HE HV; split; assumption.
Qed.
Timeout 60 Print Assumptions eval_gej_double_literal_public.
