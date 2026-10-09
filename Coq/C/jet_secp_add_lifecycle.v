(** Actual original public field-add call, including entry, copy and freeing. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight ClightBigstep Values Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_encoding C.jet_input_layout C.jet_frame_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_literal_add_program C.jet_secp_add_body C.jet_secp_add_entry.
Require Import C.jet_secp_add_prepare C.jet_secp_add_rest.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_fe_add encode.

Theorem eval_secp_fe_add_literal v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (a b : Ty.tySem (Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 256 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc (@encode (Ty.Prod (Word 8) (Word 8)) (a,b)) ->
  0 <= rc -> rc+512 <= Int64.max_unsigned ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_fe_add)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (encode (@literal_fe_add Alg.CoreFunSem (a,b))) /\
    lframe (fun bx _ => ~ extA m0 bd bw bi bx) m0 mf.
Proof.
  intros HO HN HBase HAlign HFields HI Hrc HM.
  destruct (Mem.alloc m0 0 16) as [ml bl] eqn:HL.
  destruct (Mem.alloc ml 0 40) as [ma ba] eqn:HA.
  destruct (Mem.alloc ma 0 40) as [mb bb] eqn:HB.
  set (le := secp_add_temps v_env bd dbase bs sbase).
  destruct (secp_prepare_add_locals le m0 ml ma mb bl ba bb bd dbase bs sbase
    bw outedge cursor N bi edge rc a HL HA HB HO HN HBase HAlign HFields eq_refl)
    as (mc & HCopy & HFA & HFB & HFL & HSource & HAB & HAL & HBL &
      HXSA & HXSB & HInv & HPrep & HFreshA & HFreshB & HFreshL).
  destruct (exec_secp_fe_add_rest_literal le m0 bd dbase bw outedge cursor N bi edge rc
    a b mc ba bb bl eq_refl HO HI Hrc HM HFA HFB HFL HSource HAB HAL HBL HXSA HXSB HInv)
    as (mw & HRest & HFinal & HFinalA & HFinalB & HFinalL & HRestFrame).
  destruct (secp_free_add_locals mw bl ba bb HAL HBL HAB HFinalL HFinalA HFinalB)
    as (mf & HFree & HFreeFrame).
  assert (HFreeExt : eqext m0 bd bw bi mw mf).
  { eapply lframe_implies; [exact HFreeFrame|].
    intros bx pos [_ HValid] _; repeat split; intro HE; subst bx; contradiction. }
  exists mf. split.
  - eapply eval_funcall_internal with (e := secp_public_add_env bl ba bb)
      (le1 := le) (le2 := le) (m1 := mb) (m2 := mw)
      (out := Out_return (Some (Vint Int.one, tint))).
    + eapply secp_fe_add_entry; eassumption.
    + rewrite secp_fe_add_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le); eassumption.
    + cbn; split; [discriminate|reflexivity].
    + exact HFree.
  - split.
    + eapply finv_stable; [exact HO|exact HFinal|exact HFreeExt].
    + assert (HOutside : lframe (fun bx _ => Mem.valid_block m0 bx /\ ~ extA m0 bd bw bi bx) m0 mf).
      { eapply lframe_trans.
        - eapply lframe_implies; [exact HPrep|].
          intros bx pos [HValid _] _; repeat split; intro HE; subst bx; contradiction.
        - eapply lframe_trans.
          + eapply lframe_implies; [exact HRestFrame|].
            intros bx pos [HValid HExt] _; split; [intro HE; subst bx; contradiction|].
            split; [intro HE; subst bx; contradiction|].
            split; [intro HE; subst bx; contradiction|exact HExt].
          + eapply lframe_implies; [exact HFreeFrame|].
            intros bx pos [HValid _] _; repeat split; intro HE; subst bx; contradiction. }
      eapply lframe_implies; [exact HOutside|]. intros bx pos HExt HValid; split; assumption.
Qed.
Print Assumptions eval_secp_fe_add_literal.
