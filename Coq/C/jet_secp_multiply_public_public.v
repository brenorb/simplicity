(** Complete actual public C function: entry/copy/body/return/free, full domain.
    The numeric result is still an intermediate, not the literal specification. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Translate.
Require Import C.jet_frame_layout C.jet_output_layout C.jet_encoding C.jet_frame_inv.
Require Import C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_multiply_input_input C.jet_secp_multiply_input_pair.
Require Import C.jet_secp_multiply_public_layout C.jet_secp_multiply_public_rest C.jet_secp_multiply_public_lifecycle.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge input_product_word pair_rho normalized_value Simplicity.Translate.encode.

Theorem eval_original_public_field_multiply v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (x y : Ty.tySem (Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 256 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc
    (@Simplicity.Translate.encode (Ty.Prod (Word 8) (Word 8)) (x, y)) ->
  0 <= rc -> rc + 512 <= Int64.max_unsigned ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_fe_multiply)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (@Simplicity.Translate.encode (Word 8) (input_product_word x y)) /\
    lframe (fun b _ => ~ extA m0 bd bw bi b) m0 mf.
Proof.
  intros HO HCapacity HBase HAlign HFields HInput HCursor HMax.
  destruct (Mem.alloc m0 0 16) as [ml bl] eqn:HL.
  destruct (Mem.alloc ml 0 40) as [ma ba] eqn:HA.
  destruct (Mem.alloc ma 0 40) as [mb bb] eqn:HB.
  destruct (prepare_three v_env m0 ml ma mb bl ba bb bd dbase bs sbase bw outedge cursor N bi edge rc
    HL HA HB HO HBase HAlign HFields)
    as (mc & HCopy & HFA & HFB & HFL & HLocalFields & HDAB & HDAL & HDBL & HS & HI & HPrepFrame & HNA & HNB & HNL).
  destruct (exec_original_public_rest (public_temps v_env bd dbase bs sbase)
    m0 bd dbase bw outedge cursor N bi edge rc x y mc ba bb bl
    eq_refl HO HCapacity HInput HCursor HMax HFA HFB HFL HLocalFields HDAB HDAL HDBL HS HI)
    as (mw & HRest & HFinal & HFinalFreeA & HFinalFreeB & HFinalFreeL & HRestFrame).
  destruct (free_three mw bl ba bb HDAB HDAL HDBL HFinalFreeL HFinalFreeA HFinalFreeB)
    as (mf & HFree & HFreeFrame).
  assert (HFreeExt : eqext m0 bd bw bi mw mf).
  { eapply lframe_implies; [exact HFreeFrame|].
    intros b pos [_ HV] HValid; repeat split; intro HEq; subst b; contradiction. }
  exists mf; split.
  - eapply eval_funcall_internal with (e := public_env bl ba bb)
      (le1 := public_temps v_env bd dbase bs sbase) (le2 := public_temps v_env bd dbase bs sbase)
      (m1 := mb) (m2 := mw) (out := Out_return (Some (Vint Int.one, tint))).
    + eapply original_public_entry; eassumption.
    + rewrite original_public_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
        (le1 := public_temps v_env bd dbase bs sbase); eassumption.
    + cbn; split; [discriminate|reflexivity].
    + exact HFree.
  - split.
    + eapply finv_stable; [exact HO|exact HFinal|exact HFreeExt].
    + assert (HOutside : lframe
        (fun b _ => Mem.valid_block m0 b /\ ~ extA m0 bd bw bi b) m0 mf).
      { eapply lframe_trans.
        - eapply lframe_implies; [exact HPrepFrame|].
          intros b pos [HV HE] HValid; repeat split; intro HEq; subst b; contradiction.
        - eapply lframe_trans.
          + eapply lframe_implies; [exact HRestFrame|].
            intros b pos [HV HE] HValid; unfold pair_locals_outside.
            split; [intro HEq; subst b; contradiction|];
              split; [intro HEq; subst b; contradiction|];
              split; [intro HEq; subst b; contradiction|exact HE].
          + eapply lframe_implies; [exact HFreeFrame|].
            intros b pos [HV HE] HValid; repeat split; intro HEq; subst b; contradiction. }
      eapply lframe_implies; [exact HOutside|]; intros b pos HE HV; split; assumption.
Qed.
