(* Complete unchanged scalar-zero C function against its literal term. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_exec C.jet_readBit_layout C.jet_frame_layout C.jet_frame_inv.
Require Import C.jet_encoding C.jet_input_layout C.jet_output_layout C.jet_sx_mem C.jet_secp_frame.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_public_body.
Require Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg Simplicity.Translate.
Require Import C.jet_secp_scalar_public_entry C.jet_secp_scalar_public_setup.
Require Import C.jet_secp_scalar_public_rest C.jet_secp_canonical_scalar_zero.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_scalar_is_zero Simplicity.Translate.encode.

Lemma scalar_zero_public_body :
  fn_body f_simplicity_scalar_is_zero =
    Ssequence (Sassign (Evar _src secp_frame_type) (Etempvar _src secp_frame_type)) scalar_public_rest.
Proof. reflexivity. Qed.

(* Every allocation, source copy, helper call, write, return and free is derived.
   These are the inherited local frame contracts, not the general evaluator domain. *)
Theorem eval_secp_scalar_zero_canonical v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word.Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 1 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc+256 <= Int64.max_unsigned ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_scalar_is_zero)
      [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf Datatypes.true
      (Simplicity.Translate.encode (@canonical_scalar_is_zero Alg.CoreFunSem value)) /\
    lframe (fun b _ => ~ extA m0 bd bw bi b) m0 mf.
Proof.
  intros HO HCapacity HBase HAlign HFields HI Hrc HM.
  destruct (Mem.alloc m0 0 16) as [ma bl] eqn:HA.
  destruct (Mem.alloc ma 0 32) as [mb ba] eqn:HB.
  destruct (scalar_prepare_public_locals (scalar_public_temps v_env bd dbase bs sbase)
    m0 ma bl ba mb bd dbase bs sbase bw outedge cursor N bi edge rc value
    HA HB HO HCapacity HBase HAlign HFields (scalar_public_src_temp v_env bd dbase bs sbase))
    as (mc & HCopy & HFreeA & HFreeL & HLocalFields & HSeparate & HSep & HInv & HPrepFrame & HFreshA & HFreshL).
  assert (HDst : (scalar_public_temps v_env bd dbase bs sbase)!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold scalar_public_temps; rewrite !PTree.gso by discriminate; apply PTree.gss. }
  destruct (exec_scalar_public_rest_canonical (scalar_public_temps v_env bd dbase bs sbase)
    m0 bd dbase bw outedge cursor N bi edge rc value mc ba bl
    HDst HO HI Hrc HM HFreeA HFreeL HLocalFields HSeparate HSep HInv)
    as (mw & HRest & HFinal & HFinalFreeA & HFinalFreeL & HRestFrame).
  destruct (scalar_free_public_locals mw bl ba HSeparate HFinalFreeL HFinalFreeA)
    as (mf & HFree & HFreeFrame).
  assert (HFreeExt : eqext m0 bd bw bi mw mf).
  { eapply lframe_implies; [exact HFreeFrame|].
    intros b pos [_ HValid] _; split; intro HEq; subst b; contradiction. }
  exists mf; split.
  - eapply eval_funcall_internal with (e := scalar_public_env bl ba)
      (le1 := scalar_public_temps v_env bd dbase bs sbase)
      (le2 := PTree.set _t'1 (Vint (bit_int (Bit.toBool (@canonical_scalar_is_zero Alg.CoreFunSem value))))
        (scalar_public_temps v_env bd dbase bs sbase)) (m1 := mb) (m2 := mw)
      (out := Out_return (Some (Vint Int.one, tint))).
    + eapply scalar_zero_public_entry; eassumption.
    + rewrite scalar_zero_public_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
        (le1 := scalar_public_temps v_env bd dbase bs sbase); eassumption.
    + cbn; split; [discriminate|reflexivity].
    + exact HFree.
  - split.
    + eapply finv_stable; [exact HO|exact HFinal|exact HFreeExt].
    + assert (HOutside : lframe (fun b _ => Mem.valid_block m0 b /\ ~ extA m0 bd bw bi b) m0 mf).
      { eapply lframe_trans.
        - eapply lframe_implies; [exact HPrepFrame|].
          intros b pos [HValid _] _; split; intro HEq; subst b; contradiction.
        - eapply lframe_trans.
          + eapply lframe_implies; [exact HRestFrame|].
            intros b pos [HValid HExt] _; unfold secp_locals_outside.
            split; [intro HEq; subst b; contradiction|];
              split; [intro HEq; subst b; contradiction|exact HExt].
          + eapply lframe_implies; [exact HFreeFrame|].
            intros b pos [HValid _] _; split; intro HEq; subst b; contradiction. }
      eapply lframe_implies; [exact HOutside|]; intros b pos HExt HValid; split; assumption.
Qed.
