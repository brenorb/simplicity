(** Complete unchanged scalar_normalize C call against its literal term.
    Allocation, source copy, both helper calls, return and free are derived. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_exec C.jet_readBit_layout C.jet_frame_layout C.jet_frame_inv.
Require Import C.jet_encoding C.jet_input_layout C.jet_output_layout C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_public_body C.jet_secp_wrapper_run.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_secp_scalar_public_entry C.jet_secp_scalar_public_setup.
Require Import C.jet_secp_canonical_scalar.
Require Import C.jet_secp_scalar_normalize_rest.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_scalar_normalize encode.

Definition scalar_normalize_temps (v_env : val) bd dbase bs sbase : temp_env :=
  PTree.set _env v_env
    (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
      (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
        (create_undef_temps (fn_temps f_simplicity_scalar_normalize)))).

Lemma scalar_normalize_entry v_env m ma mb bl ba bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 32 = (mb, ba) ->
  function_entry2 secp_ge f_simplicity_scalar_normalize
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] m
    (scalar_public_env bl ba) (scalar_normalize_temps v_env bd dbase bs sbase) mb.
Proof.
  intros HA HB; constructor.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY HE; cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in HE; discriminate|congruence].
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma, bl)); exact HA.
    + eapply alloc_variables_cons with (m1 := mb) (b1 := ba).
      * change (Mem.alloc ma 0 32 = (mb, ba)); exact HB.
      * constructor.
  - reflexivity.
Qed.

Lemma scalar_normalize_src_temp v_env bd dbase bs sbase :
  (scalar_normalize_temps v_env bd dbase bs sbase)!_src = Some (Vptr bs (Ptrofs.repr sbase)).
Proof. unfold scalar_normalize_temps; rewrite PTree.gso by discriminate; apply PTree.gss. Qed.
Lemma scalar_normalize_public_body :
  fn_body f_simplicity_scalar_normalize =
    Ssequence (Sassign (Evar _src secp_frame_type) (Etempvar _src secp_frame_type)) scalar_normalize_rest.
Proof. reflexivity. Qed.

Theorem eval_secp_scalar_normalize_canonical v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 256 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_scalar_normalize)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (encode (@canonical_scalar_normalize Alg.CoreFunSem value)) /\
    lframe (fun b _ => ~ extA m0 bd bw bi b) m0 mf.
Proof.
  intros HO HCapacity HBase HAlign HFields HI Hrc HM.
  destruct (Mem.alloc m0 0 16) as [ma bl] eqn:HA.
  destruct (Mem.alloc ma 0 32) as [mb ba] eqn:HB.
  destruct (scalar_prepare_public_locals (scalar_normalize_temps v_env bd dbase bs sbase)
    m0 ma bl ba mb bd dbase bs sbase bw outedge cursor N bi edge rc value
    HA HB HO ltac:(lia) HBase HAlign HFields (scalar_normalize_src_temp v_env bd dbase bs sbase))
    as (mc & HCopy & HFreeA & HFreeL & HLocalFields & HSeparate & HSep & HInv & HPrepFrame & HFreshA & HFreshL).
  assert (HInv256 : invA m0 bd dbase bw outedge cursor N bi rc false [] 256
      (read_fe_rho (frame_input_word_bits value) rc) [] mc).
  { destruct HInv as [HRho [HF [_ HW]]].
    split; [exact HRho|]; split; [exact HF|]; split; [exact HCapacity|cbn; lia]. }
  assert (HDst : (scalar_normalize_temps v_env bd dbase bs sbase)!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold scalar_normalize_temps; rewrite !PTree.gso by discriminate; apply PTree.gss. }
  destruct (exec_scalar_normalize_rest_canonical (scalar_normalize_temps v_env bd dbase bs sbase)
    m0 bd dbase bw outedge cursor N bi edge rc value mc ba bl
    HDst HO HI Hrc HM HFreeA HFreeL HLocalFields HSeparate HSep HInv256)
    as (mw & HRest & HFinal & HFinalFreeA & HFinalFreeL & HRestFrame).
  destruct (scalar_free_public_locals mw bl ba HSeparate HFinalFreeL HFinalFreeA)
    as (mf & HFree & HFreeFrame).
  assert (HFreeExt : eqext m0 bd bw bi mw mf).
  { eapply lframe_implies; [exact HFreeFrame|].
    intros b pos [_ HValid] _; split; intro HEq; subst b; contradiction. }
  exists mf; split.
  - eapply eval_funcall_internal with (e := scalar_public_env bl ba)
      (le1 := scalar_normalize_temps v_env bd dbase bs sbase)
      (le2 := scalar_normalize_temps v_env bd dbase bs sbase) (m1 := mb) (m2 := mw)
      (out := Out_return (Some (Vint Int.one, tint))).
    + eapply scalar_normalize_entry; eassumption.
    + rewrite scalar_normalize_public_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
        (le1 := scalar_normalize_temps v_env bd dbase bs sbase); eassumption.
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
