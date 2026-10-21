(** Entire original in-place gej_double: both parameter bindings, three real
    local allocations, flag copy, all arithmetic, void result and all frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp
  C.jet_secp_double_statements C.jet_secp_double_body C.jet_secp_double_all_calls C.jet_secp_double_prefix
  C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
  C.jet_secp_curve_frame C.jet_secp_field_read_preservation.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition double_entry_temps ba := PTree.set _a (Vptr ba Ptrofs.zero)
  (PTree.set _r (Vptr ba Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_gej_double))).
Lemma double_function_ok : fn_okb f_secp256k1_gej_double=true.
Proof. reflexivity. Qed.
Lemma double_function_entry m ml ms mi ba bl bs bt :
  Mem.alloc m 0 40=(ml,bl) -> Mem.alloc ml 0 40=(ms,bs) -> Mem.alloc ms 0 40=(mi,bt) ->
  function_entry2 secp_ge f_secp256k1_gej_double [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] m
    (double_helper_env bl bs bt) (double_entry_temps ba) mi.
Proof.
  intros AL AS AT;destruct (fn_okb_true _ double_function_ok) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
  eapply alloc_variables_cons with (m1:=ml) (b1:=bl);[exact AL|].
  eapply alloc_variables_cons with (m1:=ms) (b1:=bs);[exact AS|].
  eapply alloc_variables_cons with (m1:=mi) (b1:=bt);[exact AT|constructor].
Qed.
Lemma double_function_blocks bl bs bt : blocks_of_env secp_ge (double_helper_env bl bs bt)=
  [(bs,0,40);(bl,0,40);(bt,0,40)].
Proof. reflexivity. Qed.

Theorem eval_double_function x y z m ba flag :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  Mem.load Mint32 m ba 120=Some (Vint flag) ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double)
    [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef /\
  fe_at mf ba 0 (words5 (double_output_x_words x y)) /\
  fe_at mf ba 40 (words5 (double_output_y_words x y)) /\
  fe_at mf ba 80 (words5 (double_output_z_words y z)) /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
  square_input_bounds (double_output_x_words x y) /\
  square_input_bounds (double_output_y_words x y) /\
  square_input_bounds (double_output_z_words y z) /\ lframe (fun b _ => b<>ba) m mf.
Proof.
  intros BX BY BZ HFlag HX HY HZ HFA.
  destruct (Mem.alloc m 0 40) as [ml bl] eqn:AL.
  destruct (Mem.alloc ml 0 40) as [ms bs] eqn:AS.
  destruct (Mem.alloc ms 0 40) as [mi bt] eqn:AT.
  assert (HOld : forall b, Mem.valid_block m b -> b<>bs /\ b<>bl /\ b<>bt).
  { intros b HV;repeat split;intro HE;subst b.
    - apply (Mem.fresh_block_alloc _ _ _ _ _ AS);eapply Mem.valid_block_alloc;[exact AL|exact HV].
    - exact (Mem.fresh_block_alloc _ _ _ _ _ AL HV).
    - apply (Mem.fresh_block_alloc _ _ _ _ _ AT).
      eapply Mem.valid_block_alloc;[exact AS|]. eapply Mem.valid_block_alloc;[exact AL|exact HV]. }
  assert (HV : Mem.valid_block m ba) by (eapply Mem.perm_valid_block;apply (HFA 0);lia).
  destruct (HOld ba HV) as (HAS & HAL & HAT).
  assert (HSL : bs<>bl).
  { intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ AS);rewrite HE;eapply Mem.valid_new_block;exact AL. }
  assert (HST : bs<>bt).
  { intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ AT);rewrite <- HE;eapply Mem.valid_new_block;exact AS. }
  assert (HLT : bl<>bt).
  { intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ AT);rewrite <- HE.
    eapply Mem.valid_block_alloc;[exact AS|eapply Mem.valid_new_block;exact AL]. }
  assert (FAlloc : lframe (fun _ _ => True) m mi).
  { eapply lframe_trans.
    - apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact AL.
    - eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption. }
  pose proof (field_at_lframe m mi ba 0 _ _ HX FAlloc ltac:(intros;exact I)) as HXi.
  pose proof (field_at_lframe m mi ba 40 _ _ HY FAlloc ltac:(intros;exact I)) as HYi.
  pose proof (field_at_lframe m mi ba 80 _ _ HZ FAlloc ltac:(intros;exact I)) as HZi.
  pose proof (curve_keep_free _ m mi ba 128 ltac:(lia) HFA FAlloc ltac:(intros;exact I)) as HFAi.
  assert (HFlagi : Mem.load Mint32 mi ba 120=Some (Vint flag)).
  { rewrite (proj1 FAlloc Mint32 ba 120 HV ltac:(intros;exact I));exact HFlag. }
  assert (HFLi : Mem.range_perm mi bl 0 40 Cur Freeable).
  { intros pos HP;eapply Mem.perm_alloc_1;[exact AT|]. eapply Mem.perm_alloc_1;[exact AS|].
    eapply Mem.perm_alloc_2;[exact AL|exact HP]. }
  assert (HFSi : Mem.range_perm mi bs 0 40 Cur Freeable).
  { intros pos HP;eapply Mem.perm_alloc_1;[exact AT|]. eapply Mem.perm_alloc_2;[exact AS|exact HP]. }
  assert (HFTi : Mem.range_perm mi bt 0 40 Cur Freeable).
  { intros pos HP;eapply Mem.perm_alloc_2;[exact AT|exact HP]. }
  assert (HA : (double_entry_temps ba)!_a=Some (Vptr ba Ptrofs.zero)) by (apply PTree.gss).
  assert (HR : (double_entry_temps ba)!_r=Some (Vptr ba Ptrofs.zero)).
  { unfold double_entry_temps;rewrite PTree.gso by discriminate;apply PTree.gss. }
  destruct (exec_double_body_owned (double_entry_temps ba) x y z mi ba bs bl bt flag
    HA HR HFlagi BX BY BZ HAS HAL HAT HSL HST HLT HXi HYi HZi HFAi HFSi HFLi HFTi)
    as (mo & HBody & XO & YO & ZO & AFo & SFo & LFo & TFo & BXO & BYO & BZO & FBody).
  destruct (free_list_exists [(bs,0,40);(bl,0,40);(bt,0,40)] mo) as (mf & HFree & HUnchanged).
  - cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi [H|[H|[H|H]]];
      [inversion H;subst;exact SFo|inversion H;subst;exact LFo|inversion H;subst;exact TFo|contradiction].
  - assert (FFree : lframe (fun b _ => b<>bs /\ b<>bl /\ b<>bt) mo mf).
    { eapply lframe_implies;[apply lframe_unchanged;exact HUnchanged|].
      intros b pos (NS & NL & NT) HV';cbn;intuition congruence. }
    pose proof (field_at_lframe mo mf ba 0 _ _ XO FFree ltac:(intro pos;repeat split;assumption)) as XF.
    pose proof (field_at_lframe mo mf ba 40 _ _ YO FFree ltac:(intro pos;repeat split;assumption)) as YF.
    pose proof (field_at_lframe mo mf ba 80 _ _ ZO FFree ltac:(intro pos;repeat split;assumption)) as ZF.
    pose proof (curve_keep_free _ mo mf ba 128 ltac:(lia) AFo FFree
      ltac:(intro pos;repeat split;assumption)) as AFf.
    exists mf;split.
    + eapply eval_funcall_internal with (e:=double_helper_env bl bs bt) (le1:=double_entry_temps ba)
        (le2:=PTree.set _t'1 (Vint flag) (double_entry_temps ba)) (m1:=mi) (m2:=mo) (out:=Out_normal).
      * exact (double_function_entry m ml ms mi ba bl bs bt AL AS AT).
      * exact HBody.
      * reflexivity.
      * rewrite double_function_blocks;exact HFree.
    + split;[exact XF|];split;[exact YF|];split;[exact ZF|];split;[exact AFf|].
      split;[exact BXO|];split;[exact BYO|];split;[exact BZO|].
      assert (HFrame : lframe (fun b _ => Mem.valid_block m b /\ b<>ba) m mf).
      { eapply lframe_trans.
        - eapply lframe_implies;[exact FAlloc|];intros;exact I.
        - eapply lframe_trans.
          + eapply lframe_implies;[exact FBody|]. intros b pos [HV0 HNotA] HV1.
            destruct (HOld b HV0) as (NS & NL & NT).
            split;[unfold double_work_frame;repeat split;assumption|exact NT].
          + eapply lframe_implies;[exact FFree|]. intros b pos [HV0 HNotA] HV1;exact (HOld b HV0). }
      eapply lframe_implies;[exact HFrame|]. intros b pos HOther HV0;split;assumption.
Qed.
