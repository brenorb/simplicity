(** Entire original finite-affine validity helper: actual allocations, entry,
    flag branch, all arithmetic, integer return conversion and private frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns.
Require Import C.jet_secp_field_read_preservation C.jet_secp_curve_frame.
Require Import C.jet_secp_curve_statements C.jet_secp_curve_body.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition curve_entry_temps ba :=
  PTree.set _a (Vptr ba Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_ge_is_valid_var)).
Lemma curve_function_ok : fn_okb f_secp256k1_ge_is_valid_var = true.
Proof. vm_compute; reflexivity. Qed.
Lemma curve_function_entry m ma mi ba b_y2 bx :
  Mem.alloc m 0 40 = (ma,b_y2) -> Mem.alloc ma 0 40 = (mi,bx) ->
  function_entry2 secp_ge f_secp256k1_ge_is_valid_var [Vptr ba Ptrofs.zero] m
    (curve_helper_env b_y2 bx) (curve_entry_temps ba) mi.
Proof.
  intros HY HX. destruct (fn_okb_true _ curve_function_ok) as (HN1 & HN2 & HD).
  constructor; [exact HN1|exact HN2|exact HD| |reflexivity].
  eapply alloc_variables_cons with (m1:=ma) (b1:=b_y2).
  - exact HY.
  - eapply alloc_variables_cons with (m1:=mi) (b1:=bx); [exact HX|constructor].
Qed.
Lemma curve_function_blocks b_y2 bx : blocks_of_env secp_ge (curve_helper_env b_y2 bx) =
  [(b_y2,0,40);(bx,0,40)].
Proof. reflexivity. Qed.

Theorem eval_curve_finite_function_readback x y m ba :
  square_input_bounds x -> square_input_bounds y ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) ->
  Mem.range_perm m ba 0 88 Cur Freeable -> Mem.load Mint32 m ba 80 = Some (Vint Int.zero) ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_is_valid_var)
    [Vptr ba Ptrofs.zero] E0 mf (Vint (curve_result x y)) /\
  fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
  Mem.range_perm mf ba 0 88 Cur Freeable /\ lframe (fun b _ => b<>ba) m mf /\
  Mem.load Mint32 mf ba 80=Mem.load Mint32 m ba 80.
Proof.
  intros BX BY HX HY HFA HFlag.
  destruct (Mem.alloc m 0 40) as [ma b_y2] eqn:AY.
  destruct (Mem.alloc ma 0 40) as [mi bx] eqn:AX.
  assert (HV : Mem.valid_block m ba) by (eapply Mem.perm_valid_block; apply (HFA 0); lia).
  assert (HAY : ba<>b_y2).
  { intro HE. apply (Mem.fresh_block_alloc _ _ _ _ _ AY). rewrite <- HE; exact HV. }
  assert (HAX : ba<>bx).
  { intro HE. apply (Mem.fresh_block_alloc _ _ _ _ _ AX). rewrite <- HE.
    eapply Mem.valid_block_alloc; eassumption. }
  assert (HYX : b_y2<>bx).
  { intro HE. apply (Mem.fresh_block_alloc _ _ _ _ _ AX). rewrite <- HE.
    eapply Mem.valid_new_block; exact AY. }
  assert (FAlloc : lframe (fun _ _ => True) m mi).
  { eapply lframe_trans; apply lframe_unchanged; eapply Mem.alloc_unchanged_on; eassumption. }
  pose proof (field_at_lframe m mi ba 0 (words5 x) _ HX FAlloc ltac:(intros; exact I)) as HXi.
  pose proof (field_at_lframe m mi ba 40 (words5 y) _ HY FAlloc ltac:(intros; exact I)) as HYi.
  pose proof (curve_keep_free _ m mi ba 88 ltac:(lia) HFA FAlloc ltac:(intros; exact I)) as HFAi.
  assert (HFlagi : Mem.load Mint32 mi ba 80 = Some (Vint Int.zero)).
  { rewrite (proj1 FAlloc Mint32 ba 80 HV ltac:(intros; exact I)); exact HFlag. }
  assert (HFYi : Mem.range_perm mi b_y2 0 40 Cur Freeable).
  { intros pos HPos. eapply Mem.perm_alloc_1; [exact AX|]. eapply Mem.perm_alloc_2; eassumption. }
  assert (HFXi : Mem.range_perm mi bx 0 40 Cur Freeable).
  { intros pos HPos. eapply Mem.perm_alloc_2; eassumption. }
  assert (HA : (curve_entry_temps ba)!_a = Some (Vptr ba Ptrofs.zero)) by (apply PTree.gss).
  destruct (exec_curve_finite_body_readback (curve_entry_temps ba) x y mi ba b_y2 bx
    HA HFlagi BX BY HAY HAX HYX HXi HYi HFAi HFYi HFXi)
    as (mo & HBody & HXo & HYo & HFAo & HFYo & HFXo & FBody & FlagReadback).
  destruct (free_list_exists [(b_y2,0,40);(bx,0,40)] mo) as (mf & HFree & HUnchanged).
  - cbn; repeat constructor; cbn; intuition congruence.
  - intros b lo hi [H|[H|H]]; [inversion H; subst; exact HFYo|inversion H; subst; exact HFXo|contradiction].
  - assert (FFree : lframe (fun b _ => b<>b_y2 /\ b<>bx) mo mf).
    { eapply lframe_implies; [apply lframe_unchanged; exact HUnchanged|].
      intros b pos [HNotY HNotX] HV'; cbn; intuition congruence. }
    pose proof (field_at_lframe mo mf ba 0 (words5 x) _ HXo FFree ltac:(intro pos; split; assumption)) as HXf.
    pose proof (field_at_lframe mo mf ba 40 (words5 y) _ HYo FFree ltac:(intro pos; split; assumption)) as HYf.
    pose proof (curve_keep_free _ mo mf ba 88 ltac:(lia) HFAo FFree ltac:(intro pos; split; assumption)) as HFAf.
    assert (ValidO:Mem.valid_block mo ba) by (eapply Mem.perm_valid_block;apply (HFAo 0);lia).
    assert (FlagFinal:Mem.load Mint32 mf ba 80=Mem.load Mint32 m ba 80).
    { rewrite (proj1 FFree Mint32 ba 80 ValidO ltac:(intros;split;assumption)),FlagReadback.
      apply (proj1 FAlloc);[exact HV|intros;exact I]. }
    exists mf. split.
    + eapply eval_funcall_internal with (e:=curve_helper_env b_y2 bx) (le1:=curve_entry_temps ba)
        (le2:=curve_body_temps (curve_entry_temps ba) x y) (m1:=mi) (m2:=mo)
        (out:=Out_return (Some (Vint (curve_result x y),tint))).
      * exact (curve_function_entry m ma mi ba b_y2 bx AY AX).
      * exact HBody.
      * split; [discriminate|reflexivity].
      * rewrite curve_function_blocks; exact HFree.
    + split; [exact HXf|]. split; [exact HYf|]. split; [exact HFAf|].
      split;[|exact FlagFinal].
      assert (HFrame : lframe (fun b _ => Mem.valid_block m b /\ b<>ba) m mf).
      { eapply lframe_trans.
        - eapply lframe_implies; [exact FAlloc|]. intros; exact I.
        - eapply lframe_trans.
          + eapply lframe_implies; [exact FBody|]. intros b pos [HV0 HNotA] HV1.
            split; [exact HNotA|]. split; intro HE; subst b.
            * exact (Mem.fresh_block_alloc _ _ _ _ _ AY HV0).
            * apply (Mem.fresh_block_alloc _ _ _ _ _ AX).
              eapply Mem.valid_block_alloc; eassumption.
          + eapply lframe_implies; [exact FFree|]. intros b pos [HV0 HNotA] HV1.
            split; intro HE; subst b.
            * exact (Mem.fresh_block_alloc _ _ _ _ _ AY HV0).
            * apply (Mem.fresh_block_alloc _ _ _ _ _ AX).
              eapply Mem.valid_block_alloc; eassumption. }
      eapply lframe_implies; [exact HFrame|]. intros b pos HOther HV0; split; assumption.
Qed.

Theorem eval_curve_finite_function x y m ba :
  square_input_bounds x -> square_input_bounds y ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) ->
  Mem.range_perm m ba 0 88 Cur Freeable -> Mem.load Mint32 m ba 80 = Some (Vint Int.zero) ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_is_valid_var)
    [Vptr ba Ptrofs.zero] E0 mf (Vint (curve_result x y)) /\
  fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
  Mem.range_perm mf ba 0 88 Cur Freeable /\ lframe (fun b _ => b<>ba) m mf.
Proof.
 intros BX BY HX HY HFA HFlag.
 destruct (eval_curve_finite_function_readback x y m ba BX BY HX HY HFA HFlag) as (mf & Rest).
 exists mf;tauto.
Qed.
