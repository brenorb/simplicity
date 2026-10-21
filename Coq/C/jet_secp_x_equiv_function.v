(** Complete original gej_eq_x_var call, including entry and private frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns.
Require Import C.jet_secp_field_read_preservation C.jet_secp_curve_frame.
Require Import C.jet_secp_x_equiv_statements C.jet_secp_x_equiv_body.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition x_equiv_result (q x z : nat -> int64) :=
  if Z.eqb (radix_value x mod feP) ((radix_value z*radix_value z*radix_value q) mod feP)
  then Int.one else Int.zero.
Definition x_equiv_entry_temps bp bq :=
  PTree.set _a (Vptr bp Ptrofs.zero) (PTree.set _x (Vptr bq Ptrofs.zero)
    (create_undef_temps (fn_temps f_secp256k1_gej_eq_x_var))).
Lemma x_equiv_function_ok : fn_okb f_secp256k1_gej_eq_x_var = true.
Proof. vm_compute;reflexivity. Qed.
Lemma x_equiv_function_entry m ma mi bp bq br br2 :
  Mem.alloc m 0 40 = (ma,br) -> Mem.alloc ma 0 40 = (mi,br2) ->
  function_entry2 secp_ge f_secp256k1_gej_eq_x_var [Vptr bq Ptrofs.zero;Vptr bp Ptrofs.zero] m
    (x_equiv_helper_env br br2) (x_equiv_entry_temps bp bq) mi.
Proof.
  intros HR HR2. destruct (fn_okb_true _ x_equiv_function_ok) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
  eapply alloc_variables_cons with (m1:=ma) (b1:=br);[exact HR|].
  eapply alloc_variables_cons with (m1:=mi) (b1:=br2);[exact HR2|constructor].
Qed.
Lemma x_equiv_function_blocks br br2 : blocks_of_env secp_ge (x_equiv_helper_env br br2) =
  [(br2,0,40);(br,0,40)].
Proof. reflexivity. Qed.

Theorem eval_x_equiv_function q x z m bp bq :
  square_input_bounds q -> square_input_bounds x -> square_input_bounds z -> bp<>bq ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 80 (words5 z) -> fe_at m bq 0 (words5 q) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bq 0 40 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_eq_x_var)
      [Vptr bq Ptrofs.zero;Vptr bp Ptrofs.zero] E0 mf (Vint (x_equiv_result q x z)) /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bq 0 40 Cur Freeable /\
    lframe (fun b _ => b<>bp /\ b<>bq) m mf.
Proof.
  intros BQ BX BZ HPQ HX HZ HQ HFP HFQ.
  destruct (Mem.alloc m 0 40) as [ma br] eqn:AR.
  destruct (Mem.alloc ma 0 40) as [mi br2] eqn:AR2.
  assert (HVP : Mem.valid_block m bp) by (eapply Mem.perm_valid_block;apply (HFP 0);lia).
  assert (HVQ : Mem.valid_block m bq) by (eapply Mem.perm_valid_block;apply (HFQ 0);lia).
  assert (HRP : br<>bp).
  { intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ AR);rewrite HE;exact HVP. }
  assert (HRQ : br<>bq).
  { intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ AR);rewrite HE;exact HVQ. }
  assert (HR2P : br2<>bp).
  { intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ AR2);rewrite HE.
    eapply Mem.valid_block_alloc;eassumption. }
  assert (HR2Q : br2<>bq).
  { intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ AR2);rewrite HE.
    eapply Mem.valid_block_alloc;eassumption. }
  assert (HR2R : br2<>br).
  { intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ AR2);rewrite HE.
    eapply Mem.valid_new_block;exact AR. }
  assert (FA : lframe (fun _ _ => True) m mi).
  { eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption. }
  pose proof (field_at_lframe m mi bp 0 _ _ HX FA ltac:(intros;exact I)) as XI.
  pose proof (field_at_lframe m mi bp 80 _ _ HZ FA ltac:(intros;exact I)) as ZI.
  pose proof (field_at_lframe m mi bq 0 _ _ HQ FA ltac:(intros;exact I)) as QI.
  pose proof (curve_keep_free _ m mi bp 128 ltac:(lia) HFP FA ltac:(intros;exact I)) as PFI.
  pose proof (curve_keep_free _ m mi bq 40 ltac:(lia) HFQ FA ltac:(intros;exact I)) as QFI.
  assert (RFI : Mem.range_perm mi br 0 40 Cur Freeable).
  { intros pos HPos;eapply Mem.perm_alloc_1;[exact AR2|]. eapply Mem.perm_alloc_2;eassumption. }
  assert (R2FI : Mem.range_perm mi br2 0 40 Cur Freeable).
  { intros pos HPos;eapply Mem.perm_alloc_2;eassumption. }
  assert (HA : (x_equiv_entry_temps bp bq)!_a = Some (Vptr bp Ptrofs.zero)) by (apply PTree.gss).
  assert (HQt : (x_equiv_entry_temps bp bq)!_x = Some (Vptr bq Ptrofs.zero)).
  { unfold x_equiv_entry_temps;rewrite PTree.gso by discriminate;apply PTree.gss. }
  destruct (exec_x_equiv_body_owned q x z (x_equiv_entry_temps bp bq) mi bp bq br br2
    BQ BX BZ HPQ HRP HRQ HR2P HR2Q HR2R HA HQt XI ZI QI PFI QFI RFI R2FI)
    as (mo & HB & PFO & QFO & RFO & R2FO & FB).
  change (Clight2.exec_stmt secp_ge (x_equiv_helper_env br br2) (x_equiv_entry_temps bp bq) mi
    (fn_body f_secp256k1_gej_eq_x_var) E0
    (PTree.set _t'1 (Vint (x_equiv_result q x z)) (x_equiv_entry_temps bp bq)) mo
    (Out_return (Some (Vint (x_equiv_result q x z),tint)))) in HB.
  destruct (free_list_exists [(br2,0,40);(br,0,40)] mo) as (mf & HFree & HU).
  - cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi [HE|[HE|HE]];[inversion HE;subst;exact R2FO|inversion HE;subst;exact RFO|contradiction].
  - assert (FF : lframe (fun b _ => b<>br /\ b<>br2) mo mf).
    { eapply lframe_implies;[apply lframe_unchanged;exact HU|].
      intros b pos [HNR HNR2] HV;cbn;intuition congruence. }
    pose proof (curve_keep_free _ mo mf bp 128 ltac:(lia) PFO FF ltac:(intro pos;split;congruence)) as PFF.
    pose proof (curve_keep_free _ mo mf bq 40 ltac:(lia) QFO FF ltac:(intro pos;split;congruence)) as QFF.
    exists mf. split.
    + eapply eval_funcall_internal with (e:=x_equiv_helper_env br br2)
        (le1:=x_equiv_entry_temps bp bq)
        (le2:=PTree.set _t'1 (Vint (x_equiv_result q x z)) (x_equiv_entry_temps bp bq))
        (m1:=mi) (m2:=mo) (out:=Out_return (Some (Vint (x_equiv_result q x z),tint))).
      * exact (x_equiv_function_entry m ma mi bp bq br br2 AR AR2).
      * exact HB.
      * split;[discriminate|reflexivity].
      * rewrite x_equiv_function_blocks;exact HFree.
    + split;[exact PFF|]. split;[exact QFF|].
      assert (HF : lframe (fun b _ => Mem.valid_block m b /\ b<>bp /\ b<>bq) m mf).
      { eapply lframe_trans.
        - eapply lframe_implies;[exact FA|]. intros;exact I.
        - eapply lframe_trans.
          + eapply lframe_implies;[exact FB|]. intros b pos (HV & HNP & HNQ) HV'.
            split;[exact HNP|]. split;[exact HNQ|]. split;intro HE;subst b.
            * apply (Mem.fresh_block_alloc _ _ _ _ _ AR);exact HV.
            * apply (Mem.fresh_block_alloc _ _ _ _ _ AR2);eapply Mem.valid_block_alloc;eassumption.
          + eapply lframe_implies;[exact FF|]. intros b pos (HV & HNP & HNQ) HV'.
            split;intro HE;subst b.
            * apply (Mem.fresh_block_alloc _ _ _ _ _ AR);exact HV.
            * apply (Mem.fresh_block_alloc _ _ _ _ _ AR2);eapply Mem.valid_block_alloc;eassumption. }
      eapply lframe_implies;[exact HF|]. intros b pos [HNP HNQ] HV;repeat split;assumption.
Qed.
Print Assumptions eval_x_equiv_function.
