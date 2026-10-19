(** Execution of [isFee(output)] (elements/env.c):
      0 == output->scriptPubKey.len &&
      NULL != output->asset && 0x01 == output->asset[0] &&
      NULL != output->value && 0x01 == output->value[0]
    with C's short-circuit evaluation: a NULL asset or value is never
    dereferenced. *)
From Coq Require Import ZArith List Lia PeanoNat Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_be32_exec.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_copyrawamt.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Local Notation ROUT := (Tstruct _rawElementsOutput noattr).
Local Notation RBUF := (Tstruct _rawElementsBuffer noattr).

Lemma envu_rawElementsOutput_asset : envu_field_at _rawElementsOutput _asset 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawElementsOutput_value : envu_field_at _rawElementsOutput _value 8.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawElementsOutput_nonce : envu_field_at _rawElementsOutput _nonce 16.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawElementsOutput_scriptPubKey : envu_field_at _rawElementsOutput _scriptPubKey 24.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawElementsOutput_surjectionProof : envu_field_at _rawElementsOutput _surjectionProof 40.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawElementsOutput_rangeProof : envu_field_at _rawElementsOutput _rangeProof 56.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma fee_sizeof_ROUT : sizeof sha_ge ROUT = 72.
Proof. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

Definition b2i (c : bool) : int := if c then Int.one else Int.zero.

(** A raw optional byte string: NULL, or a pointer whose first byte is known. *)
Definition raw_first (m : mem) (v : val) (first : option int) : Prop :=
  (v = Vlong Int64.zero /\ first = None) \/
  (exists b o x, v = Vptr b o /\
     Mem.load Mint8unsigned m b (Ptrofs.unsigned o) = Some (Vint x) /\ first = Some x).

Definition opt_some {A} (f : option A) : bool := match f with Some _ => true | None => false end.
Definition opt_is1 (f : option int) : bool :=
  match f with Some x => Int.eq (Int.repr 1) x | None => false end.

Definition is_fee (len : int) (fa fv : option int) : bool :=
  Int.eq (Int.repr 0) len && opt_is1 fa && opt_is1 fv.

(** [(bool)(NULL != p)] for a temporary [p]. *)
Lemma eval_ne_null e le m id v first :
  le!id = Some v -> raw_first m v first ->
  eval_expr sha_ge e le m
    (Ecast (Ebinop One (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
       (Etempvar id (tptr tuchar)) tint) tbool)
    (Vint (b2i (opt_some first))).
Proof.
  intros Hid [(-> & ->)|(b & o & x & -> & HL & ->)].
  - eapply eval_Ecast.
    + eapply eval_Ebinop; [eapply eval_Ecast; [apply eval_Econst_int|reflexivity]
                          |apply eval_Etempvar; exact Hid|reflexivity].
    + reflexivity.
  - eapply eval_Ecast with (v1 := Vtrue).
    + eapply eval_Ebinop; [eapply eval_Ecast; [apply eval_Econst_int|reflexivity]
                          |apply eval_Etempvar; exact Hid|].
      pose proof (load_weak_valid _ _ _ _ HL) as HW. unfold Mem.weak_valid_pointer in HW.
      unfold sem_binary_operation, sem_cmp. cbn [classify_cmp typeof tptr typeconv remove_attributes].
      cbn. unfold cmp_ptr, Val.cmplu_bool. cbn. rewrite HW. reflexivity.
    + reflexivity.
Qed.

Lemma eval_byte0 e le m id b o x :
  le!id = Some (Vptr b o) ->
  Mem.load Mint8unsigned m b (Ptrofs.unsigned o) = Some (Vint x) ->
  eval_expr sha_ge e le m
    (Ederef (Ebinop Oadd (Etempvar id (tptr tuchar)) (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
    (Vint x).
Proof.
  intros HR HL. pose proof (Ptrofs.unsigned_range_2 o) as HO. eapply eval_Elvalue.
  - eapply eval_Ederef. eapply eval_Ebinop; [apply eval_Etempvar; exact HR|apply eval_Econst_int|reflexivity].
  - eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv.
    rewrite ptr_byte_offset by lia. rewrite Z.add_0_r. exact HL.
Qed.

(** [(bool)(1 == x)] for a byte temporary. *)
Lemma eval_is1 e le m id x :
  le!id = Some (Vint x) ->
  eval_expr sha_ge e le m
    (Ecast (Ebinop Oeq (Econst_int (Int.repr 1) tint) (Etempvar id tuchar) tint) tbool)
    (Vint (b2i (Int.eq (Int.repr 1) x))).
Proof.
  intros Hid. destruct (Int.eq (Int.repr 1) x) eqn:HE.
  - eapply eval_Ecast with (v1 := Vtrue); [|reflexivity].
    eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; exact Hid|].
    cbn. unfold Cop.sem_cmp, Cop.sem_binarith. cbn. rewrite HE. reflexivity.
  - eapply eval_Ecast with (v1 := Vfalse); [|reflexivity].
    eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; exact Hid|].
    cbn. unfold Cop.sem_cmp, Cop.sem_binarith. cbn. rewrite HE. reflexivity.
Qed.

Section IsFee.
Variables (e : env) (bout : block) (oout : Z).
Hypothesis Hoout : 0 <= oout /\ oout + 72 <= Ptrofs.max_unsigned.

Let outv := Vptr bout (Ptrofs.repr oout).

Lemma fee_ptr_field le m fld delta v :
  le!_output = Some outv -> envu_field_at _rawElementsOutput fld delta -> 0 <= delta <= 64 ->
  Mem.load Mptr m bout (oout + delta) = Some v ->
  eval_expr sha_ge e le m (Efield (Ederef (Etempvar _output (tptr ROUT)) ROUT) fld (tptr tuchar)) v.
Proof.
  intros HO HF Hd HL. eapply eval_envu_field_value;
    [reflexivity|exact HF|reflexivity|apply eval_envu_deref_struct; exact HO|].
  rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|exact HL].
Qed.

(** [c && NULL != output->fld], evaluated only when [c]. *)
Lemma fee_notnull_stage le m cond vc (c : bool) (tp tres fld : ident) delta v first :
  eval_expr sha_ge e le m cond vc -> bool_val vc (typeof cond) m = Some c ->
  le!_output = Some outv -> tp <> _output -> tres <> _output ->
  envu_field_at _rawElementsOutput fld delta -> 0 <= delta <= 64 ->
  Mem.load Mptr m bout (oout + delta) = Some v -> raw_first m v first ->
  exists le',
    Clight2.exec_stmt sha_ge e le m
      (Sifthenelse cond
         (Ssequence
            (Sset tp (Efield (Ederef (Etempvar _output (tptr ROUT)) ROUT) fld (tptr tuchar)))
            (Sset tres (Ecast (Ebinop One (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                                 (Etempvar tp (tptr tuchar)) tint) tbool)))
         (Sset tres (Econst_int (Int.repr 0) tint)))
      E0 le' m Out_normal /\
    le'!tres = Some (Vint (b2i (c && opt_some first))) /\ le'!_output = Some outv.
Proof.
  intros HC HB HO Ntp Ntr HF Hd HL HR.
  apply not_eq_sym in Ntp. apply not_eq_sym in Ntr. destruct c.
  - exists (PTree.set tres (Vint (b2i (opt_some first))) (PTree.set tp v le)).
    split; [|split].
    + eapply exec_Sifthenelse with (v1 := vc) (b := true); [exact HC|exact HB|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_Sset. exact (fee_ptr_field _ _ fld delta _ HO HF Hd HL).
      * apply exec_Sset. eapply eval_ne_null; [apply PTree.gss|exact HR].
    + apply PTree.gss.
    + rewrite !PTree.gso by assumption. exact HO.
  - exists (PTree.set tres (Vint (Int.repr 0)) le). split; [|split].
    + eapply exec_Sifthenelse with (v1 := vc) (b := false); [exact HC|exact HB|].
      apply exec_Sset. apply eval_Econst_int.
    + apply PTree.gss.
    + rewrite PTree.gso by assumption. exact HO.
Qed.

(** [c && 0x01 == output->fld[0]], the dereference only when [c]. *)
Lemma fee_is1_stage le m cond vc (c : bool) (tp tb tres fld : ident) delta v first :
  eval_expr sha_ge e le m cond vc -> bool_val vc (typeof cond) m = Some c ->
  le!_output = Some outv -> tp <> _output -> tb <> _output -> tres <> _output -> tb <> tp ->
  envu_field_at _rawElementsOutput fld delta -> 0 <= delta <= 64 ->
  Mem.load Mptr m bout (oout + delta) = Some v -> raw_first m v first ->
  (c = true -> opt_some first = true) ->
  exists le',
    Clight2.exec_stmt sha_ge e le m
      (Sifthenelse cond
         (Ssequence
            (Sset tp (Efield (Ederef (Etempvar _output (tptr ROUT)) ROUT) fld (tptr tuchar)))
            (Ssequence
               (Sset tb (Ederef (Ebinop Oadd (Etempvar tp (tptr tuchar))
                                   (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
               (Sset tres (Ecast (Ebinop Oeq (Econst_int (Int.repr 1) tint)
                                    (Etempvar tb tuchar) tint) tbool))))
         (Sset tres (Econst_int (Int.repr 0) tint)))
      E0 le' m Out_normal /\
    le'!tres = Some (Vint (b2i (c && opt_is1 first))) /\ le'!_output = Some outv.
Proof.
  intros HC HB HO Ntp Ntb Ntr Nbp HF Hd HL HR Hsome.
  apply not_eq_sym in Ntp. apply not_eq_sym in Ntb. apply not_eq_sym in Ntr. destruct c.
  - destruct HR as [(-> & ->)|(b & o & x & -> & HLx & ->)]; [specialize (Hsome eq_refl); discriminate|].
    exists (PTree.set tres (Vint (b2i (Int.eq (Int.repr 1) x)))
      (PTree.set tb (Vint x) (PTree.set tp (Vptr b o) le))).
    split; [|split].
    + eapply exec_Sifthenelse with (v1 := vc) (b := true); [exact HC|exact HB|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * apply exec_Sset. exact (fee_ptr_field _ _ fld delta _ HO HF Hd HL).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply exec_Sset. eapply eval_byte0; [apply PTree.gss|exact HLx].
        -- apply exec_Sset. apply eval_is1. apply PTree.gss.
    + apply PTree.gss.
    + rewrite !PTree.gso by assumption. exact HO.
  - exists (PTree.set tres (Vint (Int.repr 0)) le). split; [|split].
    + eapply exec_Sifthenelse with (v1 := vc) (b := false); [exact HC|exact HB|].
      apply exec_Sset. apply eval_Econst_int.
    + apply PTree.gss.
    + rewrite PTree.gso by assumption. exact HO.
Qed.

Lemma fee_bool_temp le m id (c : bool) :
  le!id = Some (Vint (b2i c)) ->
  eval_expr sha_ge e le m (Etempvar id tint) (Vint (b2i c)) /\
  bool_val (Vint (b2i c)) (typeof (Etempvar id tint)) m = Some c.
Proof. intros H. split; [apply eval_Etempvar; exact H|destruct c; reflexivity]. Qed.
End IsFee.

Theorem eval_isFee m bout oout (len : int) (va vv : val) (fa fv : option int) :
  0 <= oout -> oout + 72 <= Ptrofs.max_unsigned ->
  Mem.load Mint32 m bout (oout + 32) = Some (Vint len) ->
  Mem.load Mptr m bout oout = Some va -> raw_first m va fa ->
  Mem.load Mptr m bout (oout + 8) = Some vv -> raw_first m vv fv ->
  Clight2.eval_funcall sha_ge m (Internal f_isFee) [Vptr bout (Ptrofs.repr oout)] E0 m
    (Vint (b2i (is_fee len fa fv))).
Proof.
  intros Ho0 HoM HLen HA HRa HV HRv.
  assert (Hoout : 0 <= oout /\ oout + 72 <= Ptrofs.max_unsigned) by lia.
  set (outv := Vptr bout (Ptrofs.repr oout)).
  set (le0 := PTree.set _output outv (create_undef_temps (fn_temps f_isFee))).
  set (le10 := PTree.set _t'10 (Vint len) le0).
  set (c0 := Int.eq (Int.repr 0) len).
  assert (HA0 : Mem.load Mptr m bout (oout + 0) = Some va) by (rewrite Z.add_0_r; exact HA).
  (* stage 1 *)
  assert (HC0 : eval_expr sha_ge empty_env le10 m
    (Ebinop Oeq (Econst_int (Int.repr 0) tint) (Etempvar _t'10 tuint) tint) (Val.of_bool c0)).
  { eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; apply PTree.gss|].
    cbn. unfold Cop.sem_cmp, Cop.sem_binarith. cbn. fold c0. reflexivity. }
  assert (HB0 : bool_val (Val.of_bool c0) tint m = Some c0) by (destruct c0; reflexivity).
  assert (HO10 : le10!_output = Some outv) by reflexivity.
  destruct (fee_notnull_stage empty_env bout oout Hoout le10 m _ _ c0 _t'11 _t'1 _asset 0 va fa
    HC0 HB0 HO10 ltac:(discriminate) ltac:(discriminate) envu_rawElementsOutput_asset ltac:(lia) HA0 HRa)
    as (le1 & HE1 & Ht1 & HO1).
  (* stage 2 *)
  destruct (fee_bool_temp empty_env le1 m _t'1 _ Ht1) as [HC1 HB1].
  destruct (fee_is1_stage empty_env bout oout Hoout le1 m _ _ _ _t'8 _t'9 _t'2 _asset 0 va fa
    HC1 HB1 HO1 ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    envu_rawElementsOutput_asset ltac:(lia) HA0 HRa
    ltac:(intros H; apply andb_true_iff in H; exact (proj2 H)))
    as (le2 & HE2 & Ht2 & HO2).
  (* stage 3 *)
  destruct (fee_bool_temp empty_env le2 m _t'2 _ Ht2) as [HC2 HB2].
  destruct (fee_notnull_stage empty_env bout oout Hoout le2 m _ _ _ _t'7 _t'3 _value 8 vv fv
    HC2 HB2 HO2 ltac:(discriminate) ltac:(discriminate) envu_rawElementsOutput_value ltac:(lia) HV HRv)
    as (le3 & HE3 & Ht3 & HO3).
  (* stage 4 *)
  destruct (fee_bool_temp empty_env le3 m _t'3 _ Ht3) as [HC3 HB3].
  destruct (fee_is1_stage empty_env bout oout Hoout le3 m _ _ _ _t'5 _t'6 _t'4 _value 8 vv fv
    HC3 HB3 HO3 ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    envu_rawElementsOutput_value ltac:(lia) HV HRv
    ltac:(intros H; apply andb_true_iff in H; exact (proj2 H)))
    as (le4 & HE4 & Ht4 & HO4).
  assert (HFin : c0 && opt_some fa && opt_is1 fa && opt_some fv && opt_is1 fv = is_fee len fa fv).
  { unfold is_fee. fold c0. destruct c0, fa as [xa|], fv as [xv|]; cbn;
      rewrite ?andb_true_r, ?andb_false_r; reflexivity. }
  rewrite HFin in Ht4.
  eapply eval_funcall_internal with (e := empty_env) (le1 := le0) (m1 := m) (m2 := m)
    (le2 := le4) (out := Out_return (Some (Vint (b2i (is_fee len fa fv)), tint))).
  - apply function_entry2_intro.
    + apply list_norepet_nil.
    + repeat constructor; simpl; intuition discriminate.
    + intros x0 y0 HX HY; cbn in HX, HY; intuition (subst; discriminate).
    + apply alloc_variables_nil.
    + reflexivity.
  - unfold f_isFee. cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m); [|exact HE4].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m); [|exact HE3].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m); [|exact HE2].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le10) (m1 := m); [|exact HE1].
      apply exec_Sset.
      eapply eval_envu_field_value with (chunk := Mint32);
        [reflexivity|exact envu_rawElementsBuffer_len|reflexivity| |].
      * eapply eval_envu_field_struct;
          [reflexivity|exact envu_rawElementsOutput_scriptPubKey|apply eval_envu_deref_struct; reflexivity].
      * rewrite !envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|].
        replace (oout + 24 + 8) with (oout + 32) by lia. exact HLen.
    + apply exec_Sreturn_some. apply eval_Etempvar. exact Ht4.
  - cbn. split; [discriminate|]. destruct (is_fee len fa fv); reflexivity.
  - reflexivity.
Qed.
