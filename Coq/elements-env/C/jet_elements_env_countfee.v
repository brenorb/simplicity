(** Execution of [countFeeOutputs(rawTx)] (elements/env.c):
      for (i = 0; i < rawTx->numOutputs; ++i) result += isFee(&rawTx->output[i]);
    The result is the number of fee outputs of the raw transaction. *)
From Coq Require Import ZArith List Lia PeanoNat Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_be32_exec.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_copyrawamt C.jet_elements_env_isfee.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Local Notation ROUT := (Tstruct _rawElementsOutput noattr).
Local Notation RTX := (Tstruct _rawElementsTransaction noattr).

Lemma sha_isFee_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _isFee = Some (sha_symbol_block _isFee).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_isFee_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _isFee) Ptrofs.zero) =
    Some (Internal f_isFee).
Proof. vm_compute; reflexivity. Qed.

Lemma envu_rawElementsTransaction_txid : envu_field_at _rawElementsTransaction _txid 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawElementsTransaction_input : envu_field_at _rawElementsTransaction _input 8.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawElementsTransaction_output : envu_field_at _rawElementsTransaction _output 16.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawElementsTransaction_numInputs : envu_field_at _rawElementsTransaction _numInputs 24.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawElementsTransaction_numOutputs : envu_field_at _rawElementsTransaction _numOutputs 28.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawElementsTransaction_version : envu_field_at _rawElementsTransaction _version 32.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawElementsTransaction_lockTime : envu_field_at _rawElementsTransaction _lockTime 36.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.

Definition cf_s1 : statement :=
  ltac:(let b := eval cbv delta [f_countFeeOutputs fn_body] beta iota in (fn_body f_countFeeOutputs) in
        lazymatch b with Ssequence _ (Ssequence (Ssequence _ (Sloop ?s1 _)) _) => exact s1 end).
Definition cf_s2 : statement :=
  ltac:(let b := eval cbv delta [f_countFeeOutputs fn_body] beta iota in (fn_body f_countFeeOutputs) in
        lazymatch b with Ssequence _ (Ssequence (Ssequence _ (Sloop _ ?s2)) _) => exact s2 end).

Lemma cf_body_shape :
  fn_body f_countFeeOutputs =
    Ssequence (Sset _result (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Ssequence
        (Ssequence (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong)) (Sloop cf_s1 cf_s2))
        (Sreturn (Some (Etempvar _result tulong)))).
Proof. reflexivity. Qed.

Local Opaque sha_ge.

(** What [isFee] reads of one raw output. *)
Record fee_out : Type := { fo_len : int; fo_va : val; fo_vv : val; fo_fa : option int; fo_fv : option int }.

Definition raw_out_fee (m : mem) (bo : block) (o : Z) (d : fee_out) : Prop :=
  Mem.load Mint32 m bo (o + 32) = Some (Vint (fo_len d)) /\
  Mem.load Mptr m bo o = Some (fo_va d) /\ raw_first m (fo_va d) (fo_fa d) /\
  Mem.load Mptr m bo (o + 8) = Some (fo_vv d) /\ raw_first m (fo_vv d) (fo_fv d).

Definition fee_flag (d : fee_out) : bool := is_fee (fo_len d) (fo_fa d) (fo_fv d).

Fixpoint fee_count (data : nat -> fee_out) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => fee_count data k' + (if fee_flag (data k') then 1 else 0)
  end.

Lemma fee_count_range data k : 0 <= fee_count data k <= Z.of_nat k.
Proof. induction k as [|k IH]; cbn [fee_count]; [lia|]. destruct (fee_flag (data k)); lia. Qed.

Lemma cf_ptr_index ob sz k : 0 <= ob -> 0 <= sz <= 1000 -> 0 <= k <= 4294967295 ->
  ob + sz * k <= 18446744073709551615 ->
  Ptrofs.add (Ptrofs.repr ob) (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_int64 (Int64.repr k))) =
    Ptrofs.repr (ob + sz * k).
Proof.
  intros Ho Hs Hk Hb. unfold Ptrofs.of_int64.
  rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  unfold Ptrofs.add, Ptrofs.mul.
  rewrite (Ptrofs.unsigned_repr sz), (Ptrofs.unsigned_repr k), (Ptrofs.unsigned_repr ob)
    by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
  rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; nia). reflexivity.
Qed.

Section CountFee.
Variables (m : mem) (btx : block) (otx : Z) (nout : int) (bo : block) (oo : Z) (data : nat -> fee_out).
Hypothesis Hotx : 0 <= otx /\ otx + 40 <= Ptrofs.max_unsigned.
Hypothesis HNo : Mem.load Mint32 m btx (otx + 28) = Some (Vint nout).

Let n : nat := Z.to_nat (Int.unsigned nout).
Let txv := Vptr btx (Ptrofs.repr otx).

Hypothesis HOut : (0 < n)%nat -> Mem.load Mptr m btx (otx + 16) = Some (Vptr bo (Ptrofs.repr oo)).
Hypothesis Hoo : 0 <= oo /\ oo + 72 * Int.unsigned nout <= Ptrofs.max_unsigned.
Hypothesis HData : forall i, (i < n)%nat -> raw_out_fee m bo (oo + 72 * Z.of_nat i) (data i).

Lemma cf_n : Z.of_nat n = Int.unsigned nout.
Proof. unfold n. apply Z2Nat.id. pose proof (Int.unsigned_range nout). lia. Qed.

Definition cf_inv (k : nat) (le : temp_env) : Prop :=
  le!_i = Some (Vlong (Int64.repr (Z.of_nat k))) /\
  le!_result = Some (Vlong (Int64.repr (fee_count data k))) /\
  le!_rawTx = Some txv.

Lemma cf_numOutputs le :
  le!_rawTx = Some txv ->
  eval_expr sha_ge empty_env le m (Efield (Ederef (Etempvar _rawTx (tptr RTX)) RTX) _numOutputs tuint) (Vint nout).
Proof.
  intros HT. eapply eval_envu_field_value;
    [reflexivity|exact envu_rawElementsTransaction_numOutputs|reflexivity
    |apply eval_envu_deref_struct; exact HT|].
  rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|exact HNo].
Qed.

Lemma cf_ltu k : 0 <= k <= Int.unsigned nout ->
  Int64.ltu (Int64.repr k) (Int64.repr (Int.unsigned nout)) = if zlt k (Int.unsigned nout) then true else false.
Proof.
  intros Hk. pose proof (Int.unsigned_range_2 nout) as HR. change Int.max_unsigned with 4294967295 in HR.
  unfold Int64.ltu.
  rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia). reflexivity.
Qed.

Lemma cf_exit le : cf_inv n le ->
  exists le', cf_inv n le' /\
    Clight2.exec_stmt sha_ge empty_env le m (Sloop cf_s1 cf_s2) E0 le' m Out_normal.
Proof.
  intros (Hi & Hr & Ht). pose proof (Int.unsigned_range nout) as HR.
  exists (PTree.set _t'3 (Vint nout) le). split.
  { unfold cf_inv. rewrite !PTree.gso by discriminate. repeat split; assumption. }
  eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
  cbv delta [cf_s1] beta iota.
  eapply exec_Sseq_2; [|discriminate].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'3 (Vint nout) le) (m1 := m).
  - apply exec_Sset. apply cf_numOutputs. exact Ht.
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
    + eapply eval_Ebinop; [apply eval_Etempvar; rewrite PTree.gso by discriminate; exact Hi
                          |apply eval_Etempvar; apply PTree.gss|].
      change (Some (Val.of_bool (Int64.ltu (Int64.repr (Z.of_nat n)) (Int64.repr (Int.unsigned nout)))) =
              Some (Vint Int.zero)).
      rewrite cf_ltu by (rewrite cf_n; lia). rewrite cf_n, zlt_false by lia. reflexivity.
    + reflexivity.
    + apply exec_Sbreak.
Qed.

Lemma cf_step k le : (k < n)%nat -> cf_inv k le ->
  exists le1 le2, cf_inv (S k) le2 /\
    Clight2.exec_stmt sha_ge empty_env le m cf_s1 E0 le1 m Out_normal /\
    Clight2.exec_stmt sha_ge empty_env le1 m cf_s2 E0 le2 m Out_normal.
Proof.
  intros Hk (Hi & Hr & Ht). pose proof cf_n as Hn.
  pose proof (Int.unsigned_range_2 nout) as HR. change Int.max_unsigned with 4294967295 in HR.
  destruct (HData k Hk) as (DL & DA & DRa & DV & DRv).
  pose proof (fee_count_range data k) as HCr.
  set (flag := fee_flag (data k)).
  set (leA := PTree.set _t'3 (Vint nout) le).
  set (leB := PTree.set _t'2 (Vptr bo (Ptrofs.repr oo)) leA).
  set (leC := PTree.set _t'1 (Vint (b2i flag)) leB).
  set (le1 := PTree.set _result (Vlong (Int64.repr (fee_count data (S k)))) leC).
  set (le2 := PTree.set _i (Vlong (Int64.repr (Z.of_nat (S k)))) le1).
  exists le1, le2. split; [|split].
  - unfold cf_inv, le2, le1, leC, leB, leA. split; [apply PTree.gss|].
    split; [rewrite PTree.gso by discriminate; apply PTree.gss|].
    rewrite !PTree.gso by discriminate. exact Ht.
  - cbv delta [cf_s1] beta iota.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leA) (m1 := m).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leA) (m1 := m).
      * apply exec_Sset. apply cf_numOutputs. exact Ht.
      * eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
        -- eapply eval_Ebinop; [apply eval_Etempvar; unfold leA; rewrite PTree.gso by discriminate; exact Hi
                                |apply eval_Etempvar; apply PTree.gss|].
           change (Some (Val.of_bool (Int64.ltu (Int64.repr (Z.of_nat k)) (Int64.repr (Int.unsigned nout)))) =
                   Some (Vint Int.one)).
           rewrite cf_ltu by lia. rewrite zlt_true by lia. reflexivity.
        -- reflexivity.
        -- apply exec_Sskip.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leC) (m1 := m).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leB) (m1 := m).
        -- apply exec_Sset. eapply eval_envu_field_value;
             [reflexivity|exact envu_rawElementsTransaction_output|reflexivity
             |apply eval_envu_deref_struct; unfold leA; rewrite PTree.gso by discriminate; exact Ht|].
           rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|]. apply HOut. lia.
        -- change leC with (set_opttemp (Some _t'1) (Vint (b2i flag)) leB).
           eapply exec_Scall with (vf := Vptr (sha_symbol_block _isFee) Ptrofs.zero)
             (vargs := [Vptr bo (Ptrofs.repr (oo + 72 * Z.of_nat k))]) (f := Internal f_isFee).
           ++ reflexivity.
           ++ eapply eval_Elvalue; [apply eval_Evar_global; [apply PTree.gempty|exact sha_isFee_symbol]|].
              apply deref_loc_reference; reflexivity.
           ++ eapply eval_Econs with (v1 := Vptr bo (Ptrofs.repr (oo + 72 * Z.of_nat k)));
                [|reflexivity|apply eval_Enil].
              eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss
                                  |apply eval_Etempvar; unfold leB, leA; rewrite !PTree.gso by discriminate; exact Hi|].
              rewrite <- (cf_ptr_index oo 72 (Z.of_nat k))
                by (change Ptrofs.max_unsigned with 18446744073709551615 in *; lia).
              rewrite <- fee_sizeof_ROUT. reflexivity.
           ++ exact sha_isFee_funct.
           ++ reflexivity.
           ++ unfold flag, fee_flag.
              apply (eval_isFee m bo (oo + 72 * Z.of_nat k) _ (fo_va (data k)) (fo_vv (data k)));
                try assumption; lia.
      * apply exec_Sset.
        eapply eval_Ebinop; [apply eval_Etempvar; unfold leC, leB, leA; rewrite !PTree.gso by discriminate; exact Hr
                            |apply eval_Etempvar; apply PTree.gss|].
        cbn [fee_count]. fold flag.
        assert (HAdd : Int64.add (Int64.repr (fee_count data k)) (Int64.repr (Int.unsigned (b2i flag))) =
                       Int64.repr (fee_count data k + (if flag then 1 else 0))).
        { unfold Int64.add.
          rewrite (Int64.unsigned_repr (fee_count data k))
            by (change Int64.max_unsigned with 18446744073709551615; lia).
          destruct flag; reflexivity. }
        rewrite <- HAdd. reflexivity.
  - cbv delta [cf_s2] beta iota. apply exec_Sset.
    eapply eval_Ebinop; [apply eval_Etempvar; unfold le1, leC, leB, leA; rewrite !PTree.gso by discriminate; exact Hi
                        |apply eval_Econst_int|].
    assert (HAdd : Int64.add (Int64.repr (Z.of_nat k)) (Int64.repr (Int.signed (Int.repr 1))) =
                   Int64.repr (Z.of_nat (S k))).
    { unfold Int64.add.
      rewrite (Int64.unsigned_repr (Z.of_nat k)) by (change Int64.max_unsigned with 18446744073709551615; lia).
      change (Int64.unsigned (Int64.repr (Int.signed (Int.repr 1)))) with 1. f_equal. lia. }
    rewrite <- HAdd. reflexivity.
Qed.

Lemma cf_loop d : forall k le, (k + d = n)%nat -> cf_inv k le ->
  exists le', cf_inv n le' /\
    Clight2.exec_stmt sha_ge empty_env le m (Sloop cf_s1 cf_s2) E0 le' m Out_normal.
Proof.
  induction d as [|d IH]; intros k le Hkd HI.
  - replace k with n in HI by lia. exact (cf_exit le HI).
  - destruct (cf_step k le ltac:(lia) HI) as (le1 & le2 & HI2 & H1 & H2).
    destruct (IH (S k) le2 ltac:(lia) HI2) as (le' & HI' & HE).
    exists le'. split; [exact HI'|].
    change E0 with (E0 ** E0 ** E0).
    eapply exec_Sloop_loop; [exact H1|constructor|exact H2|exact HE].
Qed.

Theorem eval_countFeeOutputs :
  Clight2.eval_funcall sha_ge m (Internal f_countFeeOutputs) [txv] E0 m
    (Vlong (Int64.repr (fee_count data n))).
Proof.
  set (le0 := PTree.set _rawTx txv (create_undef_temps (fn_temps f_countFeeOutputs))).
  set (leR := PTree.set _result (Vlong (Int64.repr 0)) le0).
  set (leI := PTree.set _i (Vlong (Int64.repr 0)) leR).
  destruct (cf_loop n 0%nat leI eq_refl) as (le' & (Hi & Hr & Ht) & HE).
  { unfold cf_inv, leI, leR, le0. split; [apply PTree.gss|].
    split; [rewrite PTree.gso by discriminate; apply PTree.gss|].
    rewrite !PTree.gso by discriminate. apply PTree.gss. }
  eapply eval_funcall_internal with (e := empty_env) (le1 := le0) (m1 := m) (m2 := m)
    (le2 := le') (out := Out_return (Some (Vlong (Int64.repr (fee_count data n)), tulong))).
  - apply function_entry2_intro.
    + apply list_norepet_nil.
    + repeat constructor; simpl; intuition discriminate.
    + intros x0 y0 HX HY; cbn in HX, HY; intuition (subst; discriminate).
    + apply alloc_variables_nil.
    + reflexivity.
  - rewrite cf_body_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leR) (m1 := m).
    { apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le') (m1 := m).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leI) (m1 := m).
      * apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
      * exact HE.
    + apply exec_Sreturn_some. apply eval_Etempvar. exact Hr.
  - cbn. split; [discriminate|reflexivity].
  - reflexivity.
Qed.
End CountFee.
