(** Execution of [countTotalNullDataCodes(rawTx)] (elements/env.c):
      for (i = 0; i < rawTx->numOutputs; ++i)
        result += countNullDataCodes(&rawTx->output[i].scriptPubKey);
    The result is the total number of null-data push operations of the raw
    transaction, the size of the opcode allocation of
    [simplicity_elements_mallocTransaction]. *)
From Coq Require Import ZArith List Lia PeanoNat Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_be32_exec.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_isfee C.jet_elements_env_countfee.
Require Import C.jet_elements_env_nulldata_count.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Local Notation ROUT := (Tstruct _rawElementsOutput noattr).
Local Notation RBUF := (Tstruct _rawElementsBuffer noattr).
Local Notation RTX := (Tstruct _rawElementsTransaction noattr).

Lemma sha_countNullDataCodes_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _countNullDataCodes = Some (sha_symbol_block _countNullDataCodes).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_countNullDataCodes_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _countNullDataCodes) Ptrofs.zero) =
    Some (Internal f_countNullDataCodes).
Proof. vm_compute; reflexivity. Qed.

Definition ct_s1 : statement :=
  ltac:(let b := eval cbv delta [f_countTotalNullDataCodes fn_body] beta iota in (fn_body f_countTotalNullDataCodes) in
        lazymatch b with Ssequence _ (Ssequence (Ssequence _ (Sloop ?s1 _)) _) => exact s1 end).
Definition ct_s2 : statement :=
  ltac:(let b := eval cbv delta [f_countTotalNullDataCodes fn_body] beta iota in (fn_body f_countTotalNullDataCodes) in
        lazymatch b with Ssequence _ (Ssequence (Ssequence _ (Sloop _ ?s2)) _) => exact s2 end).

Lemma ct_body_shape :
  fn_body f_countTotalNullDataCodes =
    Ssequence (Sset _result (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Ssequence
        (Ssequence (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong)) (Sloop ct_s1 ct_s2))
        (Sreturn (Some (Etempvar _result tulong)))).
Proof. reflexivity. Qed.

Local Opaque sha_ge.

(** The script of one raw output. *)
Record nd_out : Type := { no_len : int; no_bb : block; no_ob : ptrofs; no_bs : list int }.

Definition raw_out_script (m : mem) (bo : block) (o : Z) (d : nd_out) : Prop :=
  Mem.load Mint32 m bo (o + 32) = Some (Vint (no_len d)) /\
  (0 < Int.unsigned (no_len d) -> Mem.load Mptr m bo (o + 24) = Some (Vptr (no_bb d) (no_ob d))) /\
  Ptrofs.unsigned (no_ob d) + Int.unsigned (no_len d) <= Ptrofs.max_unsigned /\
  (forall i, 0 <= i < Int.unsigned (no_len d) ->
     Mem.load Mint8unsigned m (no_bb d) (Ptrofs.unsigned (no_ob d) + i) =
       Some (Vint (nth (Z.to_nat i) (no_bs d) Int.zero))).

Definition nd_out_count (d : nd_out) : Z := nd_count (no_len d) (no_bs d).

Fixpoint nd_total (data : nat -> nd_out) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => nd_total data k' + nd_out_count (data k')
  end.

Lemma ct_i64_add a b : Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  unfold Int64.add. apply Int64.eqm_samerepr.
  apply Int64.eqm_add; apply Int64.eqm_sym, Int64.eqm_unsigned_repr.
Qed.

Section CountTotal.
Variables (m : mem) (btx : block) (otx : Z) (nout : int) (bo : block) (oo : Z) (data : nat -> nd_out).
Hypothesis Hotx : 0 <= otx /\ otx + 40 <= Ptrofs.max_unsigned.
Hypothesis HNo : Mem.load Mint32 m btx (otx + 28) = Some (Vint nout).

Let n : nat := Z.to_nat (Int.unsigned nout).
Let txv := Vptr btx (Ptrofs.repr otx).

Hypothesis HOut : (0 < n)%nat -> Mem.load Mptr m btx (otx + 16) = Some (Vptr bo (Ptrofs.repr oo)).
Hypothesis Hoo : 0 <= oo /\ oo + 72 * Int.unsigned nout <= Ptrofs.max_unsigned.
Hypothesis HData : forall i, (i < n)%nat -> raw_out_script m bo (oo + 72 * Z.of_nat i) (data i).

Lemma ct_n : Z.of_nat n = Int.unsigned nout.
Proof. unfold n. apply Z2Nat.id. pose proof (Int.unsigned_range nout). lia. Qed.

Lemma ct_total_range k : (k <= n)%nat -> 0 <= nd_total data k <= Z.of_nat k * 4294967295.
Proof.
  induction k as [|k IH]; intros Hk; cbn [nd_total]; [lia|].
  destruct (HData k ltac:(lia)) as (DL & DB & DM & DBs).
  assert (HB : 0 <= nd_count (no_len (data k)) (no_bs (data k)) <= Int.unsigned (no_len (data k))).
  { eapply nd_count_bound; eassumption. }
  pose proof (Int.unsigned_range_2 (no_len (data k))) as HR. change Int.max_unsigned with 4294967295 in HR.
  specialize (IH ltac:(lia)). unfold nd_out_count. lia.
Qed.

Definition ct_inv (k : nat) (le : temp_env) : Prop :=
  le!_i = Some (Vlong (Int64.repr (Z.of_nat k))) /\
  le!_result = Some (Vlong (Int64.repr (nd_total data k))) /\
  le!_rawTx = Some txv.

Lemma ct_numOutputs le :
  le!_rawTx = Some txv ->
  eval_expr sha_ge empty_env le m (Efield (Ederef (Etempvar _rawTx (tptr RTX)) RTX) _numOutputs tuint) (Vint nout).
Proof.
  intros HT. eapply eval_envu_field_value;
    [reflexivity|exact envu_rawElementsTransaction_numOutputs|reflexivity
    |apply eval_envu_deref_struct; exact HT|].
  rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|exact HNo].
Qed.

Lemma ct_ltu k : 0 <= k <= Int.unsigned nout ->
  Int64.ltu (Int64.repr k) (Int64.repr (Int.unsigned nout)) = if zlt k (Int.unsigned nout) then true else false.
Proof.
  intros Hk. pose proof (Int.unsigned_range_2 nout) as HR. change Int.max_unsigned with 4294967295 in HR.
  unfold Int64.ltu.
  rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia). reflexivity.
Qed.

Lemma ct_exit le : ct_inv n le ->
  exists le', ct_inv n le' /\
    Clight2.exec_stmt sha_ge empty_env le m (Sloop ct_s1 ct_s2) E0 le' m Out_normal.
Proof.
  intros (Hi & Hr & Ht). pose proof (Int.unsigned_range nout) as HR.
  exists (PTree.set _t'3 (Vint nout) le). split.
  { unfold ct_inv. rewrite !PTree.gso by discriminate. repeat split; assumption. }
  eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
  cbv delta [ct_s1] beta iota.
  eapply exec_Sseq_2; [|discriminate].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'3 (Vint nout) le) (m1 := m).
  - apply exec_Sset. apply ct_numOutputs. exact Ht.
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
    + eapply eval_Ebinop; [apply eval_Etempvar; rewrite PTree.gso by discriminate; exact Hi
                          |apply eval_Etempvar; apply PTree.gss|].
      change (Some (Val.of_bool (Int64.ltu (Int64.repr (Z.of_nat n)) (Int64.repr (Int.unsigned nout)))) =
              Some (Vint Int.zero)).
      rewrite ct_ltu by (rewrite ct_n; lia). rewrite ct_n, zlt_false by lia. reflexivity.
    + reflexivity.
    + apply exec_Sbreak.
Qed.

Lemma ct_step k le : (k < n)%nat -> ct_inv k le ->
  exists le1 le2, ct_inv (S k) le2 /\
    Clight2.exec_stmt sha_ge empty_env le m ct_s1 E0 le1 m Out_normal /\
    Clight2.exec_stmt sha_ge empty_env le1 m ct_s2 E0 le2 m Out_normal.
Proof.
  intros Hk (Hi & Hr & Ht). pose proof ct_n as Hn.
  pose proof (Int.unsigned_range_2 nout) as HR. change Int.max_unsigned with 4294967295 in HR.
  destruct (HData k Hk) as (DL & DB & DM & DBs).
  set (cnt := nd_out_count (data k)).
  set (leA := PTree.set _t'3 (Vint nout) le).
  set (leB := PTree.set _t'2 (Vptr bo (Ptrofs.repr oo)) leA).
  set (leC := PTree.set _t'1 (Vlong (Int64.repr cnt)) leB).
  set (le1 := PTree.set _result (Vlong (Int64.repr (nd_total data (S k)))) leC).
  set (le2 := PTree.set _i (Vlong (Int64.repr (Z.of_nat (S k)))) le1).
  exists le1, le2. split; [|split].
  - unfold ct_inv, le2, le1, leC, leB, leA. split; [apply PTree.gss|].
    split; [rewrite PTree.gso by discriminate; apply PTree.gss|].
    rewrite !PTree.gso by discriminate. exact Ht.
  - cbv delta [ct_s1] beta iota.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leA) (m1 := m).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leA) (m1 := m).
      * apply exec_Sset. apply ct_numOutputs. exact Ht.
      * eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
        -- eapply eval_Ebinop; [apply eval_Etempvar; unfold leA; rewrite PTree.gso by discriminate; exact Hi
                                |apply eval_Etempvar; apply PTree.gss|].
           change (Some (Val.of_bool (Int64.ltu (Int64.repr (Z.of_nat k)) (Int64.repr (Int.unsigned nout)))) =
                   Some (Vint Int.one)).
           rewrite ct_ltu by lia. rewrite zlt_true by lia. reflexivity.
        -- reflexivity.
        -- apply exec_Sskip.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leC) (m1 := m).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leB) (m1 := m).
        -- apply exec_Sset. eapply eval_envu_field_value;
             [reflexivity|exact envu_rawElementsTransaction_output|reflexivity
             |apply eval_envu_deref_struct; unfold leA; rewrite PTree.gso by discriminate; exact Ht|].
           rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|]. apply HOut. lia.
        -- change leC with (set_opttemp (Some _t'1) (Vlong (Int64.repr cnt)) leB).
           eapply exec_Scall with (vf := Vptr (sha_symbol_block _countNullDataCodes) Ptrofs.zero)
             (vargs := [Vptr bo (Ptrofs.repr (oo + 72 * Z.of_nat k + 24))]) (f := Internal f_countNullDataCodes).
           ++ reflexivity.
           ++ eapply eval_Elvalue; [apply eval_Evar_global; [apply PTree.gempty|exact sha_countNullDataCodes_symbol]|].
              apply deref_loc_reference; reflexivity.
           ++ eapply eval_Econs with (v1 := Vptr bo (Ptrofs.repr (oo + 72 * Z.of_nat k + 24)));
                [|reflexivity|apply eval_Enil].
              eapply eval_Eaddrof.
              rewrite <- (envu_ptr_add_repr (oo + 72 * Z.of_nat k) 24) by lia.
              eapply eval_envu_field_lvalue; [reflexivity|exact envu_rawElementsOutput_scriptPubKey|].
              eapply eval_Elvalue; [|apply deref_loc_copy; reflexivity].
              eapply eval_Ederef.
              eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss
                                  |apply eval_Etempvar; unfold leB, leA; rewrite !PTree.gso by discriminate; exact Hi|].
              rewrite <- (cf_ptr_index oo 72 (Z.of_nat k))
                by (change Ptrofs.max_unsigned with 18446744073709551615 in *; lia).
              rewrite <- fee_sizeof_ROUT. reflexivity.
           ++ exact sha_countNullDataCodes_funct.
           ++ reflexivity.
           ++ unfold cnt, nd_out_count.
              apply (eval_countNullDataCodes m bo (oo + 72 * Z.of_nat k + 24) (no_len (data k))
                (no_bb (data k)) (no_ob (data k)) (no_bs (data k))).
              ** lia.
              ** replace (oo + 72 * Z.of_nat k + 24 + 8) with (oo + 72 * Z.of_nat k + 32) by lia. exact DL.
              ** exact DB.
              ** exact DM.
              ** exact DBs.
      * apply exec_Sset.
        eapply eval_Ebinop; [apply eval_Etempvar; unfold leC, leB, leA; rewrite !PTree.gso by discriminate; exact Hr
                            |apply eval_Etempvar; apply PTree.gss|].
        cbn [nd_total]. fold cnt. rewrite <- ct_i64_add. reflexivity.
  - cbv delta [ct_s2] beta iota. apply exec_Sset.
    eapply eval_Ebinop; [apply eval_Etempvar; unfold le1, leC, leB, leA; rewrite !PTree.gso by discriminate; exact Hi
                        |apply eval_Econst_int|].
    replace (Z.of_nat (S k)) with (Z.of_nat k + 1) by lia. rewrite <- ct_i64_add. reflexivity.
Qed.

Lemma ct_loop d : forall k le, (k + d = n)%nat -> ct_inv k le ->
  exists le', ct_inv n le' /\
    Clight2.exec_stmt sha_ge empty_env le m (Sloop ct_s1 ct_s2) E0 le' m Out_normal.
Proof.
  induction d as [|d IH]; intros k le Hkd HI.
  - replace k with n in HI by lia. exact (ct_exit le HI).
  - destruct (ct_step k le ltac:(lia) HI) as (le1 & le2 & HI2 & H1 & H2).
    destruct (IH (S k) le2 ltac:(lia) HI2) as (le' & HI' & HE).
    exists le'. split; [exact HI'|].
    change E0 with (E0 ** E0 ** E0).
    eapply exec_Sloop_loop; [exact H1|constructor|exact H2|exact HE].
Qed.

Theorem eval_countTotalNullDataCodes :
  Clight2.eval_funcall sha_ge m (Internal f_countTotalNullDataCodes) [txv] E0 m
    (Vlong (Int64.repr (nd_total data n))).
Proof.
  set (le0 := PTree.set _rawTx txv (create_undef_temps (fn_temps f_countTotalNullDataCodes))).
  set (leR := PTree.set _result (Vlong (Int64.repr 0)) le0).
  set (leI := PTree.set _i (Vlong (Int64.repr 0)) leR).
  destruct (ct_loop n 0%nat leI eq_refl) as (le' & (Hi & Hr & Ht) & HE).
  { unfold ct_inv, leI, leR, le0. split; [apply PTree.gss|].
    split; [rewrite PTree.gso by discriminate; apply PTree.gss|].
    rewrite !PTree.gso by discriminate. apply PTree.gss. }
  eapply eval_funcall_internal with (e := empty_env) (le1 := le0) (m1 := m) (m2 := m)
    (le2 := le') (out := Out_return (Some (Vlong (Int64.repr (nd_total data n)), tulong))).
  - apply function_entry2_intro.
    + apply list_norepet_nil.
    + repeat constructor; simpl; intuition discriminate.
    + intros x0 y0 HX HY; cbn in HX, HY; intuition (subst; discriminate).
    + apply alloc_variables_nil.
    + reflexivity.
  - rewrite ct_body_shape.
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
End CountTotal.
