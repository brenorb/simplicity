(** [simplicity_bitcoin_mallocTransaction] (bitcoin/env.c), first part: the
    null guard, the size arithmetic with its four overflow checks, the
    [malloc] call, and the pointers [tx], [input] and [output] into the
    allocated block.  Continuation style, as for [mallocTapEnv]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_add_n_init.
Require Import C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_malloc C.jet_bitcoin_env_tapenv_prelude.
Require Import C.jet_bitcoin_env_copyoutput C.jet_bitcoin_env_copyinput_fill C.jet_bitcoin_env_tx_arith.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Notation TX := (Tstruct _bitcoinTransaction noattr).
Notation RTX := (Tstruct _rawBitcoinTransaction noattr).

Definition mt_body : statement := fn_body f_simplicity_bitcoin_mallocTransaction.

(** The body after its first twenty-one statements (up to [output = ...]). *)
Definition mt_rest1 : statement :=
  ltac:(let b := eval cbv delta [mt_body f_simplicity_bitcoin_mallocTransaction fn_body] beta iota in mt_body in
        let r := drop_seq 21%nat b in exact r).

Lemma mt_sizeof_TX : Vptrofs (Ptrofs.repr (sizeof sha_ge TX)) = Vlong (Int64.repr 488).
Proof. vm_compute; reflexivity. Qed.
Lemma mt_sizeof_SIN : Vptrofs (Ptrofs.repr (sizeof sha_ge SIN)) = Vlong (Int64.repr 160).
Proof. vm_compute; reflexivity. Qed.
Lemma mt_sizeof_SOUT : Vptrofs (Ptrofs.repr (sizeof sha_ge SOUT)) = Vlong (Int64.repr 40).
Proof. vm_compute; reflexivity. Qed.
Lemma mt_alignof_SIN : Vptrofs (Ptrofs.repr (alignof sha_ge SIN)) = Vlong (Int64.repr 8).
Proof. vm_compute; reflexivity. Qed.
Lemma mt_alignof_SOUT : Vptrofs (Ptrofs.repr (alignof sha_ge SOUT)) = Vlong (Int64.repr 8).
Proof. vm_compute; reflexivity. Qed.

Lemma envu_rawTx_numInputs : envu_field_at _rawBitcoinTransaction _numInputs 24.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawTx_numOutputs : envu_field_at _rawBitcoinTransaction _numOutputs 28.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

Lemma ev_sizeof_TX e le m : eval_expr sha_ge e le m (Esizeof TX tulong) (Vlong (Int64.repr 488)).
Proof. rewrite <- mt_sizeof_TX. apply eval_Esizeof. Qed.
Lemma ev_sizeof_SIN e le m : eval_expr sha_ge e le m (Esizeof SIN tulong) (Vlong (Int64.repr 160)).
Proof. rewrite <- mt_sizeof_SIN. apply eval_Esizeof. Qed.
Lemma ev_sizeof_SOUT e le m : eval_expr sha_ge e le m (Esizeof SOUT tulong) (Vlong (Int64.repr 40)).
Proof. rewrite <- mt_sizeof_SOUT. apply eval_Esizeof. Qed.
Lemma ev_alignof_SIN e le m : eval_expr sha_ge e le m (Ealignof SIN tulong) (Vlong (Int64.repr 8)).
Proof. rewrite <- mt_alignof_SIN. apply eval_Ealignof. Qed.
Lemma ev_alignof_SOUT e le m : eval_expr sha_ge e le m (Ealignof SOUT tulong) (Vlong (Int64.repr 8)).
Proof. rewrite <- mt_alignof_SOUT. apply eval_Ealignof. Qed.

(** Normalise the left-hand side of a [sem_*] goal down to machine-integer
    operations. *)
Ltac norm_sem :=
  match goal with
  | |- ?L = _ =>
      let L' := eval lazy -[Int64.ltu Int64.mul Int64.divu Int64.modu Int64.sub Int64.add Int64.repr
                           Int.unsigned Int.signed Int.repr Int.lt Val.of_bool
                           Ptrofs.add Ptrofs.mul Ptrofs.repr Ptrofs.of_int64 Ptrofs.zero] in L in
      change L with L'
  end.

Lemma load_valid_block_any chunk m b ofs v : Mem.load chunk m b ofs = Some v -> Mem.valid_block m b.
Proof.
  intro HL. apply Mem.load_valid_access in HL.
  eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies; [exact HL|constructor].
Qed.

Definition mt_le1 (le : temp_env) (rawv : val) (bA : block) (ni : Z) : Prop :=
  le!_rawTx = Some rawv /\
  le!_tx = Some (Vptr bA Ptrofs.zero) /\
  le!_input = Some (Vptr bA (Ptrofs.repr 488)) /\
  le!_output = Some (Vptr bA (Ptrofs.repr (488 + 160 * ni))).

Section TxPrelude.
Variables (e : env) (braw : block) (oraw : Z) (niv nov : int).
Hypothesis He : e!_malloc = None.
Hypothesis Horaw : 0 <= oraw /\ oraw + 40 <= Ptrofs.max_unsigned.

Let rawv := Vptr braw (Ptrofs.repr oraw).
Let ni := Int.unsigned niv.
Let no := Int.unsigned nov.
Let le0 := PTree.set _rawTx rawv (create_undef_temps (fn_temps f_simplicity_bitcoin_mallocTransaction)).

Lemma mt_count_expr le m f delta v :
  le!_rawTx = Some rawv -> envu_field_at _rawBitcoinTransaction f delta -> 0 <= delta <= 36 ->
  Mem.load Mint32 m braw (oraw + delta) = Some (Vint v) ->
  eval_expr sha_ge e le m (Efield (Ederef (Etempvar _rawTx (tptr RTX)) RTX) f tuint) (Vint v).
Proof.
  intros Hle Hf Hd HL. eapply eval_envu_field_value;
    [reflexivity|exact Hf|reflexivity|apply eval_envu_deref_struct; exact Hle|].
  unfold rawv. rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|exact HL].
Qed.
Hypothesis Hni : 0 <= Int.unsigned niv <= 4294967295.
Hypothesis Hno : 0 <= Int.unsigned nov <= 4294967295.

Ltac seq1 l m := eapply exec_Sseq_1 with (t1 := E0) (le1 := l) (m1 := m).
Ltac guard_false := eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false); [|reflexivity|apply exec_Sskip].
Ltac tv := apply eval_Etempvar; reflexivity.

Theorem mt_prelude m :
  Mem.load Mint32 m braw (oraw + 24) = Some (Vint niv) ->
  Mem.load Mint32 m braw (oraw + 28) = Some (Vint nov) ->
  Mem.weak_valid_pointer m braw (Ptrofs.unsigned (Ptrofs.repr oraw)) = true ->
  exists m1 m2 bA le1,
    Mem.alloc m (-8) (488 + 160 * ni + 40 * no) = (m1, bA) /\
    Mem.store Mptr m1 bA (-8) (Vlong (Int64.repr (488 + 160 * ni + 40 * no))) = Some m2 /\
    mt_le1 le1 rawv bA ni /\
    (forall t le' m' out,
       Clight2.exec_stmt sha_ge e le1 m2 mt_rest1 t le' m' out ->
       Clight2.exec_stmt sha_ge e le0 m mt_body t le' m' out).
Proof.
  intros HNi HNo HWeak.
  assert (Hni' : 0 <= ni <= 4294967295) by exact Hni.
  assert (Hno' : 0 <= no <= 4294967295) by exact Hno.
  destruct (eval_malloc m (488 + 160 * ni + 40 * no)) as (m1 & m2 & bA & HA & HS & HCall).
  { change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  assert (HWA : Mem.weak_valid_pointer m2 bA (Ptrofs.unsigned Ptrofs.zero) = true).
  { unfold Mem.weak_valid_pointer. apply orb_true_iff. left.
    apply Mem.valid_pointer_nonempty_perm. eapply Mem.perm_store_1; [exact HS|].
    eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; [exact HA|rewrite Ptrofs.unsigned_zero; lia]|constructor]. }
  set (l1 := PTree.set _allocationSize (Vlong (Int64.repr 488)) le0).
  set (l2 := PTree.set _pad1 (Vlong (Int64.repr 0)) l1).
  set (l3 := PTree.set _allocationSize (Vlong (Int64.repr 488)) l2).
  set (l4 := PTree.set _t'29 (Vint niv) l3).
  set (l5 := PTree.set _t'28 (Vint niv) l4).
  set (l5a := PTree.set _t'27 (Vint niv) l5).
  set (l6 := PTree.set _allocationSize (Vlong (Int64.repr (488 + 160 * ni))) l5a).
  set (l7 := PTree.set _pad2 (Vlong (Int64.repr 0)) l6).
  set (l8 := PTree.set _allocationSize (Vlong (Int64.repr (488 + 160 * ni))) l7).
  set (l9 := PTree.set _t'26 (Vint nov) l8).
  set (l10 := PTree.set _t'25 (Vint nov) l9).
  set (l10a := PTree.set _t'24 (Vint nov) l10).
  set (l11 := PTree.set _allocationSize (Vlong (Int64.repr (488 + 160 * ni + 40 * no))) l10a).
  set (l11a := PTree.set _t'1 (Vptr bA Ptrofs.zero) l11).
  set (l12 := PTree.set _allocation (Vptr bA Ptrofs.zero) l11a).
  set (l13 := PTree.set _tx (Vptr bA Ptrofs.zero) l12).
  set (l14 := PTree.set _allocation (Vptr bA (Ptrofs.repr 488)) l13).
  set (l15 := PTree.set _input (Vptr bA (Ptrofs.repr 488)) l14).
  set (l15a := PTree.set _t'23 (Vint niv) l15).
  set (l16 := PTree.set _allocation (Vptr bA (Ptrofs.repr (488 + 160 * ni))) l15a).
  set (l17 := PTree.set _output (Vptr bA (Ptrofs.repr (488 + 160 * ni))) l16).
  exists m1, m2, bA, l17. split; [exact HA|]. split; [exact HS|]. split.
  { unfold mt_le1. repeat split; reflexivity. }
  intros t le' m' out HRest.
  cbv delta [mt_body f_simplicity_bitcoin_mallocTransaction fn_body] beta iota.
  (* 1 *)
  seq1 le0 m.
  { eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false); [|reflexivity|apply exec_Sskip].
    eapply eval_Eunop; [tv|]. unfold rawv. cbn. unfold sem_notbool, bool_val. cbn. rewrite HWeak. reflexivity. }
  (* 2 *)
  seq1 l1 m. { apply exec_Sset. apply ev_sizeof_TX. }
  (* 3 *)
  seq1 l2 m.
  { apply exec_Sset. eapply eval_Ebinop;
      [eapply eval_Ebinop; [apply ev_alignof_SIN|eapply eval_Ebinop; [tv|apply ev_alignof_SIN|reflexivity]|reflexivity]
      |apply ev_alignof_SIN|vm_compute; reflexivity]. }
  (* 4 *)
  seq1 l2 m.
  { guard_false. eapply eval_Ebinop;
      [eapply eval_Ebinop; [apply eval_Econst_long|tv|reflexivity]|tv|vm_compute; reflexivity]. }
  (* 5 *)
  seq1 l3 m. { apply exec_Sset. eapply eval_Ebinop; [tv|tv|vm_compute; reflexivity]. }
  (* 6 *)
  seq1 l4 m.
  { seq1 l4 m; [apply exec_Sset; apply mt_count_expr with (delta := 24); [reflexivity|exact envu_rawTx_numInputs|lia|exact HNi]|].
    guard_false. eapply eval_Ebinop;
      [eapply eval_Ebinop; [apply eval_Econst_long|apply ev_sizeof_SIN|reflexivity]
      |eapply eval_Ebinop; [eapply eval_Ecast; [apply eval_Econst_int|reflexivity]|tv|reflexivity]|].
    norm_sem. change (Int.signed (Int.repr 1)) with 1. fold ni.
    rewrite (tx_mul_one ni Hni'), (tx_div_in ni Hni'). reflexivity. }
  (* 7 *)
  seq1 l5 m.
  { seq1 l5 m; [apply exec_Sset; apply mt_count_expr with (delta := 24); [reflexivity|exact envu_rawTx_numInputs|lia|exact HNi]|].
    guard_false. eapply eval_Ebinop;
      [eapply eval_Ebinop; [apply eval_Econst_long|tv|reflexivity]
      |eapply eval_Ebinop; [tv|apply ev_sizeof_SIN|reflexivity]|].
    norm_sem. fold ni. rewrite (tx_mul_in ni Hni'), tx_room by lia. reflexivity. }
  (* 8 *)
  seq1 l6 m.
  { seq1 l5a m; [apply exec_Sset; apply mt_count_expr with (delta := 24); [reflexivity|exact envu_rawTx_numInputs|lia|exact HNi]|].
    apply exec_Sset. eapply eval_Ebinop;
      [tv|eapply eval_Ebinop; [tv|apply ev_sizeof_SIN|reflexivity]|].
    norm_sem. fold ni. rewrite (tx_mul_in ni Hni'), (tx_size_in ni Hni'). reflexivity. }
  (* 9 *)
  seq1 l7 m.
  { apply exec_Sset. eapply eval_Ebinop;
      [eapply eval_Ebinop; [apply ev_alignof_SOUT|eapply eval_Ebinop; [tv|apply ev_alignof_SOUT|reflexivity]|reflexivity]
      |apply ev_alignof_SOUT|].
    change (Some (Vlong (Int64.modu (Int64.sub (Int64.repr 8) (Int64.modu (Int64.repr (488 + 160 * ni)) (Int64.repr 8)))
      (Int64.repr 8))) = Some (Vlong (Int64.repr 0))).
    rewrite (tx_pad2 ni Hni'). reflexivity. }
  (* 10 *)
  seq1 l7 m.
  { guard_false. eapply eval_Ebinop;
      [eapply eval_Ebinop; [apply eval_Econst_long|tv|reflexivity]|tv|].
    change (Some (Val.of_bool (Int64.ltu (Int64.sub (Int64.repr (-1)) (Int64.repr (488 + 160 * ni))) (Int64.repr 0))) =
      Some (Vint Int.zero)).
    rewrite tx_room by lia. reflexivity. }
  (* 11 *)
  seq1 l8 m.
  { apply exec_Sset. eapply eval_Ebinop; [tv|tv|].
    change (Some (Vlong (Int64.add (Int64.repr (488 + 160 * ni)) (Int64.repr 0))) =
      Some (Vlong (Int64.repr (488 + 160 * ni)))).
    rewrite tx_add_zero. reflexivity. }
  (* 12 *)
  seq1 l9 m.
  { seq1 l9 m; [apply exec_Sset; apply mt_count_expr with (delta := 28); [reflexivity|exact envu_rawTx_numOutputs|lia|exact HNo]|].
    guard_false. eapply eval_Ebinop;
      [eapply eval_Ebinop; [apply eval_Econst_long|apply ev_sizeof_SOUT|reflexivity]
      |eapply eval_Ebinop; [eapply eval_Ecast; [apply eval_Econst_int|reflexivity]|tv|reflexivity]|].
    norm_sem. change (Int.signed (Int.repr 1)) with 1. fold no.
    rewrite (tx_mul_one no Hno'), (tx_div_out no Hno'). reflexivity. }
  (* 13 *)
  seq1 l10 m.
  { seq1 l10 m; [apply exec_Sset; apply mt_count_expr with (delta := 28); [reflexivity|exact envu_rawTx_numOutputs|lia|exact HNo]|].
    guard_false. eapply eval_Ebinop;
      [eapply eval_Ebinop; [apply eval_Econst_long|tv|reflexivity]
      |eapply eval_Ebinop; [tv|apply ev_sizeof_SOUT|reflexivity]|].
    change (Some (Val.of_bool (Int64.ltu (Int64.sub (Int64.repr (-1)) (Int64.repr (488 + 160 * ni)))
      (Int64.mul (Int64.repr no) (Int64.repr 40)))) = Some (Vint Int.zero)).
    rewrite (tx_mul_out no Hno'), tx_room by lia. reflexivity. }
  (* 14 *)
  seq1 l11 m.
  { seq1 l10a m; [apply exec_Sset; apply mt_count_expr with (delta := 28); [reflexivity|exact envu_rawTx_numOutputs|lia|exact HNo]|].
    apply exec_Sset. eapply eval_Ebinop;
      [tv|eapply eval_Ebinop; [tv|apply ev_sizeof_SOUT|reflexivity]|].
    change (Some (Vlong (Int64.add (Int64.repr (488 + 160 * ni)) (Int64.mul (Int64.repr no) (Int64.repr 40)))) =
      Some (Vlong (Int64.repr (488 + 160 * ni + 40 * no)))).
    rewrite (tx_mul_out no Hno'), (tx_size_out ni no Hni' Hno'). reflexivity. }
  (* 15 *)
  seq1 l12 m2.
  { seq1 l11a m2.
    - change l11a with (set_opttemp (Some _t'1) (Vptr bA Ptrofs.zero) l11).
      eapply exec_Scall with (vf := Vptr (sha_symbol_block _malloc) Ptrofs.zero)
        (vargs := [Vlong (Int64.repr (488 + 160 * ni + 40 * no))]) (f := malloc_fundef).
      + reflexivity.
      + eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact sha_malloc_symbol]|].
        apply deref_loc_reference; reflexivity.
      + eapply eval_Econs; [tv|reflexivity|apply eval_Enil].
      + exact sha_malloc_funct.
      + reflexivity.
      + exact HCall.
    - apply exec_Sset. tv. }
  (* 16 *)
  seq1 l12 m2.
  { eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false); [|reflexivity|apply exec_Sskip].
    eapply eval_Eunop; [tv|]. cbn. unfold sem_notbool, bool_val. cbn. rewrite HWA. reflexivity. }
  (* 17 *)
  seq1 l13 m2.
  { apply exec_Sset. eapply eval_Ecast; [eapply eval_Ecast; [tv|reflexivity]|reflexivity]. }
  (* 18 *)
  seq1 l14 m2.
  { apply exec_Sset. eapply eval_Ebinop; [tv|eapply eval_Ebinop; [apply ev_sizeof_TX|tv|reflexivity]|].
    rewrite <- tx_first_ptr. reflexivity. }
  (* 19 *)
  seq1 l15 m2.
  { apply exec_Sset. eapply eval_Ecast; [eapply eval_Ecast; [tv|reflexivity]|reflexivity]. }
  (* 20 *)
  seq1 l16 m2.
  { seq1 l15a m2;
      [apply exec_Sset; apply mt_count_expr with (delta := 24); [reflexivity|exact envu_rawTx_numInputs|lia|]|].
    { rewrite (Mem.load_store_other _ _ _ _ _ _ HS).
      - erewrite Mem.load_alloc_unchanged; [exact HNi|exact HA|]. eapply load_valid_block_any; exact HNi.
      - left. intro E. subst braw. apply (Mem.fresh_block_alloc _ _ _ _ _ HA). eapply load_valid_block_any; exact HNi. }
    apply exec_Sset. eapply eval_Ebinop;
      [tv|eapply eval_Ebinop; [eapply eval_Ebinop; [tv|apply ev_sizeof_SIN|reflexivity]|tv|reflexivity]|].
    norm_sem. fold ni. rewrite (tx_mul_in ni Hni'), <- (tx_input_ptr ni Hni'). reflexivity. }
  (* 21 *)
  seq1 l17 m2.
  { apply exec_Sset. eapply eval_Ecast; [eapply eval_Ecast; [tv|reflexivity]|reflexivity]. }
  exact HRest.
Qed.
End TxPrelude.
