(** Execution of the idioms of [parseNullData]
    (jet_elements_env_parse_defs.v) on a memory satisfying the invariant
    [pm] (jet_elements_env_parse_mem.v): the failure exit, the end-of-script
    checks, the store of an opcode's code and the allocation check. *)
From Coq Require Import ZArith List Lia PeanoNat Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_be32_exec C.jet_sha_block_local C.jet_sha_uchars_exec C.jet_sha_ctx_abs.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_isfee C.jet_elements_env_countfee.
Require Import C.jet_elements_env_nulldata_count C.jet_elements_env_parse_defs C.jet_elements_env_parse_mem.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Lemma envu_pnd_op : envu_field_at _parsedNullData _op 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_pnd_len : envu_field_at _parsedNullData _len 8.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_opcode_dataHash : envu_field_at _opcode _dataHash 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_opcode_code : envu_field_at _opcode _code 32.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma pn_sizeof_OPC : sizeof sha_ge OPC = 36.
Proof. vm_compute; reflexivity. Qed.
Lemma pn_sizeof_PND : sizeof sha_ge PND = 16.
Proof. vm_compute; reflexivity. Qed.
Lemma pn_blockcopy_PND : alignof_blockcopy sha_ge PND = 8.
Proof. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

(** Temporaries whose assignment leaves the parser's variables alone. *)
Definition pn_keeps (id : ident) : Prop :=
  nd_keeps id /\
  forall (v : val) (le : temp_env),
    (PTree.set id v le)!_allocation = le!_allocation /\
    (PTree.set id v le)!_allocationLen = le!_allocationLen.

Ltac pn_keeps_tac :=
  unfold pn_keeps, nd_keeps; repeat split; intros;
  rewrite !PTree.gso by discriminate; repeat split; reflexivity.

Section ParseOps.
Variables (e : env).
Variables (br : block) (or_ : Z) (ba : block) (oa : Z) (bl : block) (ol : Z) (bop : block) (oop alen : Z).
Variables (bsp : block) (osp : Z) (len : int) (bb : block) (ob : ptrofs) (bs : list int).

Hypothesis Hor : 0 <= or_ /\ or_ + 16 <= Ptrofs.max_unsigned.
Hypothesis Hoa : 0 <= oa /\ oa + 8 <= Ptrofs.max_unsigned.
Hypothesis Hol : 0 <= ol /\ ol + 8 <= Ptrofs.max_unsigned.
Hypothesis Hoop : 0 <= oop /\ oop + 36 * alen <= Ptrofs.max_unsigned.
Hypothesis HoopA : (4 | oop).
Hypothesis Halen : 0 <= alen <= 4294967295.
Hypothesis Hosp : 0 <= osp /\ osp + 16 <= Ptrofs.max_unsigned.

Let L : Z := Int.unsigned len.
Let spv := Vptr bsp (Ptrofs.repr osp).
Let resv := Vptr br (Ptrofs.repr or_).

(** The parser's variables. *)
Definition pl (le : temp_env) (i : Z) : Prop :=
  le!_i = Some (Vlong (Int64.repr i)) /\ le!_result = Some resv /\
  le!_allocation = Some (Vptr ba (Ptrofs.repr oa)) /\
  le!_allocationLen = Some (Vptr bl (Ptrofs.repr ol)) /\
  le!_scriptPubKey = Some spv.

Definition pls (le : temp_env) (i : Z) (c : int) (sk : Z) : Prop :=
  pl le i /\ le!_code = Some (Vint c) /\ le!_skip = Some (Vlong (Int64.repr sk)).

Lemma pl_set id v le i : pn_keeps id -> pl le i -> pl (PTree.set id v le) i.
Proof.
  intros (HK & HA) (H1 & H2 & H3 & H4 & H5). destruct (HK v le) as (K1 & _ & _ & K4 & K5).
  destruct (HA v le) as (A1 & A2). unfold pl. rewrite K1, K4, K5, A1, A2. repeat split; assumption.
Qed.

Lemma pls_set id v le i c sk : pn_keeps id -> pls le i c sk -> pls (PTree.set id v le) i c sk.
Proof.
  intros HKK (HP & Hc & Hs). pose proof HKK as (HK & _). destruct (HK v le) as (_ & K2 & K3 & _ & _).
  split; [apply pl_set; assumption|]. rewrite K2, K3. split; assumption.
Qed.

Lemma pn_add0 (o : ptrofs) : Ptrofs.add o (Ptrofs.repr 0) = o.
Proof. change (Ptrofs.repr 0) with Ptrofs.zero. apply Ptrofs.add_zero. Qed.

Lemma pn_op_lvalue le m :
  le!_result = Some resv ->
  eval_lvalue sha_ge e le m (Efield PRES _op PO) br (Ptrofs.repr or_) Full.
Proof.
  intros HR. rewrite <- (pn_add0 (Ptrofs.repr or_)).
  eapply eval_envu_field_lvalue; [reflexivity|exact envu_pnd_op|apply eval_envu_deref_struct; exact HR].
Qed.

Lemma pn_len_lvalue le m :
  le!_result = Some resv ->
  eval_lvalue sha_ge e le m (Efield PRES _len tulong) br (Ptrofs.repr (or_ + 8)) Full.
Proof.
  intros HR. rewrite <- (envu_ptr_add_repr or_ 8) by lia.
  eapply eval_envu_field_lvalue; [reflexivity|exact envu_pnd_len|apply eval_envu_deref_struct; exact HR].
Qed.

Lemma pn_len_value le m v :
  le!_result = Some resv -> Mem.load Mint64 m br (or_ + 8) = Some v ->
  eval_expr sha_ge e le m (Efield PRES _len tulong) v.
Proof.
  intros HR HL. eapply eval_Elvalue; [apply pn_len_lvalue; exact HR|].
  eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv. rewrite Ptrofs.unsigned_repr by lia. exact HL.
Qed.

Lemma pn_alloc_value le m v :
  le!_allocation = Some (Vptr ba (Ptrofs.repr oa)) -> Mem.load Mptr m ba oa = Some v ->
  eval_expr sha_ge e le m (Ederef (Etempvar _allocation PPO) PO) v.
Proof.
  intros HA HL. eapply eval_Elvalue; [apply eval_Ederef, eval_Etempvar; exact HA|].
  eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv. rewrite Ptrofs.unsigned_repr by lia. exact HL.
Qed.

Lemma pn_alen_value le m v :
  le!_allocationLen = Some (Vptr bl (Ptrofs.repr ol)) -> Mem.load Mint64 m bl ol = Some v ->
  eval_expr sha_ge e le m (Ederef (Etempvar _allocationLen (tptr tulong)) tulong) v.
Proof.
  intros HA HL. eapply eval_Elvalue; [apply eval_Ederef, eval_Etempvar; exact HA|].
  eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv. rewrite Ptrofs.unsigned_repr by lia. exact HL.
Qed.

(** [{ result->op = NULL; return; }] *)
Lemma pn_fail_exec le m :
  le!_result = Some resv -> Mem.valid_access m Mptr br or_ Writable ->
  exists m',
    Clight2.exec_stmt sha_ge e le m pn_fail E0 le m' (Out_return None) /\
    Mem.store Mptr m br or_ (Vlong Int64.zero) = Some m'.
Proof.
  intros HR VA. destruct (Mem.valid_access_store m Mptr br or_ (Vlong Int64.zero) VA) as [m' HS].
  exists m'. split; [|exact HS]. unfold pn_fail.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m'); [|apply exec_Sreturn_none].
  eapply exec_Sassign with (v2 := Vlong Int64.zero) (v := Vlong Int64.zero).
  - apply pn_op_lvalue. exact HR.
  - eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
  - reflexivity.
  - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite Ptrofs.unsigned_repr by lia. exact HS.
Qed.

(** The address of opcode [n] of the array and of its code. *)
Lemma pn_opcode_ptr le m ta tn n :
  le!ta = Some (Vptr bop (Ptrofs.repr oop)) -> le!tn = Some (Vlong (Int64.repr n)) -> 0 <= n < alen ->
  eval_expr sha_ge e le m (Ebinop Oadd (Etempvar ta PO) (Etempvar tn tulong) PO)
    (Vptr bop (Ptrofs.repr (oop + 36 * n))).
Proof.
  intros Ha Hn Hr. eapply eval_Ebinop; [apply eval_Etempvar; exact Ha|apply eval_Etempvar; exact Hn|].
  rewrite <- (cf_ptr_index oop 36 n) by (change Ptrofs.max_unsigned with 18446744073709551615 in *; lia).
  rewrite <- pn_sizeof_OPC. reflexivity.
Qed.

Lemma pn_code_lvalue le m ta tn n :
  le!ta = Some (Vptr bop (Ptrofs.repr oop)) -> le!tn = Some (Vlong (Int64.repr n)) -> 0 <= n < alen ->
  eval_lvalue sha_ge e le m
    (Efield (Ederef (Ebinop Oadd (Etempvar ta PO) (Etempvar tn tulong) PO) OPC) _code tint)
    bop (Ptrofs.repr (oop + 36 * n + 32)) Full.
Proof.
  intros Ha Hn Hr. rewrite <- (envu_ptr_add_repr (oop + 36 * n) 32) by lia.
  eapply eval_envu_field_lvalue; [reflexivity|exact envu_opcode_code|].
  eapply eval_Elvalue; [apply eval_Ederef; exact (pn_opcode_ptr le m ta tn n Ha Hn Hr)|apply deref_loc_copy; reflexivity].
Qed.

(** [( *allocation)[result->len].code = rhs;] *)
Lemma pn_setcode_exec ta tn (rhs : expr) (cv : int) le m n :
  le!_result = Some resv -> le!_allocation = Some (Vptr ba (Ptrofs.repr oa)) ->
  pn_keeps ta -> pn_keeps tn ->
  (forall (v : val) (le0 : temp_env), (PTree.set tn v le0)!ta = le0!ta) ->
  Mem.load Mptr m ba oa = Some (Vptr bop (Ptrofs.repr oop)) ->
  Mem.load Mint64 m br (or_ + 8) = Some (Vlong (Int64.repr n)) -> 0 <= n < alen ->
  Mem.range_perm m bop oop (oop + 36 * alen) Cur Writable ->
  (forall le' m', le'!_code = le!_code -> eval_expr sha_ge e le' m' rhs (Vint cv)) -> typeof rhs = tint ->
  exists m',
    Clight2.exec_stmt sha_ge e le m (pn_setcode ta tn rhs) E0
      (PTree.set tn (Vlong (Int64.repr n)) (PTree.set ta (Vptr bop (Ptrofs.repr oop)) le)) m' Out_normal /\
    Mem.store Mint32 m bop (oop + 36 * n + 32) (Vint cv) = Some m'.
Proof.
  intros HR HA Ka Kn Hna HLa HLn Hn PO Hrhs Hty.
  destruct (Mem.valid_access_store m Mint32 bop (oop + 36 * n + 32) (Vint cv)) as [m' HS].
  { split.
    - intros o Ho. change (size_chunk Mint32) with 4 in Ho. apply PO. lia.
    - change (align_chunk Mint32) with 4. destruct HoopA as [q ->]. exists (q + 9 * n + 8). lia. }
  set (le1 := PTree.set ta (Vptr bop (Ptrofs.repr oop)) le).
  set (le2 := PTree.set tn (Vlong (Int64.repr n)) le1).
  destruct Ka as (Ka1 & Ka2). destruct Kn as (Kn1 & Kn2).
  assert (HR1 : le1!_result = Some resv).
  { unfold le1. rewrite (proj1 (proj2 (proj2 (proj2 (Ka1 (Vptr bop (Ptrofs.repr oop)) le))))). exact HR. }
  exists m'. split; [|exact HS]. unfold pn_setcode.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
  { apply exec_Sset. apply pn_alloc_value; [exact HA|exact HLa]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m).
  { apply exec_Sset. apply pn_len_value; [exact HR1|exact HLn]. }
  eapply exec_Sassign with (v2 := Vint cv) (v := Vint cv).
  - apply pn_code_lvalue; [unfold le2; rewrite Hna; apply PTree.gss|apply PTree.gss|exact Hn].
  - apply Hrhs. unfold le2, le1.
    rewrite (proj1 (proj2 (Kn1 (Vlong (Int64.repr n)) (PTree.set ta (Vptr bop (Ptrofs.repr oop)) le)))).
    exact (proj1 (proj2 (Ka1 (Vptr bop (Ptrofs.repr oop)) le))).
  - rewrite Hty. reflexivity.
  - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
    rewrite Ptrofs.unsigned_repr by lia. exact HS.
Qed.
End ParseOps.
