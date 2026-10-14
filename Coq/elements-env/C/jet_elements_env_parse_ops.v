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

(** The code stored for a push opcode (OP_IMMEDIATE, OP_PUSHDATA,
    OP_PUSHDATA2, OP_PUSHDATA4 of elements/txEnv.h). *)
Definition pn_kindv (c : Z) : Z :=
  if c <? 76 then 0 else if c <? 77 then 1 else if c <? 78 then 2 else 3.

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
(** The script, readable in the current memory. *)
Section Script.
Variable m : mem.
Hypothesis HLen : Mem.load Mint32 m bsp (osp + 8) = Some (Vint len).
Hypothesis HBuf : 0 < L -> Mem.load Mptr m bsp osp = Some (Vptr bb ob).
Hypothesis HobM : Ptrofs.unsigned ob + L <= Ptrofs.max_unsigned.
Hypothesis HBs : forall i, 0 <= i < L ->
  Mem.load Mint8unsigned m bb (Ptrofs.unsigned ob + i) = Some (Vint (nth (Z.to_nat i) bs Int.zero)).

Lemma pn_if le a (b : bool) s1 s2 t le' m' out :
  eval_expr sha_ge e le m a (Val.of_bool b) -> typeof a = tint ->
  Clight2.exec_stmt sha_ge e le m (if b then s1 else s2) t le' m' out ->
  Clight2.exec_stmt sha_ge e le m (Sifthenelse a s1 s2) t le' m' out.
Proof.
  intros HE HT HX. eapply exec_Sifthenelse with (v1 := Val.of_bool b) (b := b);
    [exact HE|rewrite HT; apply nd_bool_val|exact HX].
Qed.

(** [if (len == i) { result->op = NULL; return; }] *)
Lemma pn_eof_exec tl le i :
  pn_keeps tl -> pl le i -> 0 <= i <= L -> Mem.valid_access m Mptr br or_ Writable ->
  if L =? i
  then exists m', Clight2.exec_stmt sha_ge e le m (pn_eof tl) E0 (PTree.set tl (Vint len) le) m' (Out_return None) /\
         Mem.store Mptr m br or_ (Vlong Int64.zero) = Some m'
  else Clight2.exec_stmt sha_ge e le m (pn_eof tl) E0 (PTree.set tl (Vint len) le) m Out_normal.
Proof.
  intros HK HP Hi VA. pose proof (pl_set tl (Vint len) le i HK HP) as (Hi1 & Hr1 & _ & _ & Hs1).
  destruct HP as (Hli & Hr & _ & _ & Hsp).
  assert (HS : Clight2.exec_stmt sha_ge e le m (Sset tl (Efield PSPK _len tuint)) E0
    (PTree.set tl (Vint len) le) m Out_normal).
  { apply exec_Sset. eapply nd_ev_len; eassumption. }
  assert (HC : eval_expr sha_ge e (PTree.set tl (Vint len) le) m
    (Ebinop Oeq (Etempvar tl tuint) (Etempvar _i tulong) tint) (Val.of_bool (L =? i))).
  { apply nd_ev_len_eq_i; [apply PTree.gss|exact Hi1|exact Hi]. }
  unfold pn_eof. destruct (L =? i) eqn:EL.
  - destruct (pn_fail_exec (PTree.set tl (Vint len) le) m Hr1 VA) as (m' & XF & HSt).
    exists m'. split; [|exact HSt].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HS|].
    eapply pn_if with (b := true); [exact HC|reflexivity|exact XF].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HS|].
    eapply pn_if with (b := false); [exact HC|reflexivity|apply exec_Sskip].
Qed.

Definition pn_trip (tt tp tb : ident) : Prop :=
  nd_trip tt tp tb /\ pn_keeps tt /\ pn_keeps tp /\ pn_keeps tb.

Lemma pl_read tt tp tb le i :
  pn_trip tt tp tb -> pl le i ->
  pl (nd_read_le bb ob bs tt tp tb le i) (i + 1) /\
  (nd_read_le bb ob bs tt tp tb le i)!_code = le!_code /\
  (nd_read_le bb ob bs tt tp tb le i)!_skip = le!_skip.
Proof.
  intros (HT & Kt & Kp & Kb) HP. unfold nd_read_le.
  pose proof (pl_set tt (Vlong (Int64.repr i)) le i Kt HP) as (H1 & H2 & H3 & H4 & H5).
  destruct Kt as (Kt1 & _). destruct Kp as (Kp1 & Kp2). destruct Kb as (Kb1 & Kb2).
  split.
  - apply pl_set; [split; assumption|]. apply pl_set; [split; assumption|].
    unfold pl. rewrite PTree.gss. rewrite !(PTree.gso _ _ (j := _i)) by discriminate.
    repeat split; first [reflexivity|assumption].
  - destruct (Kb1 (Vint (nd_b bs i)) (PTree.set tp (Vptr bb ob)
      (PTree.set _i (Vlong (Int64.repr (i + 1))) (PTree.set tt (Vlong (Int64.repr i)) le)))) as (_ & B2 & B3 & _ & _).
    destruct (Kp1 (Vptr bb ob)
      (PTree.set _i (Vlong (Int64.repr (i + 1))) (PTree.set tt (Vlong (Int64.repr i)) le))) as (_ & P2 & P3 & _ & _).
    destruct (Kt1 (Vlong (Int64.repr i)) le) as (_ & T2 & T3 & _ & _).
    rewrite B2, B3, P2, P3.
    rewrite (PTree.gso _ _ (i := _code)) by discriminate.
    rewrite (PTree.gso _ _ (i := _skip)) by discriminate.
    rewrite T2, T3. split; reflexivity.
Qed.

(** [code = buf[i++]] *)
Lemma pn_read_code tt tp tb le i :
  pn_trip tt tp tb -> pl le i -> 0 <= i < L ->
  exists le',
    Clight2.exec_stmt sha_ge e le m
      (nd_read_stmt tt tp tb (Sset _code (Ecast (Etempvar tb tuchar) tuchar))) E0 le' m Out_normal /\
    pl le' (i + 1) /\ le'!_code = Some (Vint (nd_b bs i)) /\ 0 <= nd_byte bs i < 256.
Proof.
  intros HT HP Hi. destruct (pl_read tt tp tb le i HT HP) as (HP1 & _ & _).
  destruct (nd_load_byte _ _ _ _ (HBs i Hi)) as [Hz Hbr]. fold (nd_b bs i) in Hz, Hbr.
  exists (PTree.set _code (Vint (nd_b bs i)) (nd_read_le bb ob bs tt tp tb le i)).
  destruct HP as (Hli & _ & _ & _ & Hsp).
  split; [|split; [|split; [apply PTree.gss|exact Hbr]]].
  - eapply nd_read_exec with (bs := bs); try eassumption; [exact (proj1 HT)|].
    apply exec_Sset. eapply eval_Ecast with (v1 := Vint (nd_b bs i)); [apply eval_Etempvar; apply nd_read_tb|].
    change (Some (Vint (Int.zero_ext 8 (nd_b bs i))) = Some (Vint (nd_b bs i))). rewrite Hz. reflexivity.
  - destruct HP1 as (A1 & A2 & A3 & A4 & A5). unfold pl. rewrite !PTree.gso by discriminate.
    repeat split; assumption.
Qed.

(** [skip = buf[i++]] *)
Lemma pn_read_skip1 tt tp tb le i c sk :
  pn_trip tt tp tb -> pls le i c sk -> 0 <= i < L ->
  exists le',
    Clight2.exec_stmt sha_ge e le m (nd_read_stmt tt tp tb (nd_skip_set1 tb)) E0 le' m Out_normal /\
    pls le' (i + 1) c (nd_byte bs i).
Proof.
  intros HT (HP & Hc & Hk) Hi. destruct (pl_read tt tp tb le i HT HP) as (HP1 & O1 & O2).
  exists (PTree.set _skip (Vlong (Int64.repr (nd_byte bs i))) (nd_read_le bb ob bs tt tp tb le i)).
  pose proof HP as (Hli & _ & _ & _ & Hsp). split.
  - eapply nd_read_exec with (bs := bs); try eassumption; [exact (proj1 HT)|].
    apply exec_Sset. eapply eval_Ecast; [apply eval_Etempvar; apply nd_read_tb|reflexivity].
  - destruct HP1 as (A1 & A2 & A3 & A4 & A5). unfold pls, pl. rewrite PTree.gss. rewrite !PTree.gso by discriminate.
    rewrite O1. repeat split; assumption.
Qed.

(** [skip += (uint_fast32_t)(buf[i++]) << k] *)
Lemma pn_read_skipk tt tp tb k le i c sk :
  pn_trip tt tp tb -> pls le i c sk -> 0 <= i < L -> 0 <= sk < 4294967296 -> 8 <= k <= 24 ->
  exists le',
    Clight2.exec_stmt sha_ge e le m (nd_read_stmt tt tp tb (nd_skip_add tb k)) E0 le' m Out_normal /\
    pls le' (i + 1) c (sk + nd_byte bs i * 2 ^ k).
Proof.
  intros HT (HP & Hc & Hk) Hi Hs Hkr. destruct (pl_read tt tp tb le i HT HP) as (HP1 & O1 & O2).
  pose proof (nd_byte_range m len bb ob bs HBs i Hi) as HB.
  assert (HPw : 0 < 2 ^ k <= 2 ^ 24) by (split; [apply Z.pow_pos_nonneg; lia|apply Z.pow_le_mono_r; lia]).
  change (2 ^ 24) with 16777216 in HPw.
  exists (PTree.set _skip (Vlong (Int64.repr (sk + nd_byte bs i * 2 ^ k))) (nd_read_le bb ob bs tt tp tb le i)).
  pose proof HP as (Hli & _ & _ & _ & Hsp). split.
  - eapply nd_read_exec with (bs := bs); try eassumption; [exact (proj1 HT)|].
    apply exec_Sset.
    eapply eval_Ebinop with (v1 := Vlong (Int64.repr sk)) (v2 := Vlong (Int64.repr (nd_byte bs i * 2 ^ k))).
    + apply eval_Etempvar. rewrite O2. exact Hk.
    + eapply eval_Ebinop with (v1 := Vlong (Int64.repr (nd_byte bs i))) (v2 := Vint (Int.repr k)).
      * eapply eval_Ecast; [apply eval_Etempvar; apply nd_read_tb|reflexivity].
      * apply eval_Econst_int.
      * unfold sem_binary_operation, sem_shl, sem_shift.
        cbn [classify_shift typeof tulong tint typeconv remove_attributes].
        assert (HLt : Int.ltu (Int.repr k) Int64.iwordsize' = true).
        { unfold Int.ltu. rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
          change (Int.unsigned Int64.iwordsize') with 64. apply zlt_true. lia. }
        cbn. rewrite HLt. rewrite nd_i64_shl by lia. reflexivity.
    + rewrite <- (nd_i64_add sk (nd_byte bs i * 2 ^ k)) by nia. reflexivity.
  - destruct HP1 as (A1 & A2 & A3 & A4 & A5). unfold pls, pl. rewrite PTree.gss. rewrite !PTree.gso by discriminate.
    rewrite O1. repeat split; assumption.
Qed.

(** [if ( *allocationLen <= result->len || 0x60 < code) { result->op = NULL; return; }] *)
Lemma pn_check_exec le i (c : int) n :
  pl le i -> le!_code = Some (Vint c) -> 0 <= Int.unsigned c < 256 ->
  Mem.load Mint64 m bl ol = Some (Vlong (Int64.repr alen)) ->
  Mem.load Mint64 m br (or_ + 8) = Some (Vlong (Int64.repr n)) -> 0 <= n <= alen ->
  Mem.valid_access m Mptr br or_ Writable ->
  exists le',
    pl le' i /\ le'!_code = Some (Vint c) /\
    if (alen <=? n) || (96 <? Int.unsigned c)
    then exists m', Clight2.exec_stmt sha_ge e le m pn_check E0 le' m' (Out_return None) /\
           Mem.store Mptr m br or_ (Vlong Int64.zero) = Some m'
    else Clight2.exec_stmt sha_ge e le m pn_check E0 le' m Out_normal.
Proof.
  intros HP Hc Hcr HLa HLn Hn VA. pose proof HP as (Hli & Hr & Ha & Hal & Hsp).
  set (le39 := PTree.set _t'39 (Vlong (Int64.repr alen)) le).
  set (le40 := PTree.set _t'40 (Vlong (Int64.repr n)) le39).
  set (b1 := alen <=? n). set (b2 := 96 <? Int.unsigned c).
  set (le3 := PTree.set _t'3 (Val.of_bool (b1 || b2)) le40).
  assert (K39 : pn_keeps _t'39) by pn_keeps_tac.
  assert (K40 : pn_keeps _t'40) by pn_keeps_tac.
  assert (K3 : pn_keeps _t'3) by pn_keeps_tac.
  assert (HP3 : pl le3 i) by (unfold le3, le40, le39; repeat apply pl_set; assumption).
  assert (Hc3 : le3!_code = Some (Vint c)) by (unfold le3, le40, le39; rewrite !PTree.gso by discriminate; exact Hc).
  exists le3. split; [exact HP3|]. split; [exact Hc3|].
  assert (HCnd : eval_expr sha_ge e le40 m (Ebinop Ole (Etempvar _t'39 tulong) (Etempvar _t'40 tulong) tint)
    (Val.of_bool b1)).
  { eapply eval_Ebinop; [apply eval_Etempvar; unfold le40; rewrite PTree.gso by discriminate; apply PTree.gss
                        |apply eval_Etempvar; apply PTree.gss|].
    change (Some (Val.of_bool (negb (Int64.ltu (Int64.repr n) (Int64.repr alen)))) = Some (Val.of_bool b1)).
    rewrite nd_i64_ltu by lia. unfold b1.
    destruct (Z.ltb_spec n alen); destruct (Z.leb_spec alen n); try reflexivity; lia. }
  assert (XA : Clight2.exec_stmt sha_ge e le m
    (Ssequence (Sset _t'39 (Ederef (Etempvar _allocationLen (tptr tulong)) tulong))
      (Ssequence (Sset _t'40 (Efield PRES _len tulong))
        (Sifthenelse (Ebinop Ole (Etempvar _t'39 tulong) (Etempvar _t'40 tulong) tint)
          (Sset _t'3 (Econst_int (Int.repr 1) tint))
          (Sset _t'3 (Ecast (Ebinop Olt (Econst_int (Int.repr 96) tint) (Etempvar _code tuchar) tint) tbool)))))
    E0 le3 m Out_normal).
  { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le39) (m1 := m).
    { apply exec_Sset. apply pn_alen_value; [exact Hal|exact HLa]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le40) (m1 := m).
    { apply exec_Sset. apply pn_len_value; [unfold le39; rewrite PTree.gso by discriminate; exact Hr|exact HLn]. }
    eapply pn_if with (b := b1); [exact HCnd|reflexivity|].
    unfold le3. destruct b1; cbn [orb].
    - apply exec_Sset. apply eval_Econst_int.
    - apply exec_Sset. eapply eval_Ecast with (v1 := Val.of_bool b2).
      + apply nd_ev_lt_code; [unfold le40, le39; rewrite !PTree.gso by discriminate; exact Hc|lia|exact Hcr].
      + destruct b2; reflexivity. }
  assert (HT3 : eval_expr sha_ge e le3 m (Etempvar _t'3 tint) (Val.of_bool (b1 || b2)))
    by (apply eval_Etempvar; apply PTree.gss).
  unfold pn_check. destruct (b1 || b2) eqn:EB.
  - destruct (pn_fail_exec le3 m (proj1 (proj2 HP3)) VA) as (m' & XF & HSt).
    exists m'. split; [|exact HSt].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact XA|].
    eapply pn_if with (b := true); [exact HT3|reflexivity|exact XF].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact XA|].
    eapply pn_if with (b := false); [exact HT3|reflexivity|apply exec_Sskip].
Qed.
(** The push-length decoding with the store of the opcode's code. *)
Lemma pn_kind_exec le n i (c : int) :
  pls le i c 0 -> 1 <= i <= L -> 0 <= Int.unsigned c < 79 ->
  Mem.load Mptr m ba oa = Some (Vptr bop (Ptrofs.repr oop)) ->
  Mem.load Mint64 m br (or_ + 8) = Some (Vlong (Int64.repr n)) -> 0 <= n < alen ->
  Mem.range_perm m bop oop (oop + 36 * alen) Cur Writable ->
  Mem.valid_access m Mptr br or_ Writable ->
  match nd_skip len bs (Int.unsigned c) i with
  | Some (i', sk) =>
      exists le' m',
        Clight2.exec_stmt sha_ge e le m pn_kind E0 le' m' Out_normal /\
        pls le' i' c sk /\ i <= i' <= L /\ 0 <= sk < 4294967296 /\
        Mem.store Mint32 m bop (oop + 36 * n + 32) (Vint (Int.repr (pn_kindv (Int.unsigned c)))) = Some m'
  | None =>
      exists le' m',
        Clight2.exec_stmt sha_ge e le m pn_kind E0 le' m' (Out_return None) /\
        Mem.store Mptr m br or_ (Vlong Int64.zero) = Some m'
  end.
Proof.
  intros HS Hi Hc HLa HLn Hn PO VA. pose proof HS as (HP & Hcd & Hk). pose proof (nd_L len) as HLr. fold L in HLr.
  assert (Hc' : 0 <= Int.unsigned c < 256) by lia.
  assert (E1 : forall le0, le0!_code = Some (Vint c) -> forall k, 0 <= k < 256 ->
    eval_expr sha_ge e le0 m (Ebinop Olt (Etempvar _code tuchar) (Econst_int (Int.repr k) tint) tint)
      (Val.of_bool (Int.unsigned c <? k))).
  { intros le0 H0 k Hkk. apply nd_ev_code_lt; assumption. }
  (* storing the code in a state [le0] *)
  assert (SC : forall ta tn kv le0 i0 sk0,
    pn_keeps ta -> pn_keeps tn -> (forall (v : val) (le1 : temp_env), (PTree.set tn v le1)!ta = le1!ta) ->
    pls le0 i0 c sk0 ->
    exists le' m',
      Clight2.exec_stmt sha_ge e le0 m (pn_setcode ta tn (Econst_int (Int.repr kv) tint)) E0 le' m' Out_normal /\
      pls le' i0 c sk0 /\
      Mem.store Mint32 m bop (oop + 36 * n + 32) (Vint (Int.repr kv)) = Some m').
  { intros ta tn kv le0 i0 sk0 Ka Kn Hna HS0. pose proof HS0 as ((_ & Hr0 & Ha0 & _) & _).
    destruct (pn_setcode_exec ta tn (Econst_int (Int.repr kv) tint) (Int.repr kv) le0 m n Hr0 Ha0 Ka Kn Hna
      HLa HLn Hn PO ltac:(intros; apply eval_Econst_int) eq_refl) as (m' & XS & HSt).
    eexists _, m'. split; [exact XS|]. split; [|exact HSt]. apply pls_set; [exact Kn|]. apply pls_set; assumption. }
  unfold nd_skip, pn_kind, pn_kindv. fold L.
  pose proof (E1 le Hcd 76 ltac:(lia)) as C76.
  destruct (Int.unsigned c <? 76) eqn:E76.
  { (* immediate push *)
    set (le1 := PTree.set _skip (Vlong (Int64.repr (Int.unsigned c))) le).
    assert (HS1 : pls le1 i c (Int.unsigned c)).
    { destruct HP as (A1 & A2 & A3 & A4 & A5). unfold pls, pl, le1. rewrite PTree.gss, !PTree.gso by discriminate.
      repeat split; assumption. }
    destruct (SC _t'35 _t'36 0 le1 i (Int.unsigned c) ltac:(pn_keeps_tac) ltac:(pn_keeps_tac)
      ltac:(intros; rewrite PTree.gso by discriminate; reflexivity) HS1) as (le' & m' & XS & HS' & HSt).
    exists le', m'. split; [|split; [exact HS'|split; [lia|split; [lia|exact HSt]]]].
    eapply pn_if; [exact C76|reflexivity|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [|exact XS].
    apply exec_Sset. eapply eval_Ecast; [apply eval_Etempvar; exact Hcd|reflexivity]. }
  apply Z.ltb_ge in E76.
  rewrite (proj2 (Z.ltb_lt (Int.unsigned c) 79)) by lia.
  assert (K34 : pn_keeps _t'34) by pn_keeps_tac. assert (K29 : pn_keeps _t'29) by pn_keeps_tac.
  assert (K24 : pn_keeps _t'24) by pn_keeps_tac. assert (K21 : pn_keeps _t'21) by pn_keeps_tac.
  assert (T1 : pn_trip _t'4 _t'32 _t'33) by (unfold pn_trip, nd_trip; repeat split; try pn_keeps_tac;
    intros; rewrite ?PTree.gso by discriminate; repeat split; reflexivity).
  assert (T2 : pn_trip _t'5 _t'27 _t'28) by (unfold pn_trip, nd_trip; repeat split; try pn_keeps_tac;
    intros; rewrite ?PTree.gso by discriminate; repeat split; reflexivity).
  assert (T3 : pn_trip _t'6 _t'22 _t'23) by (unfold pn_trip, nd_trip; repeat split; try pn_keeps_tac;
    intros; rewrite ?PTree.gso by discriminate; repeat split; reflexivity).
  assert (T4 : pn_trip _t'7 _t'19 _t'20) by (unfold pn_trip, nd_trip; repeat split; try pn_keeps_tac;
    intros; rewrite ?PTree.gso by discriminate; repeat split; reflexivity).
  assert (HOuter : forall rest le' m' out,
    Clight2.exec_stmt sha_ge e le m rest E0 le' m' out ->
    Clight2.exec_stmt sha_ge e le m
      (Sifthenelse (Ebinop Olt (Etempvar _code tuchar) (Econst_int (Int.repr 76) tint) tint)
         (Ssequence (Sset _skip (Ecast (Etempvar _code tuchar) tulong))
            (pn_setcode _t'35 _t'36 (Econst_int (Int.repr 0) tint))) rest) E0 le' m' out).
  { intros rest le' m' out HX. eapply pn_if; [exact C76|reflexivity|exact HX]. }
  (* one length byte *)
  pose proof (pn_eof_exec _t'34 le i K34 HP ltac:(lia) VA) as X1.
  set (le1 := PTree.set _t'34 (Vint len) le) in *.
  assert (S1 : pls le1 i c 0) by (apply pls_set; assumption).
  revert X1. destruct (L =? i) eqn:EL1; intros X1.
  { destruct X1 as (m' & X1 & HSt). exists le1, m'. split; [|exact HSt].
    apply HOuter. eapply exec_Sseq_2; [exact X1|discriminate]. }
  apply Z.eqb_neq in EL1.
  destruct (pn_read_skip1 _t'4 _t'32 _t'33 le1 i c 0 T1 S1 ltac:(lia)) as (le2 & X2 & S2).
  pose proof (nd_byte_range m len bb ob bs HBs i ltac:(lia)) as B1.
  pose proof (E1 le2 (proj1 (proj2 S2)) 77 ltac:(lia)) as C77.
  destruct (Int.unsigned c <? 77) eqn:E77.
  { apply Z.ltb_lt in E77. rewrite (proj2 (Z.leb_gt 77 (Int.unsigned c))) by lia.
    destruct (SC _t'30 _t'31 1 le2 (i + 1) (nd_byte bs i) ltac:(pn_keeps_tac) ltac:(pn_keeps_tac)
      ltac:(intros; rewrite PTree.gso by discriminate; reflexivity) S2) as (le' & m' & XS & HS' & HSt).
    exists le', m'. split; [|split; [exact HS'|split; [lia|split; [lia|]]]].
    - apply HOuter. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X1|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X2|].
      eapply pn_if; [exact C77|reflexivity|exact XS].
    - exact HSt. }
  apply Z.ltb_ge in E77. rewrite (proj2 (Z.leb_le 77 (Int.unsigned c))) by lia.
  (* two length bytes *)
  pose proof (pn_eof_exec _t'29 le2 (i + 1) K29 (proj1 S2) ltac:(lia) VA) as X3.
  set (le3 := PTree.set _t'29 (Vint len) le2) in *.
  assert (S3 : pls le3 (i + 1) c (nd_byte bs i)) by (apply pls_set; assumption).
  revert X3. destruct (L =? i + 1) eqn:EL2; intros X3.
  { destruct X3 as (m' & X3 & HSt). exists le3, m'. split; [|exact HSt].
    apply HOuter. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X1|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X2|].
    eapply pn_if; [exact C77|reflexivity|]. eapply exec_Sseq_2; [exact X3|discriminate]. }
  apply Z.eqb_neq in EL2.
  destruct (pn_read_skipk _t'5 _t'27 _t'28 8 le3 (i + 1) c (nd_byte bs i) T2 S3 ltac:(lia) ltac:(lia) ltac:(lia))
    as (le4 & X4 & S4).
  pose proof (nd_byte_range m len bb ob bs HBs (i + 1) ltac:(lia)) as B2.
  pose proof (E1 le4 (proj1 (proj2 S4)) 78 ltac:(lia)) as C78.
  destruct (Int.unsigned c <? 78) eqn:E78.
  { apply Z.ltb_lt in E78. rewrite (proj2 (Z.leb_gt 78 (Int.unsigned c))) by lia.
    destruct (SC _t'25 _t'26 2 le4 (i + 1 + 1) (nd_byte bs i + nd_byte bs (i + 1) * 2 ^ 8)
      ltac:(pn_keeps_tac) ltac:(pn_keeps_tac)
      ltac:(intros; rewrite PTree.gso by discriminate; reflexivity) S4) as (le' & m' & XS & HS' & HSt).
    exists le', m'. split; [|split; [exact HS'|split; [lia|split; [change (2 ^ 8) with 256; lia|exact HSt]]]].
    apply HOuter. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X1|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X2|].
    eapply pn_if; [exact C77|reflexivity|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X3|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X4|].
    eapply pn_if; [exact C78|reflexivity|exact XS]. }
  apply Z.ltb_ge in E78. rewrite (proj2 (Z.leb_le 78 (Int.unsigned c))) by lia.
  (* four length bytes *)
  assert (HMid : forall rest le' m' out,
    Clight2.exec_stmt sha_ge e le4 m rest E0 le' m' out ->
    Clight2.exec_stmt sha_ge e le m
      (Sifthenelse (Ebinop Olt (Etempvar _code tuchar) (Econst_int (Int.repr 76) tint) tint)
         (Ssequence (Sset _skip (Ecast (Etempvar _code tuchar) tulong))
            (pn_setcode _t'35 _t'36 (Econst_int (Int.repr 0) tint)))
         (Ssequence (pn_eof _t'34)
           (Ssequence (nd_read_stmt _t'4 _t'32 _t'33 (nd_skip_set1 _t'33))
             (Sifthenelse (Ebinop Olt (Etempvar _code tuchar) (Econst_int (Int.repr 77) tint) tint)
               (pn_setcode _t'30 _t'31 (Econst_int (Int.repr 1) tint))
               (Ssequence (pn_eof _t'29)
                 (Ssequence (nd_read_stmt _t'5 _t'27 _t'28 (nd_skip_add _t'28 8))
                   (Sifthenelse (Ebinop Olt (Etempvar _code tuchar) (Econst_int (Int.repr 78) tint) tint)
                     (pn_setcode _t'25 _t'26 (Econst_int (Int.repr 2) tint)) rest))))))) E0 le' m' out).
  { intros rest le' m' out HX. apply HOuter.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X1|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X2|].
    eapply pn_if; [exact C77|reflexivity|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X3|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X4|].
    eapply pn_if; [exact C78|reflexivity|exact HX]. }
  pose proof (pn_eof_exec _t'24 le4 (i + 1 + 1) K24 (proj1 S4) ltac:(lia) VA) as X5.
  set (le5 := PTree.set _t'24 (Vint len) le4) in *.
  assert (S5 : pls le5 (i + 1 + 1) c (nd_byte bs i + nd_byte bs (i + 1) * 2 ^ 8)) by (apply pls_set; assumption).
  revert X5. destruct (L =? i + 1 + 1) eqn:EL3; intros X5.
  { destruct X5 as (m' & X5 & HSt). exists le5, m'. split; [|exact HSt].
    apply HMid. eapply exec_Sseq_2; [exact X5|discriminate]. }
  apply Z.eqb_neq in EL3.
  destruct (pn_read_skipk _t'6 _t'22 _t'23 16 le5 (i + 1 + 1) c (nd_byte bs i + nd_byte bs (i + 1) * 2 ^ 8)
    T3 S5 ltac:(lia) ltac:(change (2 ^ 8) with 256; lia) ltac:(lia)) as (le6 & X6 & S6).
  pose proof (nd_byte_range m len bb ob bs HBs (i + 1 + 1) ltac:(lia)) as B3.
  pose proof (pn_eof_exec _t'21 le6 (i + 1 + 1 + 1) K21 (proj1 S6) ltac:(lia) VA) as X7.
  set (le7 := PTree.set _t'21 (Vint len) le6) in *.
  assert (S7 : pls le7 (i + 1 + 1 + 1) c
    (nd_byte bs i + nd_byte bs (i + 1) * 2 ^ 8 + nd_byte bs (i + 1 + 1) * 2 ^ 16)) by (apply pls_set; assumption).
  revert X7. destruct (L =? i + 1 + 1 + 1) eqn:EL4; intros X7.
  { destruct X7 as (m' & X7 & HSt). exists le7, m'. split; [|exact HSt].
    apply HMid. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X5|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X6|].
    eapply exec_Sseq_2; [exact X7|discriminate]. }
  apply Z.eqb_neq in EL4.
  destruct (pn_read_skipk _t'7 _t'19 _t'20 24 le7 (i + 1 + 1 + 1) c
    (nd_byte bs i + nd_byte bs (i + 1) * 2 ^ 8 + nd_byte bs (i + 1 + 1) * 2 ^ 16)
    T4 S7 ltac:(lia) ltac:(change (2 ^ 8) with 256; change (2 ^ 16) with 65536; lia) ltac:(lia)) as (le8 & X8 & S8).
  pose proof (nd_byte_range m len bb ob bs HBs (i + 1 + 1 + 1) ltac:(lia)) as B4.
  destruct (SC _t'17 _t'18 3 le8 (i + 1 + 1 + 1 + 1)
    (nd_byte bs i + nd_byte bs (i + 1) * 2 ^ 8 + nd_byte bs (i + 1 + 1) * 2 ^ 16 + nd_byte bs (i + 1 + 1 + 1) * 2 ^ 24)
    ltac:(pn_keeps_tac) ltac:(pn_keeps_tac)
    ltac:(intros; rewrite PTree.gso by discriminate; reflexivity) S8) as (le' & m' & XS & HS' & HSt).
  exists le', m'. split; [|split; [exact HS'|split; [lia|split; [|exact HSt]]]].
  - apply HMid. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X5|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X6|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X7|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X8|exact XS].
  - change (2 ^ 8) with 256. change (2 ^ 16) with 65536. change (2 ^ 24) with 16777216. lia.
Qed.
End Script.
End ParseOps.
