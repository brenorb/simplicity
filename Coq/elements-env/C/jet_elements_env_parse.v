(** [parseNullData] (elements/env.c) against the functional parser
    [pn_run]: the prologue (compound literal and structure copy), the
    script-header test, the loop (jet_elements_env_parse_iter.v) and the
    epilogue that advances the caller's allocation cursor. *)
From Coq Require Import ZArith List Lia PeanoNat Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_struct_copy_loads.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_be32_exec C.jet_sha_block_local C.jet_sha_uchars_exec.
Require Import C.jet_sha_add_n_init C.jet_sha_ctx_abs C.jet_sha_compress_call C.jet_sha_tapdata_prep.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_hashbuffer C.jet_elements_env_nulldata_count.
Require Import C.jet_elements_env_countfee.
Require Import C.jet_elements_env_parse_defs C.jet_elements_env_parse_mem C.jet_elements_env_parse_ops.
Require Import C.jet_elements_env_parse_hash C.jet_elements_env_parse_iter.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Ltac zp :=
  repeat match goal with
         | H : ?a <> ?b |- _ => match type of a with block => clear H end
         end; lia.

Definition pn_env (bK bC bRs : block) : env :=
  PTree.set __res (bRs, CTX) (PTree.set _ctx (bC, CTX) (PTree.set ___compound (bK, PND) empty_env)).

Lemma pn_entry m m1 m2 m3 bK bC bRs v1 v2 v3 v4 :
  Mem.alloc m 0 16 = (m1, bK) -> Mem.alloc m1 0 88 = (m2, bC) -> Mem.alloc m2 0 88 = (m3, bRs) ->
  function_entry2 sha_ge f_parseNullData [v1; v2; v3; v4] m (pn_env bK bC bRs)
    (PTree.set _scriptPubKey v4 (PTree.set _allocationLen v3 (PTree.set _allocation v2
       (PTree.set _result v1 (create_undef_temps (fn_temps f_parseNullData)))))) m3.
Proof.
  intros A1 A2 A3. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst; try contradiction; discriminate.
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bK); [change (Mem.alloc m 0 16 = (m1, bK)); exact A1|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := bC); [change (Mem.alloc m1 0 88 = (m2, bC)); exact A2|].
    eapply alloc_variables_cons with (m1 := m3) (b1 := bRs); [change (Mem.alloc m2 0 88 = (m3, bRs)); exact A3|].
    constructor.
  - reflexivity.
Qed.

Lemma pn_blocks bK bC bRs :
  blocks_of_env sha_ge (pn_env bK bC bRs) = [(bC, 0, 88); (bK, 0, 16); (bRs, 0, 88)].
Proof. vm_compute. reflexivity. Qed.

Local Opaque sha_ge.

Lemma pn_int_eq_106 (c : int) : Int.eq (Int.repr 106) c = (Int.unsigned c =? 106).
Proof.
  unfold Int.eq. rewrite Int.unsigned_repr by (vm_compute; split; discriminate).
  destruct (zeq 106 (Int.unsigned c)); destruct (Z.eqb_spec (Int.unsigned c) 106); try reflexivity; lia.
Qed.

Section ParseParts.
Variable e : env.
Variables (bK : block) (br : block) (or_ : Z) (ba : block) (oa : Z) (bl : block) (ol : Z) (bop : block) (oop alen : Z).
Variables (bsp : block) (osp : Z) (len : int) (bb : block) (ob : ptrofs) (bs : list int).
Hypothesis HeK : e!___compound = Some (bK, PND).
Hypothesis Hor : 0 <= or_ /\ or_ + 16 <= Ptrofs.max_unsigned.
Hypothesis HorA : (8 | or_).
Hypothesis Hoa : 0 <= oa /\ oa + 8 <= Ptrofs.max_unsigned.
Hypothesis Hol : 0 <= ol /\ ol + 8 <= Ptrofs.max_unsigned.
Hypothesis Hoop : 0 <= oop /\ oop + 36 * alen <= Ptrofs.max_unsigned.
Hypothesis Halen : 0 <= alen <= 4294967295.
Hypothesis Hosp : 0 <= osp /\ osp + 16 <= Ptrofs.max_unsigned.

Let resv := Vptr br (Ptrofs.repr or_).

(** [*result = (parsedNullData){ .op = *allocation, .len = 0 };] *)
Lemma pn_init_exec le m :
  le!_result = Some resv -> le!_allocation = Some (Vptr ba (Ptrofs.repr oa)) ->
  Mem.load Mptr m ba oa = Some (Vptr bop (Ptrofs.repr oop)) ->
  Mem.range_perm m bK 0 16 Cur Writable -> Mem.range_perm m br or_ (or_ + 16) Cur Writable ->
  bK <> br -> bK <> ba ->
  exists m',
    Clight2.exec_stmt sha_ge e le m pn_init E0 (PTree.set _t'47 (Vptr bop (Ptrofs.repr oop)) le) m' Out_normal /\
    Mem.load Mptr m' br or_ = Some (Vptr bop (Ptrofs.repr oop)) /\
    Mem.load Mint64 m' br (or_ + 8) = Some (Vlong (Int64.repr 0)) /\
    (forall ch b ofs, b <> bK -> (b <> br \/ ofs + size_chunk ch <= or_ \/ or_ + 16 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Hr Ha HLa PK PR NKr NKa.
  set (le1 := PTree.set _t'47 (Vptr bop (Ptrofs.repr oop)) le).
  assert (VK1 : Mem.valid_access m Mptr bK 0 Writable).
  { split; [intros o Ho; apply PK; change (size_chunk Mptr) with 8 in Ho; zp|exists 0; reflexivity]. }
  destruct (Mem.valid_access_store m Mptr bK 0 (Vptr bop (Ptrofs.repr oop)) VK1) as [m1 S1].
  assert (VK2 : Mem.valid_access m1 Mint64 bK 8 Writable).
  { split; [intros o Ho; eapply Mem.perm_store_1; [exact S1|apply PK; change (size_chunk Mint64) with 8 in Ho; zp]
           |exists 1; reflexivity]. }
  destruct (Mem.valid_access_store m1 Mint64 bK 8 (Vlong (Int64.repr 0)) VK2) as [m2 S2].
  destruct (Mem.range_perm_loadbytes m2 bK 0 16) as [bytes HLB].
  { intros o Ho. eapply Mem.perm_implies with (p1 := Writable); [|constructor].
    eapply Mem.perm_store_1; [exact S2|]. eapply Mem.perm_store_1; [exact S1|]. apply PK. zp. }
  pose proof (Mem.loadbytes_length _ _ _ _ _ HLB) as HBL. change (Z.to_nat 16) with 16%nat in HBL.
  destruct (Mem.range_perm_storebytes m2 br or_ bytes) as [m3 S3].
  { rewrite HBL. change (Z.of_nat 16) with 16. intros o Ho.
    eapply Mem.perm_store_1; [exact S2|]. eapply Mem.perm_store_1; [exact S1|]. apply PR. exact Ho. }
  assert (HB3 : Mem.loadbytes m3 br or_ 16 = Some bytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ S3) as H. rewrite HBL in H. exact H. }
  assert (HK0 : Mem.load Mptr m2 bK 0 = Some (Vptr bop (Ptrofs.repr oop))).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ S2) by (right; left; change (size_chunk Mptr) with 8; zp).
    rewrite (Mem.load_store_same _ _ _ _ _ _ S1). reflexivity. }
  assert (HK8 : Mem.load Mint64 m2 bK 8 = Some (Vlong (Int64.repr 0))).
  { rewrite (Mem.load_store_same _ _ _ _ _ _ S2). reflexivity. }
  assert (HEK : forall le' m', eval_expr sha_ge e le' m' (Evar ___compound PND) (Vptr bK Ptrofs.zero)).
  { intros le' m'. eapply eval_Elvalue; [apply eval_Evar_local; exact HeK|apply deref_loc_copy; reflexivity]. }
  exists m3. split; [|split; [|split; [|split; [|split]]]].
  - unfold pn_init.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m2).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m1).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
        { apply exec_Sset. eapply eval_Elvalue; [apply eval_Ederef, eval_Etempvar; exact Ha|].
          eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv. rewrite Ptrofs.unsigned_repr by zp. exact HLa. }
        eapply exec_Sassign with (v2 := Vptr bop (Ptrofs.repr oop)) (v := Vptr bop (Ptrofs.repr oop)).
        - eapply eval_envu_field_lvalue; [reflexivity|exact envu_pnd_op|apply HEK].
        - apply eval_Etempvar. apply PTree.gss.
        - reflexivity.
        - eapply assign_loc_value; [reflexivity|]. exact S1. }
      eapply exec_Sassign with (v2 := Vint (Int.repr 0)) (v := Vlong (Int64.repr 0)).
      - eapply eval_envu_field_lvalue; [reflexivity|exact envu_pnd_len|apply HEK].
      - apply eval_Econst_int.
      - reflexivity.
      - eapply assign_loc_value; [reflexivity|]. exact S2. }
    eapply exec_Sassign with (v2 := Vptr bK Ptrofs.zero) (v := Vptr bK Ptrofs.zero).
    + apply eval_Ederef. apply eval_Etempvar. unfold le1. rewrite PTree.gso by discriminate. exact Hr.
    + apply HEK.
    + reflexivity.
    + eapply assign_loc_copy with (b' := bK) (ofs' := Ptrofs.zero) (bytes := bytes).
      * reflexivity.
      * intros _. change (typeof PRES) with PND. rewrite pn_blockcopy_PND. exists 0; reflexivity.
      * intros _. change (typeof PRES) with PND. rewrite pn_blockcopy_PND.
        rewrite Ptrofs.unsigned_repr by zp. exact HorA.
      * left. exact NKr.
      * change (typeof PRES) with PND. rewrite pn_sizeof_PND. exact HLB.
      * rewrite Ptrofs.unsigned_repr by zp. exact S3.
  - pose proof (equal_loadbytes_field Mptr m2 m3 bK br 0 or_ 16 0 bytes _ ltac:(zp)
                  ltac:(change (size_chunk Mptr) with 8; zp) HLB HB3
                  ltac:(rewrite Z.add_0_r; exact HorA) HK0) as H.
    rewrite Z.add_0_r in H. exact H.
  - apply (equal_loadbytes_field Mint64 m2 m3 bK br 0 or_ 16 8 bytes _ ltac:(zp)
             ltac:(change (size_chunk Mint64) with 8; zp) HLB HB3).
    + change (align_chunk Mint64) with 8. apply Z.divide_add_r; [exact HorA|exists 1; reflexivity].
    + exact HK8.
  - intros ch b ofs NK Hd.
    rewrite (Mem.load_storebytes_other _ _ _ _ _ S3)
      by (rewrite HBL; change (Z.of_nat 16) with 16; destruct Hd as [H|[H|H]]; [left; exact H|right; left; zp|right; right; zp]).
    rewrite (Mem.load_store_other _ _ _ _ _ _ S2) by (left; exact NK).
    apply (Mem.load_store_other _ _ _ _ _ _ S1). left; exact NK.
  - intros b ofs k p Hp. eapply Mem.perm_storebytes_1; [exact S3|].
    eapply Mem.perm_store_1; [exact S2|]. eapply Mem.perm_store_1; [exact S1|exact Hp].
  - intros b Hb. eapply Mem.storebytes_valid_block_1; [exact S3|].
    eapply Mem.store_valid_block_1; [exact S2|]. eapply Mem.store_valid_block_1; [exact S1|exact Hb].
Qed.
(** [if (0 == scriptPubKey->len || 0x6a != scriptPubKey->buf[0]) fail] *)
Lemma pn_head_exec le m :
  le!_result = Some resv -> le!_scriptPubKey = Some (Vptr bsp (Ptrofs.repr osp)) ->
  Mem.load Mint32 m bsp (osp + 8) = Some (Vint len) ->
  (0 < Int.unsigned len -> Mem.load Mptr m bsp osp = Some (Vptr bb ob)) ->
  (0 < Int.unsigned len -> Mem.load Mint8unsigned m bb (Ptrofs.unsigned ob) = Some (Vint (nd_b bs 0))) ->
  Mem.valid_access m Mptr br or_ Writable ->
  exists le',
    le'!_result = le!_result /\ le'!_allocation = le!_allocation /\
    le'!_allocationLen = le!_allocationLen /\ le'!_scriptPubKey = le!_scriptPubKey /\
    if (Int.unsigned len =? 0) || negb (nd_byte bs 0 =? 106)
    then exists m', Clight2.exec_stmt sha_ge e le m pn_head E0 le' m' (Out_return None) /\
           Mem.store Mptr m br or_ (Vlong Int64.zero) = Some m'
    else Clight2.exec_stmt sha_ge e le m pn_head E0 le' m Out_normal.
Proof.
  intros Hr Hsp HLen HBuf HB0 VA.
  set (le1 := PTree.set _t'44 (Vint len) le).
  assert (X44 : Clight2.exec_stmt sha_ge e le m (Sset _t'44 (Efield PSPK _len tuint)) E0 le1 m Out_normal).
  { apply exec_Sset. eapply eval_envu_field_value;
      [reflexivity|exact envu_rawElementsBuffer_len|reflexivity|apply eval_envu_deref_struct; exact Hsp|].
    rewrite envu_ptr_add_repr by zp. apply envu_loadv_repr; [zp|exact HLen]. }
  assert (HC0 : eval_expr sha_ge e le1 m
     (Ebinop Oeq (Econst_int (Int.repr 0) tint) (Etempvar _t'44 tuint) tint)
     (Val.of_bool (Int.unsigned len =? 0))).
  { eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; apply PTree.gss|].
    change (Some (Val.of_bool (Int.eq (Int.repr 0) len)) = Some (Val.of_bool (Int.unsigned len =? 0))).
    do 2 f_equal. unfold Int.eq. change (Int.unsigned (Int.repr 0)) with 0.
    destruct (zeq 0 (Int.unsigned len)); destruct (Z.eqb_spec (Int.unsigned len) 0); try reflexivity; lia. }
  destruct (Int.unsigned len =? 0) eqn:EL.
  { cbn [orb]. set (le2 := PTree.set _t'1 (Vint (Int.repr 1)) le1).
    assert (Hr2 : le2!_result = Some resv) by (unfold le2, le1; rewrite !PTree.gso by discriminate; exact Hr).
    destruct (pn_fail_exec e br or_ len Hor le2 m Hr2 VA) as (m' & XF & HS).
    exists le2. unfold le2, le1. rewrite !PTree.gso by discriminate.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exists m'. split; [|exact HS]. unfold pn_head.
    eapply pn_seq1.
    - eapply pn_seq1; [exact X44|]. eapply pn_if with (b := true); [exact HC0|reflexivity|].
      apply exec_Sset. apply eval_Econst_int.
    - eapply pn_if with (b := true); [apply eval_Etempvar; apply PTree.gss|reflexivity|exact XF]. }
  apply Z.eqb_neq in EL. cbn [orb].
  assert (HL : 0 < Int.unsigned len) by (pose proof (Int.unsigned_range len); lia).
  set (le2 := PTree.set _t'45 (Vptr bb ob) le1).
  set (le3 := PTree.set _t'46 (Vint (nd_b bs 0)) le2).
  assert (X45 : Clight2.exec_stmt sha_ge e le1 m (Sset _t'45 (Efield PSPK _buf (tptr tuchar))) E0 le2 m Out_normal).
  { apply exec_Sset. eapply eval_envu_field_value;
      [reflexivity|exact envu_rawElementsBuffer_buf|reflexivity
      |apply eval_envu_deref_struct; unfold le1; rewrite PTree.gso by discriminate; exact Hsp|].
    rewrite envu_ptr_add_repr by zp. apply envu_loadv_repr; [zp|]. rewrite Z.add_0_r. exact (HBuf HL). }
  assert (X46 : Clight2.exec_stmt sha_ge e le2 m
     (Sset _t'46 (Ederef (Ebinop Oadd (Etempvar _t'45 (tptr tuchar)) (Econst_int (Int.repr 0) tint)
                            (tptr tuchar)) tuchar)) E0 le3 m Out_normal).
  { apply exec_Sset. eapply eval_Elvalue with (loc := bb) (ofs := ob) (bf := Full).
    - apply eval_Ederef. eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|apply eval_Econst_int|].
      change (Some (Vptr bb (Ptrofs.add ob (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 0))))) =
              Some (Vptr bb ob)).
      change (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_ints (Int.repr 0))) with (Ptrofs.repr 0).
      rewrite pn_add0. reflexivity.
    - eapply deref_loc_value; [reflexivity|]. exact (HB0 HL). }
  assert (XT : forall b0 : bool, b0 = negb (nd_byte bs 0 =? 106) ->
     Clight2.exec_stmt sha_ge e le3 m
       (Sset _t'1 (Ecast (Ebinop One (Econst_int (Int.repr 106) tint) (Etempvar _t'46 tuchar) tint) tbool))
       E0 (PTree.set _t'1 (Val.of_bool b0) le3) m Out_normal).
  { intros b0 Hb0. apply exec_Sset. eapply eval_Ecast with (v1 := Val.of_bool b0).
    - eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; apply PTree.gss|].
      change (Some (Val.of_bool (negb (Int.eq (Int.repr 106) (nd_b bs 0)))) = Some (Val.of_bool b0)).
      rewrite pn_int_eq_106, Hb0. reflexivity.
    - destruct b0; reflexivity. }
  assert (Hr4 : forall v, (PTree.set _t'1 v le3)!_result = Some resv)
    by (intros v; unfold le3, le2, le1; rewrite !PTree.gso by discriminate; exact Hr).
  destruct (negb (nd_byte bs 0 =? 106)) eqn:EB.
  - destruct (pn_fail_exec e br or_ len Hor (PTree.set _t'1 (Val.of_bool true) le3) m (Hr4 _) VA) as (m' & XF & HS).
    exists (PTree.set _t'1 (Val.of_bool true) le3). unfold le3, le2, le1. rewrite !PTree.gso by discriminate.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exists m'. split; [|exact HS]. unfold pn_head.
    eapply pn_seq1.
    + eapply pn_seq1; [exact X44|]. eapply pn_if with (b := false); [exact HC0|reflexivity|].
      eapply pn_seq1; [exact X45|]. eapply pn_seq1; [exact X46|exact (XT true eq_refl)].
    + eapply pn_if with (b := true); [apply eval_Etempvar; apply PTree.gss|reflexivity|exact XF].
  - exists (PTree.set _t'1 (Val.of_bool false) le3). unfold le3, le2, le1. rewrite !PTree.gso by discriminate.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    unfold pn_head.
    eapply pn_seq1.
    + eapply pn_seq1; [exact X44|]. eapply pn_if with (b := false); [exact HC0|reflexivity|].
      eapply pn_seq1; [exact X45|]. eapply pn_seq1; [exact X46|exact (XT false eq_refl)].
    + eapply pn_if with (b := false); [apply eval_Etempvar; apply PTree.gss|reflexivity|apply exec_Sskip].
Qed.

(** [*allocation += result->len; *allocationLen -= result->len;] *)
Lemma pn_finish_exec le m n :
  le!_result = Some resv -> le!_allocation = Some (Vptr ba (Ptrofs.repr oa)) ->
  le!_allocationLen = Some (Vptr bl (Ptrofs.repr ol)) ->
  Mem.load Mptr m ba oa = Some (Vptr bop (Ptrofs.repr oop)) ->
  Mem.load Mint64 m br (or_ + 8) = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bl ol = Some (Vlong (Int64.repr alen)) -> 0 <= n <= alen ->
  Mem.valid_access m Mptr ba oa Writable -> Mem.valid_access m Mint64 bl ol Writable ->
  ba <> br -> ba <> bl ->
  exists le' m1 m',
    Clight2.exec_stmt sha_ge e le m pn_finish E0 le' m' Out_normal /\
    Mem.store Mptr m ba oa (Vptr bop (Ptrofs.repr (oop + 36 * n))) = Some m1 /\
    Mem.store Mint64 m1 bl ol (Vlong (Int64.repr (alen - n))) = Some m'.
Proof.
  intros Hr Ha Hl HLa HLn HLl Hn VAa VAl Nar Nal.
  destruct (Mem.valid_access_store m Mptr ba oa (Vptr bop (Ptrofs.repr (oop + 36 * n))) VAa) as [m1 S1].
  destruct (Mem.valid_access_store m1 Mint64 bl ol (Vlong (Int64.repr (alen - n)))
              (Mem.store_valid_access_1 _ _ _ _ _ _ S1 _ _ _ _ VAl)) as [m2 S2].
  set (le1 := PTree.set _t'10 (Vptr bop (Ptrofs.repr oop)) le).
  set (le2 := PTree.set _t'11 (Vlong (Int64.repr n)) le1).
  set (le3 := PTree.set _t'8 (Vlong (Int64.repr alen)) le2).
  set (le4 := PTree.set _t'9 (Vlong (Int64.repr n)) le3).
  exists le4, m1, m2. split; [|split; assumption]. unfold pn_finish.
  eapply pn_seq1 with (le1 := le2) (m1 := m1).
  - eapply pn_seq1 with (le1 := le1) (m1 := m).
    { apply exec_Sset. eapply eval_Elvalue; [apply eval_Ederef, eval_Etempvar; exact Ha|].
      eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv. rewrite Ptrofs.unsigned_repr by zp. exact HLa. }
    eapply pn_seq1 with (le1 := le2) (m1 := m).
    { apply exec_Sset. apply (pn_len_value e br or_ len Hor le1 m);
        [unfold le1; rewrite PTree.gso by discriminate; exact Hr|exact HLn]. }
    eapply exec_Sassign with (v2 := Vptr bop (Ptrofs.repr (oop + 36 * n))) (v := Vptr bop (Ptrofs.repr (oop + 36 * n))).
    + apply eval_Ederef. apply eval_Etempvar. unfold le2, le1. rewrite !PTree.gso by discriminate. exact Ha.
    + eapply eval_Ebinop; [apply eval_Etempvar; unfold le2; rewrite PTree.gso by discriminate; apply PTree.gss
                          |apply eval_Etempvar; apply PTree.gss|].
      rewrite <- (cf_ptr_index oop 36 n) by (change Ptrofs.max_unsigned with 18446744073709551615 in *; zp).
      rewrite <- pn_sizeof_OPC. reflexivity.
    + reflexivity.
    + eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite Ptrofs.unsigned_repr by zp. exact S1.
  - eapply pn_seq1 with (le1 := le3) (m1 := m1).
    { apply exec_Sset. eapply eval_Elvalue;
        [apply eval_Ederef, eval_Etempvar; unfold le2, le1; rewrite !PTree.gso by discriminate; exact Hl|].
      eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv. rewrite Ptrofs.unsigned_repr by zp.
      rewrite (Mem.load_store_other _ _ _ _ _ _ S1) by (left; apply not_eq_sym; exact Nal). exact HLl. }
    eapply pn_seq1 with (le1 := le4) (m1 := m1).
    { apply exec_Sset. apply (pn_len_value e br or_ len Hor le3 m1);
        [unfold le3, le2, le1; rewrite !PTree.gso by discriminate; exact Hr|].
      rewrite (Mem.load_store_other _ _ _ _ _ _ S1) by (left; apply not_eq_sym; exact Nar). exact HLn. }
    eapply exec_Sassign with (v2 := Vlong (Int64.repr (alen - n))) (v := Vlong (Int64.repr (alen - n))).
    + apply eval_Ederef. apply eval_Etempvar. unfold le4, le3, le2, le1. rewrite !PTree.gso by discriminate. exact Hl.
    + eapply eval_Ebinop; [apply eval_Etempvar; unfold le4; rewrite PTree.gso by discriminate; apply PTree.gss
                          |apply eval_Etempvar; apply PTree.gss|].
      rewrite <- (nd_i64_sub alen n) by zp. reflexivity.
    + reflexivity.
    + eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite Ptrofs.unsigned_repr by zp. exact S2.
Qed.
End ParseParts.
