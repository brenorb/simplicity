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

(** The functional parser: [None] is [result->op = NULL]. *)
Definition pn_run (alen : Z) (len : int) (bs : list int) : option (list pn_ent) :=
  if (Int.unsigned len =? 0) || negb (nd_byte bs 0 =? 106) then None
  else pn_loop alen len bs (Z.to_nat (Int.unsigned len)) 0 1 [].

Lemma pn_load_valid ch m b ofs v : Mem.load ch m b ofs = Some v -> Mem.valid_block m b.
Proof.
  intros H. eapply Mem.valid_access_valid_block.
  eapply Mem.valid_access_implies; [exact (Mem.load_valid_access _ _ _ _ _ H)|constructor].
Qed.

Lemma pn_ent_at_ext bop oop m m' k en :
  (forall ch ofs, Mem.load ch m' bop ofs = Mem.load ch m bop ofs) ->
  pn_ent_at bop oop m k en -> pn_ent_at bop oop m' k en.
Proof.
  intros H [H1 H2]. split; [rewrite H; exact H1|].
  destruct (snd en); [intros j Hj; rewrite H; apply H2, Hj|exact I].
Qed.

Theorem eval_parseNullData (Hmodel : memcpy_model) m br or_ ba oa bl ol bop oop alen bsp osp len bb ob bs :
  0 <= or_ /\ or_ + 16 <= Ptrofs.max_unsigned -> (8 | or_) ->
  0 <= oa /\ oa + 8 <= Ptrofs.max_unsigned -> 0 <= ol /\ ol + 8 <= Ptrofs.max_unsigned ->
  0 <= oop /\ oop + 36 * alen <= Ptrofs.max_unsigned -> (4 | oop) -> 0 <= alen <= 4294967295 ->
  0 <= osp /\ osp + 16 <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned ob + Int.unsigned len <= Ptrofs.max_unsigned ->
  Mem.load Mptr m ba oa = Some (Vptr bop (Ptrofs.repr oop)) ->
  Mem.load Mint64 m bl ol = Some (Vlong (Int64.repr alen)) ->
  Mem.load Mint32 m bsp (osp + 8) = Some (Vint len) ->
  (0 < Int.unsigned len -> Mem.load Mptr m bsp osp = Some (Vptr bb ob)) ->
  (forall i, 0 <= i < Int.unsigned len ->
     Mem.load Mint8unsigned m bb (Ptrofs.unsigned ob + i) = Some (Vint (nth (Z.to_nat i) bs Int.zero))) ->
  Mem.range_perm m br or_ (or_ + 16) Cur Writable ->
  Mem.range_perm m bop oop (oop + 36 * alen) Cur Writable -> Mem.valid_block m bop ->
  Mem.valid_access m Mptr ba oa Writable -> Mem.valid_access m Mint64 bl ol Writable ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  (br <> bop \/ or_ + 16 <= oop \/ oop + 36 * alen <= or_) ->
  ba <> bop -> bl <> bop -> bsp <> bop -> bb <> bop -> GC <> bop -> GM <> bop ->
  ba <> br -> bl <> br -> bsp <> br -> bb <> br -> GC <> br -> GM <> br -> ba <> bl ->
  exists mf,
    Clight2.eval_funcall sha_ge m (Internal f_parseNullData)
      [Vptr br (Ptrofs.repr or_); Vptr ba (Ptrofs.repr oa); Vptr bl (Ptrofs.repr ol); Vptr bsp (Ptrofs.repr osp)]
      E0 mf Vundef /\
    match pn_run alen len bs with
    | None =>
        Mem.load Mptr mf br or_ = Some (Vlong Int64.zero) /\
        (forall ch b ofs, Mem.valid_block m b ->
           (b <> br \/ ofs + size_chunk ch <= or_ \/ or_ + 16 <= ofs) ->
           (b <> bop \/ ofs + size_chunk ch <= oop \/ oop + 36 * alen <= ofs) ->
           Mem.load ch mf b ofs = Mem.load ch m b ofs)
    | Some ents =>
        Z.of_nat (length ents) <= alen /\
        Mem.load Mptr mf br or_ = Some (Vptr bop (Ptrofs.repr oop)) /\
        Mem.load Mint64 mf br (or_ + 8) = Some (Vlong (Int64.repr (Z.of_nat (length ents)))) /\
        (forall k, (k < length ents)%nat -> pn_ent_at bop oop mf (Z.of_nat k) (nth k ents (0, None))) /\
        Mem.load Mptr mf ba oa = Some (Vptr bop (Ptrofs.repr (oop + 36 * Z.of_nat (length ents)))) /\
        Mem.load Mint64 mf bl ol = Some (Vlong (Int64.repr (alen - Z.of_nat (length ents)))) /\
        (forall ch b ofs, Mem.valid_block m b ->
           (b <> br \/ ofs + size_chunk ch <= or_ \/ or_ + 16 <= ofs) ->
           (b <> bop \/ ofs + size_chunk ch <= oop \/ oop + 36 * alen <= ofs) ->
           (b <> ba \/ ofs + size_chunk ch <= oa \/ oa + 8 <= ofs) ->
           (b <> bl \/ ofs + size_chunk ch <= ol \/ ol + 8 <= ofs) ->
           Mem.load ch mf b ofs = Mem.load ch m b ofs)
    end /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm mf b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros Hor HorA Hoa Hol Hoop HoopA Halen Hosp HobM HLa HLl HLen HBuf HBs PR PO Vop VAa VAl Hdisp HMax Hsep
    Nba Nbl Nbsp Nbb NG NM Nbar Nblr Nbspr Nbbr NGr NMr Nbal.
  assert (VG : Mem.valid_block m GC).
  { pose proof Hdisp as Hd'. unfold sha_dispatch_ok in Hd'. exact (pn_load_valid _ _ _ _ _ Hd'). }
  pose proof (pn_load_valid _ _ _ _ _ HMax) as VM.
  assert (Vr : Mem.valid_block m br) by (eapply Mem.perm_valid_block; apply (PR or_); zp).
  pose proof (pn_load_valid _ _ _ _ _ HLa) as Va.
  pose proof (pn_load_valid _ _ _ _ _ HLl) as Vl.
  pose proof (pn_load_valid _ _ _ _ _ HLen) as Vsp.
  destruct (Mem.alloc m 0 16) as [ma1 bK] eqn:A1.
  destruct (Mem.alloc ma1 0 88) as [ma2 bC] eqn:A2.
  destruct (Mem.alloc ma2 0 88) as [m0 bRs] eqn:A3.
  assert (HAL : alloc_list m [16; 88; 88] = (m0, [bK; bC; bRs])).
  { cbn [alloc_list]. rewrite A1, A2, A3. reflexivity. }
  destruct (alloc_list_props _ _ _ _ HAL) as ((XV & XL & XP & XA) & FRh & ND & FA).
  inversion FA as [|? ? ? ? [PK0 VK0] FA1]; subst.
  inversion FA1 as [|? ? ? ? [PC0 VC0] FA2]; subst.
  inversion FA2 as [|? ? ? ? [PRs0 VRs0] FA3]; subst. clear FA FA1 FA2 FA3 HAL.
  assert (DL : bK <> bC /\ bK <> bRs /\ bC <> bRs).
  { inversion ND as [|? ? HN1 ND1]; subst. inversion ND1 as [|? ? HN2 _]; subst. cbn [In] in HN1, HN2.
    repeat split; intro E;
      [apply HN1; left; symmetry; exact E|apply HN1; right; left; symmetry; exact E|apply HN2; left; symmetry; exact E]. }
  destruct DL as (DKC & DKR & DCR).
  assert (NF : forall b, Mem.valid_block m b -> b <> bK /\ b <> bC /\ b <> bRs).
  { intros b Hb. pose proof (FRh b Hb) as HN. cbn [In] in HN.
    repeat split; intro E; apply HN; rewrite E; tauto. }
  destruct (NF GC VG) as (G1 & G2 & G3). destruct (NF GM VM) as (M1 & M2 & M3).
  destruct (NF bop Vop) as (O1 & O2 & O3). destruct (NF br Vr) as (R1 & R2 & R3).
  destruct (NF ba Va) as (Q1 & Q2 & Q3). destruct (NF bl Vl) as (T1 & T2 & T3).
  destruct (NF bsp Vsp) as (U1 & U2 & U3).
  set (e := pn_env bK bC bRs).
  set (le0 := PTree.set _scriptPubKey (Vptr bsp (Ptrofs.repr osp)) (PTree.set _allocationLen (Vptr bl (Ptrofs.repr ol))
     (PTree.set _allocation (Vptr ba (Ptrofs.repr oa)) (PTree.set _result (Vptr br (Ptrofs.repr or_))
        (create_undef_temps (fn_temps f_parseNullData)))))).
  (* the common ending: free the three locals *)
  assert (FIN : forall le' mX out,
    Clight2.exec_stmt sha_ge e le0 m0 (fn_body f_parseNullData) E0 le' mX out ->
    out = Out_normal \/ out = Out_return None ->
    (forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm mX b ofs k p) ->
    exists mf,
      Clight2.eval_funcall sha_ge m (Internal f_parseNullData)
        [Vptr br (Ptrofs.repr or_); Vptr ba (Ptrofs.repr oa); Vptr bl (Ptrofs.repr ol); Vptr bsp (Ptrofs.repr osp)]
        E0 mf Vundef /\
      (forall ch b ofs, Mem.valid_block m b -> Mem.load ch mf b ofs = Mem.load ch mX b ofs) /\
      (forall b ofs k p, Mem.valid_block m b -> Mem.perm mX b ofs k p -> Mem.perm mf b ofs k p) /\
      (forall b, Mem.valid_block mX b -> Mem.valid_block mf b)).
  { intros le' mX out HX Hout HPX.
    destruct (free_list_blocks [(bC, 0, 88); (bK, 0, 16); (bRs, 0, 88)] mX) as (mf & HFL & HLf & HPf & HVf).
    { intros b0 lo hi HIn o Ho. cbn [In] in HIn. apply HPX.
      destruct HIn as [E|[E|[E|[]]]]; injection E as <- <- <-; [apply PC0|apply PK0|apply PRs0]; exact Ho. }
    { cbn [map fst]. apply NoDup_cons; [cbn [In]; intros [E|[E|[]]]; [exact (DKC E)|exact (DCR (eq_sym E))]|].
      apply NoDup_cons; [cbn [In]; intros [E|[]]; exact (DKR (eq_sym E))|].
      apply NoDup_cons; [intros []|apply NoDup_nil]. }
    cbn [map fst] in HLf, HPf.
    assert (NIn : forall b, Mem.valid_block m b -> ~ In b [bC; bK; bRs]).
    { intros b Hb HIn. destruct (NF b Hb) as (? & ? & ?). cbn [In] in HIn.
      repeat (destruct HIn as [HIn|HIn]; [symmetry in HIn; contradiction|]). exact HIn. }
    exists mf. split; [|split; [|split]].
    - eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m0) (le2 := le') (m2 := mX) (out := out).
      + eapply pn_entry; eassumption.
      + exact HX.
      + destruct Hout as [-> | ->]; reflexivity.
      + unfold e. rewrite pn_blocks. exact HFL.
    - intros ch b ofs Hb. apply HLf, NIn, Hb.
    - intros b ofs k p Hb Hp. apply HPf; [apply NIn, Hb|exact Hp].
    - exact HVf. }
  (* the prologue *)
  assert (HLa0 : Mem.load Mptr m0 ba oa = Some (Vptr bop (Ptrofs.repr oop))) by (rewrite XL by exact Va; exact HLa).
  destruct (pn_init_exec e bK br or_ ba oa bop oop eq_refl Hor HorA Hoa le0 m0 eq_refl eq_refl HLa0) as
    (m1 & XI & HI1 & HI2 & LI & PI & VI).
  { intros o Ho. eapply Mem.perm_implies; [apply PK0, Ho|constructor]. }
  { intros o Ho. apply XP, PR, Ho. }
  { apply not_eq_sym. exact R1. }
  { apply not_eq_sym. exact Q1. }
  set (le1 := PTree.set _t'47 (Vptr bop (Ptrofs.repr oop)) le0) in *.
  assert (K1 : forall ch b ofs, Mem.valid_block m b ->
     (b <> br \/ ofs + size_chunk ch <= or_ \/ or_ + 16 <= ofs) -> Mem.load ch m1 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb Hd. destruct (NF b Hb) as (? & ? & ?). rewrite LI by assumption. apply XL, Hb. }
  assert (P1 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m1 b ofs k p).
  { intros b ofs k p Hp. apply PI, XP, Hp. }
  assert (HLen1 : Mem.load Mint32 m1 bsp (osp + 8) = Some (Vint len)).
  { rewrite K1 by (try exact Vsp; left; exact Nbspr). exact HLen. }
  assert (HBuf1 : 0 < Int.unsigned len -> Mem.load Mptr m1 bsp osp = Some (Vptr bb ob)).
  { intros HL. rewrite K1 by (try exact Vsp; left; exact Nbspr). exact (HBuf HL). }
  assert (Vbb : 0 < Int.unsigned len -> Mem.valid_block m bb).
  { intros HL. exact (pn_load_valid _ _ _ _ _ (HBs 0 ltac:(zp))). }
  assert (HBs1 : forall i, 0 <= i < Int.unsigned len ->
     Mem.load Mint8unsigned m1 bb (Ptrofs.unsigned ob + i) = Some (Vint (nth (Z.to_nat i) bs Int.zero))).
  { intros i Hi. rewrite K1 by (try (apply Vbb; zp); left; exact Nbbr). exact (HBs i Hi). }
  assert (HB01 : 0 < Int.unsigned len -> Mem.load Mint8unsigned m1 bb (Ptrofs.unsigned ob) = Some (Vint (nd_b bs 0))).
  { intros HL. pose proof (HBs1 0 ltac:(zp)) as H. rewrite Z.add_0_r in H. exact H. }
  assert (VA1 : Mem.valid_access m1 Mptr br or_ Writable).
  { split; [intros o Ho; apply P1, PR; change (size_chunk Mptr) with 8 in Ho; zp|exact HorA]. }
  destruct (pn_head_exec e br or_ bsp osp len bb ob bs Hor Hosp le1 m1 eq_refl eq_refl HLen1 HBuf1 HB01 VA1)
    as (le2 & E1 & E2 & E3 & E4 & HH).
  unfold pn_run. destruct ((Int.unsigned len =? 0) || negb (nd_byte bs 0 =? 106)) eqn:EBad.
  { (* not a null-data script *)
    destruct HH as (m2 & XH & HS).
    destruct (FIN le2 m2 (Out_return None)) as (mf & XF & HLf & HPf & HVf).
    { rewrite parseNullData_body_shape. eapply pn_seq1; [exact XI|]. apply pn_seqr. exact XH. }
    { right; reflexivity. }
    { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact HS|]. apply PI, Hp. }
    exists mf. split; [exact XF|]. split; [split|split].
    - rewrite HLf by exact Vr. rewrite (Mem.load_store_same _ _ _ _ _ _ HS). reflexivity.
    - intros ch b ofs Hb Hd1 Hd2. rewrite HLf by exact Hb.
      rewrite (Mem.load_store_other _ _ _ _ _ _ HS)
        by (change (size_chunk Mptr) with 8; destruct Hd1 as [H|[H|H]]; [left; exact H|right; left; exact H|right; right; zp]).
      apply K1; assumption.
    - intros b ofs k p Hb Hp. apply HPf; [exact Hb|]. eapply Mem.perm_store_1; [exact HS|]. apply P1, Hp.
    - intros b Hb. apply HVf. eapply Mem.store_valid_block_1; [exact HS|]. apply VI, XV, Hb. }
  apply orb_false_elim in EBad. destruct EBad as [EL0 _]. apply Z.eqb_neq in EL0.
  assert (HL : 0 < Int.unsigned len) by (pose proof (Int.unsigned_range len); zp).
  destruct (NF bb (Vbb HL)) as (W1 & W2 & W3).
  set (le3 := PTree.set _i (Vlong (Int64.repr 1)) le2).
  assert (XS : Clight2.exec_stmt sha_ge e le2 m1 (Sset _i (Ecast (Econst_int (Int.repr 1) tint) tulong))
                 E0 le3 m1 Out_normal).
  { apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity]. }
  assert (HP3 : pl br or_ ba oa bl ol bsp osp le3 1).
  { unfold pl, le3. rewrite PTree.gss, !PTree.gso by discriminate. rewrite E1, E2, E3, E4.
    repeat split; reflexivity. }
  assert (HM1 : pm bC bRs br or_ ba oa bl ol bop oop alen bsp osp len bb ob bs m1 0 []).
  { assert (C5 : Mem.load Mptr m1 ba oa = Some (Vptr bop (Ptrofs.repr oop)))
      by (rewrite K1 by (try exact Va; left; exact Nbar); exact HLa).
    assert (C6 : Mem.load Mint64 m1 bl ol = Some (Vlong (Int64.repr alen)))
      by (rewrite K1 by (try exact Vl; left; exact Nblr); exact HLl).
    assert (C10 : forall k, (k < length (@nil pn_ent))%nat ->
       pn_ent_at bop oop m1 (Z.of_nat k) (nth k (@nil pn_ent) (0, None))) by (intros k Hk; inversion Hk).
    assert (C12 : Mem.valid_access m1 Mint64 br (or_ + 8) Writable).
    { split; [intros o Ho; apply P1, PR; change (size_chunk Mint64) with 8 in Ho; zp
             |change (align_chunk Mint64) with 8; apply Z.divide_add_r; [exact HorA|exists 1; reflexivity]]. }
    assert (C13 : Mem.range_perm m1 bop oop (oop + 36 * alen) Cur Writable) by (intros o Ho; apply P1, PO, Ho).
    assert (C14 : Mem.range_perm m1 bC 0 88 Cur Freeable) by (intros o Ho; apply PI, PC0, Ho).
    assert (C15 : Mem.range_perm m1 bRs 0 88 Cur Freeable) by (intros o Ho; apply PI, PRs0, Ho).
    assert (C16 : sha_dispatch_ok m1).
    { unfold sha_dispatch_ok. rewrite K1 by (try exact VG; left; exact NGr). exact Hdisp. }
    assert (C17 : Mem.load Mint64 m1 GM 0 = Some (Vlong sha_max_counter))
      by (rewrite K1 by (try exact VM; left; exact NMr); exact HMax).
    exact (conj eq_refl (conj (proj1 Halen) (conj HI1 (conj HI2 (conj C5 (conj C6 (conj HLen1 (conj HBuf1
      (conj HBs1 (conj C10 (conj VA1 (conj C12 (conj C13 (conj C14 (conj C15 (conj C16 C17)))))))))))))))). }
  pose proof (pn_loop_exec Hmodel e bC bRs eq_refl eq_refl eq_refl eq_refl eq_refl br or_ ba oa bl ol bop oop alen
    bsp osp len bb ob bs Hor Hoa Hol Hoop HoopA Halen Hosp HobM Hsep Nba Nbl Nbsp Nbb NG NM Nbar Nblr Nbspr Nbbr
    NGr NMr R2 R3 Q2 Q3 T2 T3 O2 O3 U2 U3 W2 W3 G2 G3 M2 M3 (not_eq_sym DCR)
    (Z.to_nat (Int.unsigned len)) le3 m1 0 [] 1 HM1 HP3 ltac:(zp) ltac:(zp)) as HLoop.
  destruct (pn_loop alen len bs (Z.to_nat (Int.unsigned len)) 0 1 []) as [ents|].
  2: { (* a parse failure inside the loop *)
    destruct HLoop as (le4 & m4 & XL4 & HL4 & (LF & PF & VF)).
    destruct (FIN le4 m4 (Out_return None)) as (mf & XF & HLf & HPf & HVf).
    { rewrite parseNullData_body_shape. eapply pn_seq1; [exact XI|]. eapply pn_seq1; [exact HH|].
      apply pn_seqr. eapply pn_seq1; [exact XS|exact XL4]. }
    { right; reflexivity. }
    { intros b ofs k p Hp. apply PF; [apply VI; eapply Mem.perm_valid_block; exact Hp|apply PI, Hp]. }
    exists mf. split; [exact XF|]. split; [split|split].
    - rewrite HLf by exact Vr. exact HL4.
    - intros ch b ofs Hb Hd1 Hd2. rewrite HLf by exact Hb. destruct (NF b Hb) as (? & ? & ?).
      rewrite LF by (try assumption; apply VI, XV, Hb). apply K1; assumption.
    - intros b ofs k p Hb Hp. apply HPf; [exact Hb|]. apply PF; [apply VI, XV, Hb|apply P1, Hp].
    - intros b Hb. apply HVf, VF, VI, XV, Hb. }
  destruct HLoop as (le4 & m4 & n' & i' & XL4 & HM4 & HP4 & (LF & PF & VF)).
  pose proof HM4 as (HN & HNa & Hop4 & Hlen4 & Hal4 & Hall4 & _ & _ & _ & Hents4 & _).
  subst n'. destruct HP4 as (_ & Hr4 & Ha4 & Hl4 & _).
  assert (P4 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m4 b ofs k p).
  { intros b ofs k p Hp. apply PF; [apply VI, XV; eapply Mem.perm_valid_block; exact Hp|apply P1, Hp]. }
  destruct (pn_finish_exec e br or_ ba oa bl ol bop oop alen len Hor Hoa Hol Hoop Halen le4 m4
              (Z.of_nat (length ents)) Hr4 Ha4 Hl4 Hal4 Hlen4 Hall4 ltac:(zp)) as (le5 & m5 & m6 & XFn & S5 & S6).
  { split; [intros o Ho; apply P4; exact (proj1 VAa o Ho)|exact (proj2 VAa)]. }
  { split; [intros o Ho; apply P4; exact (proj1 VAl o Ho)|exact (proj2 VAl)]. }
  { exact Nbar. }
  { exact Nbal. }
  destruct (FIN le5 m6 Out_normal) as (mf & XF & HLf & HPf & HVf).
  { rewrite parseNullData_body_shape. eapply pn_seq1; [exact XI|]. eapply pn_seq1; [exact HH|].
    eapply pn_seq1; [eapply pn_seq1; [exact XS|exact XL4]|exact XFn]. }
  { left; reflexivity. }
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S6|]. eapply Mem.perm_store_1; [exact S5|].
    apply PF; [apply VI; eapply Mem.perm_valid_block; exact Hp|apply PI, Hp]. }
  assert (K6 : forall ch b ofs, b <> ba -> b <> bl -> Mem.load ch m6 b ofs = Mem.load ch m4 b ofs).
  { intros ch b ofs N1 N2. rewrite (Mem.load_store_other _ _ _ _ _ _ S6) by (left; exact N2).
    apply (Mem.load_store_other _ _ _ _ _ _ S5). left; exact N1. }
  exists mf. split; [exact XF|]. split; [|split].
  - split; [exact HNa|]. split; [|split; [|split; [|split; [|split]]]].
    + rewrite HLf by exact Vr. rewrite K6 by (apply not_eq_sym; assumption). exact Hop4.
    + rewrite HLf by exact Vr. rewrite K6 by (apply not_eq_sym; assumption). exact Hlen4.
    + intros k Hk. apply (pn_ent_at_ext bop oop m4 mf); [|exact (Hents4 k Hk)].
      intros ch ofs. rewrite HLf by exact Vop. apply K6; apply not_eq_sym; assumption.
    + rewrite HLf by exact Va.
      rewrite (Mem.load_store_other _ _ _ _ _ _ S6) by (left; exact Nbal).
      rewrite (Mem.load_store_same _ _ _ _ _ _ S5). reflexivity.
    + rewrite HLf by exact Vl. rewrite (Mem.load_store_same _ _ _ _ _ _ S6). reflexivity.
    + intros ch b ofs Hb Hd1 Hd2 Hd3 Hd4. rewrite HLf by exact Hb. destruct (NF b Hb) as (? & ? & ?).
      rewrite (Mem.load_store_other _ _ _ _ _ _ S6) by exact Hd4.
      rewrite (Mem.load_store_other _ _ _ _ _ _ S5) by exact Hd3.
      rewrite LF by (try assumption; apply VI, XV, Hb). apply K1; assumption.
  - intros b ofs k p Hb Hp. apply HPf; [exact Hb|].
    eapply Mem.perm_store_1; [exact S6|]. eapply Mem.perm_store_1; [exact S5|]. apply P4, Hp.
  - intros b Hb. apply HVf. eapply Mem.store_valid_block_1; [exact S6|].
    eapply Mem.store_valid_block_1; [exact S5|]. apply VF, VI, XV, Hb.
Qed.
