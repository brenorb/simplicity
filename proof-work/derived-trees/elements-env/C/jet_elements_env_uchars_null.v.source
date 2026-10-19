(** [sha256_uchars(ctx, NULL, 0)] (sha256.h): what [hashBuffer] does for the
    zero [rawElementsBuffer] the Elements environment hashes in place of an
    absent proof.  The accepted [eval_sha256_uchars] is stated for a
    non-null array; this is the remaining case. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_u32be_exec.
Require Import C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec C.jet_sha_uchar_exec.
Require Import C.jet_sha_ctx_abs C.jet_elements_env_ctxo.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 300.

Ltac ctxo_side_n :=
  first [eassumption | reflexivity
        | (change Int64.max_unsigned with 18446744073709551615; lia)
        | (change Ptrofs.max_unsigned with 18446744073709551615; lia)
        | lia | (exists 0; reflexivity)].

Local Transparent Archi.ptr64.

(** The call with a NULL array and length zero: the counter and the buffer
    are unchanged, only the overflow flag is recomputed. *)
Theorem eval_sha256_uchars_null m bx cbase (c : int64) (ovf : bool) :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m bx (cbase + 8) = Some (Vlong c) ->
  Mem.load Mint8unsigned m bx (cbase + 80) = Some (Vint (bit_int ovf)) ->
  Mem.load Mint64 m (sha_symbol_block _sha256_max_counter) 0 = Some (Vlong sha_max_counter) ->
  Mem.range_perm m bx (cbase + 8) (cbase + 81) Cur Writable -> (8 | cbase) ->
  let ovf' := uc_overflow ovf c Int64.zero in
  exists m3 m4,
    Mem.store Mint8unsigned m bx (cbase + 80) (Vint (bit_int ovf')) = Some m3 /\
    Mem.store Mint64 m3 bx (cbase + 8) (Vlong (Int64.add c Int64.zero)) = Some m4 /\
    Clight2.eval_funcall sha_ge m (Internal f_sha256_uchars)
      [Vptr bx (Ptrofs.repr cbase); Vlong Int64.zero; Vlong Int64.zero] E0 m4 (Vint (bit_int (negb ovf'))).
Proof.
  intros Hcb HcM HCnt HOvf HMax HPerm HAl ovf'.
  set (vn := Int64.zero).
  set (le0 := PTree.set _len (Vlong vn) (PTree.set _arr (Vlong Int64.zero)
    (PTree.set _ctx (Vptr bx (Ptrofs.repr cbase)) (create_undef_temps (fn_temps f_sha256_uchars))))).
  set (vd := Int64.sub c64 (Int64.modu c c64)).
  assert (Hvd : Int64.unsigned vd = 64 - Int64.unsigned c mod 64).
  { unfold vd. pose proof (Z.mod_pos_bound (Int64.unsigned c) 64 ltac:(lia)).
    rewrite long_sub_unsigned; rewrite modu64_unsigned; change (Int64.unsigned c64) with 64; lia. }
  set (le1 := PTree.set _delta (Vlong vd) (PTree.set _t'9 (Vlong c) le0)).
  set (oblk := Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16)).
  set (ob := Ptrofs.add oblk (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.modu c c64)))).
  set (le2 := PTree.set _block (Vptr bx ob) (PTree.set _t'8 (Vlong c) le1)).
  assert (Hctx2 : le2!_ctx = Some (Vptr bx (Ptrofs.repr cbase))) by reflexivity.
  assert (Hlen2 : le2!_len = Some (Vlong vn)) by reflexivity.
  assert (HW80 : Mem.valid_access m Mint8unsigned bx (cbase + 80) Writable).
  { split; [|exists (cbase + 80); cbn; lia]. intros ofs Ho. apply HPerm.
    change (size_chunk Mint8unsigned) with 1 in Ho. lia. }
  destruct (uc_ovf_exec m le2 bx cbase c vn ovf Hcb HcM Hctx2 Hlen2 HCnt HOvf HMax HW80)
    as (le3 & m3 & HE3 & HS3 & Hctx3 & Harr3 & Hlen3 & Hdelta3 & Hblock3).
  fold ovf' in HS3.
  set (le4 := PTree.set _t'4 (Vlong c) le3).
  assert (HW8 : Mem.valid_access m3 Mint64 bx (cbase + 8) Writable).
  { split.
    - intros ofs Ho. eapply Mem.perm_store_1; [exact HS3|]. apply HPerm.
      change (size_chunk Mint64) with 8 in Ho. lia.
    - change (align_chunk Mint64) with 8. apply Z.divide_add_r; [exact HAl|exists 1; reflexivity]. }
  destruct (Mem.valid_access_store m3 Mint64 bx (cbase + 8) (Vlong (Int64.add c vn)) HW8) as [m4 HS4].
  assert (HCnt3 : Mem.load Mint64 m3 bx (cbase + 8) = Some (Vlong c)).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ HS3) by (change (size_chunk Mint64) with 8; right; left; lia).
    exact HCnt. }
  assert (HOvf4 : Mem.load Mint8unsigned m4 bx (cbase + 80) = Some (Vint (bit_int ovf'))).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ HS4) by (change (size_chunk Mint64) with 8; right; right; lia).
    rewrite (Mem.load_store_same _ _ _ _ _ _ HS3). cbn. rewrite bit_int_zero_ext. reflexivity. }
  assert (Hctx4 : le4!_ctx = Some (Vptr bx (Ptrofs.repr cbase)))
    by (unfold le4; rewrite PTree.gso by discriminate; rewrite Hctx3; reflexivity).
  assert (Hlen4 : le4!_len = Some (Vlong vn))
    by (unfold le4; rewrite PTree.gso by discriminate; rewrite Hlen3; reflexivity).
  assert (Hdelta4 : le4!_delta = Some (Vlong vd))
    by (unfold le4; rewrite PTree.gso by discriminate; rewrite Hdelta3; reflexivity).
  assert (HCmp : Int64.cmpu Cle vd vn = false).
  { rewrite cmpu_le_bool. pose proof (Z.mod_pos_bound (Int64.unsigned c) 64 ltac:(lia)).
    apply Z.leb_gt. rewrite Hvd. change (Int64.unsigned vn) with 0. lia. }
  set (le7 := PTree.set _t'2 (Vint (bit_int ovf')) le4).
  exists m3, m4. split; [exact HS3|]. split; [exact HS4|].
  eapply eval_funcall_internal with (e := empty_env) (le1 := le0) (m1 := m) (le2 := le7) (m2 := m4)
    (out := Out_return (Some (Vint (bit_int (negb ovf')), tint))).
  - constructor.
    + cbn. constructor.
    + cbn. repeat constructor; cbn; intuition discriminate.
    + intros x y HX HY Hxy. cbn in HX, HY.
      repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
        first [contradiction | vm_compute in Hxy; discriminate | congruence].
    + constructor.
    + reflexivity.
  - rewrite uchars_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
    { unfold uc_pre1. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      - apply exec_Sset. eapply (eval_ctx_field SCounter) with (chunk := Mint64);
          [exact Hcb|exact HcM|reflexivity|reflexivity|exact HCnt].
      - apply exec_Sset. eapply eval_Ebinop with (v1 := Vint (Int.repr 64)) (v2 := Vlong (Int64.modu c c64)).
        + apply eval_Econst_int.
        + eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|apply eval_Econst_int|reflexivity].
        + reflexivity. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m).
    { unfold uc_pre2. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      - apply exec_Sset. eapply (eval_ctx_field SCounter) with (chunk := Mint64);
          [exact Hcb|exact HcM|reflexivity|reflexivity|exact HCnt].
      - apply exec_Sset. eapply eval_Ebinop with (v1 := Vptr bx oblk) (v2 := Vlong (Int64.modu c c64)).
        + apply eval_ctx_block. reflexivity.
        + eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|apply eval_Econst_int|reflexivity].
        + reflexivity. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m3); [exact HE3|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m4).
    { unfold uc_count. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m3).
      - apply exec_Sset. eapply (eval_ctx_field SCounter) with (chunk := Mint64);
          [exact Hcb|exact HcM|reflexivity|rewrite Hctx3; reflexivity|exact HCnt3].
      - eapply (exec_ctx_assign SCounter) with (chunk := Mint64) (v := Vlong (Int64.add c vn));
          [exact Hcb|exact HcM|reflexivity|exact Hctx4| |reflexivity|exact HS4].
        eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|apply eval_Etempvar; exact Hlen4|reflexivity]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m4).
    { unfold uc_loop, Swhile.
      eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
      eapply exec_Sseq_2; [|discriminate].
      eapply exec_Sifthenelse with (v1 := Val.of_bool (Int64.cmpu Cle vd vn)) (b := false).
      - unfold uc_cond.
        eapply eval_Ebinop; [apply eval_Etempvar; exact Hdelta4|apply eval_Etempvar; exact Hlen4|reflexivity].
      - rewrite HCmp. reflexivity.
      - apply exec_Sbreak. }
    unfold uc_tail.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m4).
    { eapply exec_Sifthenelse with (v1 := Vlong vn) (b := false);
        [apply eval_Etempvar; exact Hlen4|reflexivity|apply exec_Sskip]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le7) (m1 := m4).
    { apply exec_Sset. eapply (eval_ctx_field SOverflow) with (chunk := Mint8unsigned);
        [exact Hcb|exact HcM|reflexivity|exact Hctx4|exact HOvf4]. }
    apply exec_Sreturn_some.
    eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|].
    destruct ovf'; reflexivity.
  - cbn. split; [discriminate|]. destruct ovf'; reflexivity.
  - reflexivity.
Qed.

Section Null.
Variables (bx bo : block) (obase : Z).
Hypothesis Hox : bo <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgo : GC <> bo.
Hypothesis Hcx : GM <> bx.
Hypothesis Hco : GM <> bo.
Hypothesis Hob : 0 <= obase /\ obase + 32 <= Ptrofs.max_unsigned.

Theorem ctxo_uchars_null m l regs c ovf :
  ctxo m bx bo obase l regs c ovf ->
  let ovf' := uc_overflow ovf c Int64.zero in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_uchars)
      [Vptr bx (Ptrofs.repr 0); Vlong Int64.zero; Vlong Int64.zero] E0 m' (Vint (bit_int (negb ovf'))) /\
    ctxo m' bx bo obase l regs (Int64.add c Int64.zero) ovf' /\
    (forall ch b ofs, b <> bx -> Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HA ovf'.
  pose proof HA as (HOut & HCnt & HOvf & HBlk & HRegs & HMod & HLen & Hr & PX & Hdisp & HMax).
  assert (PW : Mem.range_perm m bx (0 + 8) (0 + 81) Cur Writable).
  { intros ofs Hr0. eapply Mem.perm_implies; [apply PX; lia|constructor]. }
  destruct (eval_sha256_uchars_null m bx 0 c ovf ltac:(lia)
    ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) HCnt HOvf HMax PW ltac:(exists 0; reflexivity))
    as (m3 & m4 & HS3 & HS4 & HCall).
  fold ovf' in HS3, HCall.
  assert (L4 : forall ch b ofs, (b <> bx \/ ofs + size_chunk ch <= 0 + 8 \/ 0 + 81 <= ofs) ->
    Mem.load ch m4 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hc.
    rewrite (Mem.load_store_other _ _ _ _ _ _ HS4)
      by (change (size_chunk Mint64) with 8; destruct Hc as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]).
    apply (Mem.load_store_other _ _ _ _ _ _ HS3).
    change (size_chunk Mint8unsigned) with 1. destruct Hc as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]. }
  assert (L4b : forall ch ofs, 0 + 16 <= ofs -> ofs + size_chunk ch <= 0 + 80 ->
    Mem.load ch m4 bx ofs = Mem.load ch m bx ofs).
  { intros ch ofs H1 H2.
    rewrite (Mem.load_store_other _ _ _ _ _ _ HS4) by (change (size_chunk Mint64) with 8; right; right; lia).
    apply (Mem.load_store_other _ _ _ _ _ _ HS3). right; left. lia. }
  assert (P4 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m4 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact HS4|]. eapply Mem.perm_store_1; [exact HS3|exact Hp]. }
  assert (V4 : forall b, Mem.valid_block m b -> Mem.valid_block m4 b).
  { intros b Hv. eapply Mem.store_valid_block_1; [exact HS4|]. eapply Mem.store_valid_block_1; [exact HS3|exact Hv]. }
  exists m4. split; [exact HCall|]. split; [|split; [|split; [exact P4|exact V4]]].
  - change l with (fst (absorb_i l regs [])). change regs with (snd (absorb_i l regs [])) at 2.
    eapply ctxo_step with (m := m) (n := 0); try eassumption; try reflexivity.
    + change Int64.max_unsigned with 18446744073709551615. lia.
    + rewrite L4 by (right; left; change (size_chunk Mptr) with 8; lia). exact HOut.
    + rewrite (Mem.load_store_same _ _ _ _ _ _ HS4). reflexivity.
    + rewrite (Mem.load_store_other _ _ _ _ _ _ HS4) by (change (size_chunk Mint64) with 8; right; right; lia).
      rewrite (Mem.load_store_same _ _ _ _ _ _ HS3). cbn. rewrite bit_int_zero_ext. reflexivity.
    + intros i Hi. rewrite L4b by (change (size_chunk Mint8unsigned) with 1; cbn in Hi; lia). apply HBlk. exact Hi.
    + intros i Hi. rewrite L4 by (left; exact Hox). exact (proj1 (HRegs i Hi)).
    + intros ch b ofs Hv H1 H2. apply L4. exact H1.
    + intros b ofs k p Hv Hp. apply P4, Hp.
  - intros ch b ofs Hb. apply L4. left. exact Hb.
Qed.
End Null.
