(** Complete execution of [sha256_uchars(ctx, arr, len)] in the SHA
    translation unit against the byte-absorbing model.  Conditional on the
    explicit [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_compress_uchar C.jet_sha_uchars_prep C.jet_sha_uchars_loop.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 300.

Definition c64 : int64 := Int64.repr (Int.signed (Int.repr 64)).

Definition uc_pre1 : statement :=
  Ssequence (Sset _t'9 (ctx_field_expr SCounter _ctx))
    (Sset _delta (Ebinop Osub (Econst_int (Int.repr 64) tint)
      (Ebinop Omod (Etempvar _t'9 tulong) (Econst_int (Int.repr 64) tint) tulong) tulong)).

Definition uc_pre2 : statement :=
  Ssequence (Sset _t'8 (ctx_field_expr SCounter _ctx))
    (Sset _block (Ebinop Oadd (ctx_field_expr SBlock _ctx)
      (Ebinop Omod (Etempvar _t'8 tulong) (Econst_int (Int.repr 64) tint) tulong) (tptr tuchar))).

Definition uc_ovf_else : statement :=
  Ssequence (Sset _t'6 (Evar _sha256_max_counter tulong))
    (Ssequence (Sset _t'7 (ctx_field_expr SCounter _ctx))
      (Sset _t'1 (Ecast (Ebinop Ole (Ebinop Osub (Etempvar _t'6 tulong) (Etempvar _t'7 tulong) tulong)
        (Etempvar _len tulong) tint) tbool))).

Definition uc_ovf : statement :=
  Ssequence
    (Ssequence (Sset _t'5 (ctx_field_expr SOverflow _ctx))
      (Sifthenelse (Etempvar _t'5 tbool) (Sset _t'1 (Econst_int (Int.repr 1) tint)) uc_ovf_else))
    (Sassign (ctx_field_expr SOverflow _ctx) (Etempvar _t'1 tint)).

Definition uc_count : statement :=
  Ssequence (Sset _t'4 (ctx_field_expr SCounter _ctx))
    (Sassign (ctx_field_expr SCounter _ctx)
      (Ebinop Oadd (Etempvar _t'4 tulong) (Etempvar _len tulong) tulong)).

Definition uc_tail : statement :=
  Ssequence (Sifthenelse (Etempvar _len tulong) (uc_memcpy _len) Sskip)
    (Ssequence (Sset _t'2 (ctx_field_expr SOverflow _ctx))
      (Sreturn (Some (Eunop Onotbool (Etempvar _t'2 tbool) tint)))).

Lemma uchars_body :
  fn_body f_sha256_uchars =
    Ssequence uc_pre1 (Ssequence uc_pre2 (Ssequence uc_ovf (Ssequence uc_count (Ssequence uc_loop uc_tail)))).
Proof. reflexivity. Qed.

Definition sha_max_counter : int64 := Int64.repr 2305843009213693952.

Definition uc_overflow (ovf : bool) (c vn : int64) : bool :=
  ovf || Int64.cmpu Cle (Int64.sub sha_max_counter c) vn.

Lemma modu64 c : Int64.modu c c64 = Int64.repr (Int64.unsigned c mod 64).
Proof. reflexivity. Qed.

Lemma modu64_unsigned c : Int64.unsigned (Int64.modu c c64) = Int64.unsigned c mod 64.
Proof.
  rewrite modu64. apply Int64.unsigned_repr.
  pose proof (Z.mod_pos_bound (Int64.unsigned c) 64 ltac:(lia)).
  change Int64.max_unsigned with 18446744073709551615. lia.
Qed.

Lemma bit_int_zero_ext b : Int.zero_ext 8 (bit_int b) = bit_int b.
Proof. destruct b; reflexivity. Qed.

(** The overflow update, uniformly in the incoming temporaries. *)
Lemma uc_ovf_exec m le bx cbase c vn ovf :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  le!_ctx = Some (Vptr bx (Ptrofs.repr cbase)) -> le!_len = Some (Vlong vn) ->
  Mem.load Mint64 m bx (cbase + 8) = Some (Vlong c) ->
  Mem.load Mint8unsigned m bx (cbase + 80) = Some (Vint (bit_int ovf)) ->
  Mem.load Mint64 m (sha_symbol_block _sha256_max_counter) 0 = Some (Vlong sha_max_counter) ->
  Mem.valid_access m Mint8unsigned bx (cbase + 80) Writable ->
  exists le' m',
    Clight2.exec_stmt sha_ge empty_env le m uc_ovf E0 le' m' Out_normal /\
    Mem.store Mint8unsigned m bx (cbase + 80) (Vint (bit_int (uc_overflow ovf c vn))) = Some m' /\
    le'!_ctx = le!_ctx /\ le'!_arr = le!_arr /\ le'!_len = le!_len /\
    le'!_delta = le!_delta /\ le'!_block = le!_block.
Proof.
  intros Hcb HcM Hctx Hlen HCnt HOvf HMax HW.
  destruct (Mem.valid_access_store m Mint8unsigned bx (cbase + 80)
    (Vint (bit_int (uc_overflow ovf c vn))) HW) as [m' HS].
  set (le5 := PTree.set _t'5 (Vint (bit_int ovf)) le).
  assert (H5 : Clight2.exec_stmt sha_ge empty_env le m (Sset _t'5 (ctx_field_expr SOverflow _ctx)) E0
      le5 m Out_normal).
  { apply exec_Sset. eapply (eval_ctx_field SOverflow) with (chunk := Mint8unsigned);
      [exact Hcb|exact HcM|reflexivity|exact Hctx|exact HOvf]. }
  destruct ovf.
  - set (le1 := PTree.set _t'1 (Vint (Int.repr 1)) le5).
    exists le1, m'. split; [|split; [exact HS|]].
    + unfold uc_ovf. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact H5|].
        eapply exec_Sifthenelse with (b := true); [apply eval_Etempvar; apply PTree.gss|reflexivity|].
        apply exec_Sset. apply eval_Econst_int.
      * eapply (exec_ctx_assign SOverflow) with (chunk := Mint8unsigned) (v := Vint (Int.repr 1));
          [exact Hcb|exact HcM|reflexivity| | |reflexivity|exact HS].
        -- unfold le1, le5. rewrite !PTree.gso by discriminate. exact Hctx.
        -- apply eval_Etempvar. apply PTree.gss.
    + unfold le1, le5. repeat split; rewrite !PTree.gso by discriminate; reflexivity.
  - set (b := Int64.cmpu Cle (Int64.sub sha_max_counter c) vn).
    set (le6 := PTree.set _t'6 (Vlong sha_max_counter) le5).
    set (le7 := PTree.set _t'7 (Vlong c) le6).
    set (le1 := PTree.set _t'1 (Vint (bit_int b)) le7).
    exists le1, m'. split; [|split; [exact HS|]].
    + unfold uc_ovf. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact H5|].
        eapply exec_Sifthenelse with (b := false); [apply eval_Etempvar; apply PTree.gss|reflexivity|].
        unfold uc_ovf_else.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le6) (m1 := m).
        { apply exec_Sset. eapply eval_Elvalue.
          - apply eval_Evar_global; [reflexivity|exact sha_max_counter_symbol].
          - eapply deref_loc_value; [reflexivity|exact HMax]. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le7) (m1 := m).
        { apply exec_Sset. eapply (eval_ctx_field SCounter) with (chunk := Mint64);
            [exact Hcb|exact HcM|reflexivity| |exact HCnt].
          unfold le6, le5. rewrite !PTree.gso by discriminate. exact Hctx. }
        apply exec_Sset. eapply eval_Ecast with (v1 := Val.of_bool b).
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.sub sha_max_counter c)) (v2 := Vlong vn).
           ++ eapply eval_Ebinop; [apply eval_Etempvar; unfold le7; rewrite PTree.gso by discriminate; apply PTree.gss
                |apply eval_Etempvar; apply PTree.gss|reflexivity].
           ++ apply eval_Etempvar. unfold le7, le6, le5. rewrite !PTree.gso by discriminate. exact Hlen.
           ++ reflexivity.
        -- destruct b; reflexivity.
      * eapply (exec_ctx_assign SOverflow) with (chunk := Mint8unsigned) (v := Vint (bit_int b));
          [exact Hcb|exact HcM|reflexivity| | | |exact HS].
        -- unfold le1, le7, le6, le5. rewrite !PTree.gso by discriminate. exact Hctx.
        -- apply eval_Etempvar. apply PTree.gss.
        -- unfold uc_overflow. cbn [orb]. fold b. destruct b; reflexivity.
    + unfold le1, le7, le6, le5. repeat split; rewrite !PTree.gso by discriminate; reflexivity.
Qed.

Definition uc_le0 (bx : block) (cbase : Z) (ba : block) (oa : ptrofs) (vn : int64) : temp_env :=
  PTree.set _len (Vlong vn) (PTree.set _arr (Vptr ba oa) (PTree.set _ctx (Vptr bx (Ptrofs.repr cbase))
    (create_undef_temps (fn_temps f_sha256_uchars)))).

Lemma uc_entry m bx cbase ba oa vn :
  function_entry2 sha_ge f_sha256_uchars [Vptr bx (Ptrofs.repr cbase); Vptr ba oa; Vlong vn] m
    empty_env (uc_le0 bx cbase ba oa vn) m.
Proof.
  constructor.
  - cbn. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - constructor.
  - reflexivity.
Qed.

Theorem eval_sha256_uchars (Hmodel : memcpy_model) m bx cbase bo obase ba oa
    (l regs bs : list int) (c : int64) (ovf : bool) :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned -> 0 <= obase -> obase + 32 <= Ptrofs.max_unsigned ->
  bo <> bx -> ba <> bx -> ba <> bo ->
  sha_symbol_block _simplicity_sha256_compression <> bx ->
  sha_symbol_block _simplicity_sha256_compression <> bo ->
  Ptrofs.unsigned oa + Z.of_nat (length bs) <= Ptrofs.max_unsigned ->
  length regs = 8%nat ->
  Mem.load Mptr m bx cbase = Some (Vptr bo (Ptrofs.repr obase)) ->
  Mem.load Mint64 m bx (cbase + 8) = Some (Vlong c) ->
  Int64.unsigned c mod 64 = Z.of_nat (length l) ->
  Mem.load Mint8unsigned m bx (cbase + 80) = Some (Vint (bit_int ovf)) ->
  (forall i, (i < length l)%nat ->
     Mem.load Mint8unsigned m bx (cbase + 16 + Z.of_nat i) = Some (Vint (nth i l Int.zero))) ->
  (forall i, (i < 8)%nat ->
     Mem.load Mint32 m bo (obase + 4 * Z.of_nat i) = Some (Vint (nth i regs Int.zero)) /\
     Mem.valid_access m Mint32 bo (obase + 4 * Z.of_nat i) Writable) ->
  (forall i, (i < length bs)%nat ->
     Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa + Z.of_nat i) = Some (Vint (nth i bs Int.zero))) ->
  sha_dispatch_ok m ->
  Mem.load Mint64 m (sha_symbol_block _sha256_max_counter) 0 = Some (Vlong sha_max_counter) ->
  Mem.range_perm m bx (cbase + 8) (cbase + 81) Cur Writable -> (8 | cbase) ->
  let vn := Int64.repr (Z.of_nat (length bs)) in
  let ovf' := uc_overflow ovf c vn in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_uchars)
      [Vptr bx (Ptrofs.repr cbase); Vptr ba oa; Vlong vn] E0 m' (Vint (bit_int (negb ovf'))) /\
    Mem.load Mptr m' bx cbase = Some (Vptr bo (Ptrofs.repr obase)) /\
    Mem.load Mint64 m' bx (cbase + 8) = Some (Vlong (Int64.add c vn)) /\
    Mem.load Mint8unsigned m' bx (cbase + 80) = Some (Vint (bit_int ovf')) /\
    (forall i, (i < length (fst (absorb_i l regs bs)))%nat ->
       Mem.load Mint8unsigned m' bx (cbase + 16 + Z.of_nat i) =
         Some (Vint (nth i (fst (absorb_i l regs bs)) Int.zero))) /\
    (forall i, (i < 8)%nat ->
       Mem.load Mint32 m' bo (obase + 4 * Z.of_nat i) =
         Some (Vint (nth i (snd (absorb_i l regs bs)) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b ->
       (b <> bx \/ ofs + size_chunk ch <= cbase + 8 \/ cbase + 81 <= ofs) ->
       (b <> bo \/ ofs + size_chunk ch <= obase \/ obase + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Hcb HcM Hob HoM Hox Hax Hao Hgx Hgo HaM Hr HOut HCnt HMod HOvf HBlk HRegs HBs Hdisp HMax HPerm HAl vn ovf'.
  pose proof (Ptrofs.unsigned_range oa) as HOA.
  assert (Hll : (length l < 64)%nat).
  { pose proof (Z.mod_pos_bound (Int64.unsigned c) 64 ltac:(lia)). lia. }
  assert (Hvn : Int64.unsigned vn = Z.of_nat (length bs)).
  { unfold vn. apply Int64.unsigned_repr. change Int64.max_unsigned with 18446744073709551615.
    change Ptrofs.max_unsigned with 18446744073709551615 in HaM. lia. }
  set (le0 := uc_le0 bx cbase ba oa vn).
  (* pre1 *)
  set (vd := Int64.sub c64 (Int64.modu c c64)).
  assert (Hvd : Int64.unsigned vd = 64 - Z.of_nat (length l)).
  { unfold vd. rewrite long_sub_unsigned; rewrite modu64_unsigned, HMod; change (Int64.unsigned c64) with 64; lia. }
  set (le1 := PTree.set _delta (Vlong vd) (PTree.set _t'9 (Vlong c) le0)).
  (* pre2 *)
  set (oblk := Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16)).
  assert (Hoblk : Ptrofs.unsigned oblk = cbase + 16) by (apply (ctx_address cbase SBlock); assumption).
  set (ob := Ptrofs.add oblk (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.modu c c64)))).
  assert (Hob' : Ptrofs.unsigned ob = cbase + 16 + Z.of_nat (length l)).
  { unfold ob. rewrite ptr_add_long; rewrite modu64_unsigned, HMod, Hoblk; lia. }
  set (le2 := PTree.set _block (Vptr bx ob) (PTree.set _t'8 (Vlong c) le1)).
  assert (Hctx2 : le2!_ctx = Some (Vptr bx (Ptrofs.repr cbase))) by reflexivity.
  assert (Hlen2 : le2!_len = Some (Vlong vn)) by reflexivity.
  (* overflow *)
  assert (HW80 : Mem.valid_access m Mint8unsigned bx (cbase + 80) Writable).
  { split; [|exists (cbase + 80); cbn; lia]. intros ofs Ho. apply HPerm.
    change (size_chunk Mint8unsigned) with 1 in Ho. lia. }
  destruct (uc_ovf_exec m le2 bx cbase c vn ovf Hcb HcM Hctx2 Hlen2 HCnt HOvf HMax HW80)
    as (le3 & m3 & HE3 & HS3 & Hctx3 & Harr3 & Hlen3 & Hdelta3 & Hblock3).
  fold ovf' in HS3.
  (* counter *)
  set (le4 := PTree.set _t'4 (Vlong c) le3).
  assert (HW8 : Mem.valid_access m3 Mint64 bx (cbase + 8) Writable).
  { split.
    - intros ofs Ho. eapply Mem.perm_store_1; [exact HS3|]. apply HPerm.
      change (size_chunk Mint64) with 8 in Ho. lia.
    - change (align_chunk Mint64) with 8. apply Z.divide_add_r; [exact HAl|exists 1; reflexivity]. }
  destruct (Mem.valid_access_store m3 Mint64 bx (cbase + 8) (Vlong (Int64.add c vn)) HW8) as [m4 HS4].
  assert (L34 : forall ch b ofs, (b <> bx \/ ofs + size_chunk ch <= cbase + 8 \/ cbase + 81 <= ofs) ->
    Mem.load ch m4 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hc.
    rewrite (Mem.load_store_other _ _ _ _ _ _ HS4)
      by (change (size_chunk Mint64) with 8; destruct Hc as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]).
    apply (Mem.load_store_other _ _ _ _ _ _ HS3).
    change (size_chunk Mint8unsigned) with 1. destruct Hc as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]. }
  assert (L34b : forall ch ofs, cbase + 16 <= ofs -> ofs + size_chunk ch <= cbase + 80 ->
    Mem.load ch m4 bx ofs = Mem.load ch m bx ofs).
  { intros ch ofs H1 H2.
    rewrite (Mem.load_store_other _ _ _ _ _ _ HS4) by (change (size_chunk Mint64) with 8; right; right; lia).
    apply (Mem.load_store_other _ _ _ _ _ _ HS3). right; left. lia. }
  assert (P34 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m4 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact HS4|]. eapply Mem.perm_store_1; [exact HS3|exact Hp]. }
  assert (V34 : forall b, Mem.valid_block m b -> Mem.valid_block m4 b).
  { intros b Hv. eapply Mem.store_valid_block_1; [exact HS4|]. eapply Mem.store_valid_block_1; [exact HS3|exact Hv]. }
  assert (HOvf4 : Mem.load Mint8unsigned m4 bx (cbase + 80) = Some (Vint (bit_int ovf'))).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ HS4) by (change (size_chunk Mint64) with 8; right; right; lia).
    rewrite (Mem.load_store_same _ _ _ _ _ _ HS3). cbn. rewrite bit_int_zero_ext. reflexivity. }
  assert (HCnt4 : Mem.load Mint64 m4 bx (cbase + 8) = Some (Vlong (Int64.add c vn))).
  { rewrite (Mem.load_store_same _ _ _ _ _ _ HS4). reflexivity. }
  assert (HCnt3 : Mem.load Mint64 m3 bx (cbase + 8) = Some (Vlong c)).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ HS3) by (change (size_chunk Mint64) with 8; right; left; lia).
    exact HCnt. }
  (* loop *)
  assert (Hust : ust bx bo ba cbase obase m4 le4 l regs bs (Ptrofs.unsigned oa)).
  { unfold ust. split; [exact Hll|]. split; [exact Hr|]. split; [lia|]. split; [exact HaM|].
    split; [unfold le4; rewrite PTree.gso by discriminate; rewrite Hctx3; reflexivity|].
    split; [exists oa; split; [unfold le4; rewrite PTree.gso by discriminate; rewrite Harr3; reflexivity|reflexivity]|].
    split; [exists vn; split; [unfold le4; rewrite PTree.gso by discriminate; rewrite Hlen3; reflexivity|exact Hvn]|].
    split; [exists vd; split; [unfold le4; rewrite PTree.gso by discriminate; rewrite Hdelta3; reflexivity|exact Hvd]|].
    split; [exists ob; split; [unfold le4; rewrite PTree.gso by discriminate; rewrite Hblock3; reflexivity|exact Hob']|].
    split; [rewrite L34 by (right; left; change (size_chunk Mptr) with 8; lia); exact HOut|].
    split; [intros i Hi; rewrite L34b by (change (size_chunk Mint8unsigned) with 1; lia); apply HBlk; exact Hi|].
    split.
    { intros i Hi. destruct (HRegs i Hi) as [HLd [Pr Al]]. split.
      - rewrite L34 by (left; exact Hox). exact HLd.
      - split; [|exact Al]. intros ofs Ho. apply P34, Pr, Ho. }
    split; [intros i Hi; rewrite L34 by (left; exact Hax); apply HBs; exact Hi|].
    split; [unfold sha_dispatch_ok; rewrite L34 by (left; exact Hgx); exact Hdisp|].
    intros ofs Ho. apply P34, HPerm. lia. }
  destruct (uc_loop_exec Hmodel bx bo ba cbase obase Hcb HcM Hob HoM Hox Hax Hao Hgx Hgo
    (length bs) bs eq_refl m4 le4 l regs (Ptrofs.unsigned oa) Hust)
    as (le5 & m5 & l1 & regs1 & rem1 & aoff1 & HE5 & HU5 & HLen5 & HAbs & (FL5 & FP5 & FV5)).
  destruct HU5 as (Hl1 & Hr1 & Ha1 & HaM1 & Hctx5 & (oa5 & Harr5 & Hoa5) & (vl5 & Hlen5 & Hvl5) &
    (vd5 & Hdelta5 & Hvd5) & (ob5 & Hblock5 & Hob5) & HOut5 & HBlk5 & HRegs5 & HRem5 & Hdisp5 & HPerm5).
  rewrite HAbs, (absorb_i_small rem1 l1 regs1 HLen5). cbn [fst snd].
  (* tail copy *)
  assert (HT : exists m6,
    Clight2.exec_stmt sha_ge empty_env le5 m5 (Sifthenelse (Etempvar _len tulong) (uc_memcpy _len) Sskip)
      E0 le5 m6 Out_normal /\
    (forall i, (i < length rem1)%nat ->
       Mem.load Mint8unsigned m6 bx (cbase + 16 + Z.of_nat (length l1) + Z.of_nat i) =
         Some (Vint (nth i rem1 Int.zero))) /\
    (forall ch b ofs,
       (b <> bx \/ ofs + size_chunk ch <= cbase + 16 + Z.of_nat (length l1) \/ cbase + 80 <= ofs) ->
       Mem.load ch m6 b ofs = Mem.load ch m5 b ofs) /\
    (forall b ofs k p, Mem.perm m5 b ofs k p -> Mem.perm m6 b ofs k p) /\
    (forall b, Mem.valid_block m5 b -> Mem.valid_block m6 b)).
  { destruct rem1 as [|x rem1'] eqn:Erem.
    - exists m5. split; [|split; [intros i Hi; cbn in Hi; lia|split; [reflexivity|split; auto]]].
      eapply exec_Sifthenelse with (b := false); [apply eval_Etempvar; exact Hlen5| |apply exec_Sskip].
      cbn [length] in Hvl5. cbn. unfold bool_val. cbn.
      assert (HZ : vl5 = Int64.zero) by (rewrite <- (Int64.repr_unsigned vl5), Hvl5; reflexivity).
      rewrite HZ. reflexivity.
    - rewrite <- Erem in *.
      destruct (uc_memcpy_exec Hmodel bx bo ba Hox Hax Hao Hgx Hgo _len le5 m5 ob5 oa5 vl5 rem1 Hblock5 Harr5 Hlen5 Hvl5
        ltac:(rewrite Erem; cbn [length]; lia) ltac:(rewrite Hoa5; exact HaM1)
        ltac:(rewrite Hob5; lia))
        as (m6 & HE6 & HD6 & HF6 & HP6 & HV6).
      { intros i Hi. rewrite Hoa5. apply HRem5. exact Hi. }
      { intros ofs Ho. apply HPerm5. lia. }
      exists m6. split; [|split; [|split; [|split; [exact HP6|exact HV6]]]].
      + eapply exec_Sifthenelse with (b := true); [apply eval_Etempvar; exact Hlen5| |exact HE6].
        cbn. unfold bool_val. cbn.
        assert (HNZ : Int64.eq vl5 Int64.zero = false).
        { apply Int64.eq_false. intro HZ. rewrite HZ in Hvl5. rewrite Erem in Hvl5.
          cbn [length] in Hvl5. change (Int64.unsigned Int64.zero) with 0 in Hvl5. lia. }
        rewrite HNZ. reflexivity.
      + intros i Hi. rewrite <- Hob5. apply HD6. exact Hi.
      + intros ch b ofs Hc. apply HF6. rewrite Hob5.
        destruct Hc as [H|[H|H]]; [left; exact H|right; left; exact H|right; right; lia]. }
  destruct HT as (m6 & HE6 & HD6 & HF6 & HP6 & HV6).
  assert (Hvx : Mem.valid_block m bx).
  { apply Mem.load_valid_access in HOut. eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies; [exact HOut|constructor]. }
  assert (HOvf6 : Mem.load Mint8unsigned m6 bx (cbase + 80) = Some (Vint (bit_int ovf'))).
  { rewrite HF6 by (right; right; lia).
    rewrite FL5; [exact HOvf4|apply V34; exact Hvx|right; right; lia|left; auto]. }
  set (le7 := PTree.set _t'2 (Vint (bit_int ovf')) le5).
  exists m6. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - eapply eval_funcall_internal with (e := empty_env) (le1 := le0) (m1 := m) (le2 := le7) (m2 := m6)
      (out := Out_return (Some (Vint (bit_int (negb ovf')), tint))).
    + apply uc_entry.
    + rewrite uchars_body.
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
            [exact Hcb|exact HcM|reflexivity| | |reflexivity|exact HS4].
          + unfold le4. rewrite PTree.gso by discriminate. rewrite Hctx3. reflexivity.
          + eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss
              |apply eval_Etempvar; unfold le4; rewrite PTree.gso by discriminate; rewrite Hlen3; reflexivity
              |reflexivity]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := m5); [exact HE5|].
      unfold uc_tail.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := m6); [exact HE6|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le7) (m1 := m6).
      { apply exec_Sset. eapply (eval_ctx_field SOverflow) with (chunk := Mint8unsigned);
          [exact Hcb|exact HcM|reflexivity|exact Hctx5|exact HOvf6]. }
      apply exec_Sreturn_some.
      eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|].
      destruct ovf'; reflexivity.
    + cbn. split; [discriminate|]. destruct ovf'; reflexivity.
    + reflexivity.
  - rewrite HF6 by (right; left; change (size_chunk Mptr) with 8; lia). exact HOut5.
  - rewrite HF6 by (right; left; change (size_chunk Mint64) with 8; lia).
    rewrite FL5; [exact HCnt4|apply V34; exact Hvx|right; left; change (size_chunk Mint64) with 8; lia|left; auto].
  - exact HOvf6.
  - intros i Hi. rewrite app_length in Hi. destruct (lt_dec i (length l1)) as [Hs|Hs].
    + rewrite app_nth1 by exact Hs. rewrite HF6 by (right; left; change (size_chunk Mint8unsigned) with 1; lia).
      apply HBlk5. exact Hs.
    + rewrite app_nth2 by lia.
      replace (cbase + 16 + Z.of_nat i) with (cbase + 16 + Z.of_nat (length l1) + Z.of_nat (i - length l1)) by lia.
      apply HD6. lia.
  - intros i Hi. rewrite HF6 by (left; exact Hox). apply (HRegs5 i Hi).
  - intros ch b ofs Hv Hx Ho.
    rewrite HF6 by (destruct Hx as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]).
    rewrite FL5; [apply L34; exact Hx|apply V34; exact Hv| |exact Ho].
    destruct Hx as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia].
  - intros b ofs k p Hv Hp. apply HP6, FP5; [apply V34; exact Hv|apply P34; exact Hp].
  - intros b Hv. apply HV6, FV5, V34, Hv.
Qed.
