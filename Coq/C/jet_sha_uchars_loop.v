(** The block loop of [sha256_uchars]: while a whole 64-byte block is
    available, complete the context block with [memcpy] and compress it.
    Conditional on the explicit [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat Wf_nat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256 sha.common_lemmas.
Require Import C.jet_exec C.jet_memcpy_model.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_compress_uchar C.jet_sha_uchars_prep.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 300.

Definition memcpy_ty : type :=
  Tfunction (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid) cc_default.

Definition uc_memcpy (n : ident) : statement :=
  Scall None (Evar _memcpy memcpy_ty)
    [Etempvar _block (tptr tuchar); Etempvar _arr (tptr tuchar); Etempvar n tulong].

Definition uc_loop_body : statement :=
  Ssequence (uc_memcpy _delta)
    (Ssequence (Sset _arr (Ebinop Oadd (Etempvar _arr (tptr tuchar)) (Etempvar _delta tulong) (tptr tuchar)))
      (Ssequence (Sset _len (Ebinop Osub (Etempvar _len tulong) (Etempvar _delta tulong) tulong))
        (Ssequence
          (Ssequence (Sset _t'3 (ctx_field_expr SOutput _ctx))
            (Scall None (Evar _sha256_compression_uchar
                (Tfunction (Tcons (tptr tuint) (Tcons (tptr tuchar) Tnil)) tvoid cc_default))
              [Etempvar _t'3 (tptr tuint); ctx_field_expr SBlock _ctx]))
          (Ssequence (Sset _block (ctx_field_expr SBlock _ctx))
            (Sset _delta (Ecast (Econst_int (Int.repr 64) tint) tulong)))))).

Definition uc_cond : expr := Ebinop Ole (Etempvar _delta tulong) (Etempvar _len tulong) tint.
Definition uc_loop : statement := Swhile uc_cond uc_loop_body.

Lemma ptr_add_long (o : ptrofs) (v : int64) :
  Ptrofs.unsigned o + Int64.unsigned v <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned (Ptrofs.add o (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 v))) =
    Ptrofs.unsigned o + Int64.unsigned v.
Proof.
  intros H. pose proof (Ptrofs.unsigned_range o) as HO. pose proof (Int64.unsigned_range v) as HV.
  rewrite Ptrofs.mul_commut, Ptrofs.mul_one. unfold Ptrofs.of_int64, Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr (Int64.unsigned v)) by lia.
  apply Ptrofs.unsigned_repr. lia.
Qed.

Lemma long_sub_unsigned (a b : int64) :
  Int64.unsigned b <= Int64.unsigned a ->
  Int64.unsigned (Int64.sub a b) = Int64.unsigned a - Int64.unsigned b.
Proof.
  intros H. pose proof (Int64.unsigned_range_2 a). pose proof (Int64.unsigned_range b).
  unfold Int64.sub. apply Int64.unsigned_repr. lia.
Qed.

Lemma cmpu_le_bool (a b : int64) :
  Int64.cmpu Cle a b = Z.leb (Int64.unsigned a) (Int64.unsigned b).
Proof.
  unfold Int64.cmpu, Int64.ltu. destruct (zlt (Int64.unsigned b) (Int64.unsigned a)); cbn [negb].
  - symmetry. apply Z.leb_gt. lia.
  - symmetry. apply Z.leb_le. lia.
Qed.

Section Loop.
Variable Hmodel : memcpy_model.
Variables (bx bo ba : block) (cbase obase : Z).
Hypothesis Hcb : 0 <= cbase.
Hypothesis HcM : cbase + 88 <= Ptrofs.max_unsigned.
Hypothesis Hob : 0 <= obase.
Hypothesis HoM : obase + 32 <= Ptrofs.max_unsigned.
Hypothesis Hox : bo <> bx.
Hypothesis Hax : ba <> bx.
Hypothesis Hao : ba <> bo.
Hypothesis Hgx : sha_symbol_block _simplicity_sha256_compression <> bx.
Hypothesis Hgo : sha_symbol_block _simplicity_sha256_compression <> bo.

Definition ust (m : mem) (le : temp_env) (l regs rem : list int) (aoff : Z) : Prop :=
  (length l < 64)%nat /\ length regs = 8%nat /\
  0 <= aoff /\ aoff + Z.of_nat (length rem) <= Ptrofs.max_unsigned /\
  le!_ctx = Some (Vptr bx (Ptrofs.repr cbase)) /\
  (exists oa, le!_arr = Some (Vptr ba oa) /\ Ptrofs.unsigned oa = aoff) /\
  (exists vl, le!_len = Some (Vlong vl) /\ Int64.unsigned vl = Z.of_nat (length rem)) /\
  (exists vd, le!_delta = Some (Vlong vd) /\ Int64.unsigned vd = 64 - Z.of_nat (length l)) /\
  (exists ob, le!_block = Some (Vptr bx ob) /\ Ptrofs.unsigned ob = cbase + 16 + Z.of_nat (length l)) /\
  Mem.load Mptr m bx cbase = Some (Vptr bo (Ptrofs.repr obase)) /\
  (forall i, (i < length l)%nat ->
     Mem.load Mint8unsigned m bx (cbase + 16 + Z.of_nat i) = Some (Vint (nth i l Int.zero))) /\
  (forall i, (i < 8)%nat ->
     Mem.load Mint32 m bo (obase + 4 * Z.of_nat i) = Some (Vint (nth i regs Int.zero)) /\
     Mem.valid_access m Mint32 bo (obase + 4 * Z.of_nat i) Writable) /\
  (forall i, (i < length rem)%nat ->
     Mem.load Mint8unsigned m ba (aoff + Z.of_nat i) = Some (Vint (nth i rem Int.zero))) /\
  sha_dispatch_ok m /\
  Mem.range_perm m bx (cbase + 16) (cbase + 80) Cur Writable.

Definition uframe (m m' : mem) : Prop :=
  (forall ch b ofs, Mem.valid_block m b ->
     (b <> bx \/ ofs + size_chunk ch <= cbase + 16 \/ cbase + 80 <= ofs) ->
     (b <> bo \/ ofs + size_chunk ch <= obase \/ obase + 32 <= ofs) ->
     Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
  (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
  (forall b, Mem.valid_block m b -> Mem.valid_block m' b).

Lemma uframe_refl m : uframe m m.
Proof. repeat split; auto. Qed.

Lemma uframe_trans m1 m2 m3 : uframe m1 m2 -> uframe m2 m3 -> uframe m1 m3.
Proof.
  intros (L1 & P1 & V1) (L2 & P2 & V2). split; [|split].
  - intros ch b ofs Hv Hx Ho. rewrite L2 by (auto). apply L1; auto.
  - intros b ofs k p Hv Hp. apply P2; [apply V1; exact Hv|]. apply P1; assumption.
  - intros b Hv. apply V2, V1, Hv.
Qed.

Lemma uc_cond_eval le m vd vl :
  le!_delta = Some (Vlong vd) -> le!_len = Some (Vlong vl) ->
  eval_expr sha_ge empty_env le m uc_cond (Val.of_bool (Z.leb (Int64.unsigned vd) (Int64.unsigned vl))).
Proof.
  intros HD HL. unfold uc_cond. rewrite <- cmpu_le_bool.
  eapply eval_Ebinop; [apply eval_Etempvar; exact HD|apply eval_Etempvar; exact HL|reflexivity].
Qed.

Lemma uc_memcpy_exec (n : ident) le m ob oa vn (xs : list int) :
  le!_block = Some (Vptr bx ob) -> le!_arr = Some (Vptr ba oa) -> le!n = Some (Vlong vn) ->
  Int64.unsigned vn = Z.of_nat (length xs) -> (0 < length xs)%nat ->
  Ptrofs.unsigned oa + Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned ob + Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  (forall i, (i < length xs)%nat ->
     Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa + Z.of_nat i) = Some (Vint (nth i xs Int.zero))) ->
  Mem.range_perm m bx (Ptrofs.unsigned ob) (Ptrofs.unsigned ob + Z.of_nat (length xs)) Cur Writable ->
  exists m',
    Clight2.exec_stmt sha_ge empty_env le m (uc_memcpy n) E0 le m' Out_normal /\
    (forall i, (i < length xs)%nat ->
       Mem.load Mint8unsigned m' bx (Ptrofs.unsigned ob + Z.of_nat i) = Some (Vint (nth i xs Int.zero))) /\
    (forall ch b ofs,
       (b <> bx \/ ofs + size_chunk ch <= Ptrofs.unsigned ob \/
        Ptrofs.unsigned ob + Z.of_nat (length xs) <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HB HA HN HV Hpos HMa HMb HL HP.
  destruct (memcpy_bytes_effect Hmodel (Clight.genv_genv sha_ge) m ba oa bx ob xs ltac:(lia) HMa HMb HL HP Hax)
    as (m' & HX & HD & HF & HPm & HVb).
  exists m'. split; [|split; [exact HD|split; [exact HF|split; [exact HPm|exact HVb]]]].
  assert (HVn : vn = Int64.repr (Z.of_nat (length xs))) by (rewrite <- HV; symmetry; apply Int64.repr_unsigned).
  change le with (set_opttemp None (Vptr bx ob) le) at 2. unfold uc_memcpy.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _memcpy) Ptrofs.zero)
    (vargs := [Vptr bx ob; Vptr ba oa; Vlong vn]).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_memcpy_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply eval_Etempvar; exact HB|reflexivity|].
    eapply eval_Econs; [apply eval_Etempvar; exact HA|reflexivity|].
    eapply eval_Econs; [apply eval_Etempvar; exact HN|reflexivity|apply eval_Enil].
  - exact sha_memcpy_funct.
  - reflexivity.
  - rewrite HVn. apply eval_funcall_external. exact HX.
Qed.

Lemma uc_loop_exec : forall n rem, length rem = n -> forall m le l regs aoff,
  ust m le l regs rem aoff ->
  exists le' m' l1 regs1 rem1 aoff1,
    Clight2.exec_stmt sha_ge empty_env le m uc_loop E0 le' m' Out_normal /\
    ust m' le' l1 regs1 rem1 aoff1 /\ (length l1 + length rem1 < 64)%nat /\
    absorb_i l regs rem = absorb_i l1 regs1 rem1 /\ uframe m m'.
Proof.
  induction n as [n IH] using lt_wf_ind. intros rem Hn m le l regs aoff Hust.
  pose proof Hust as (Hl & Hr & Ha0 & HaM & Hctx & (oa & Harr & Hoa) & (vl & Hlen & Hvl) &
    (vd & Hdelta & Hvd) & (ob & Hblock & Hob') & HOut & HBlk & HRegs & HRem & Hdisp & HPerm).
  destruct (Z_le_dec (64 - Z.of_nat (length l)) (Z.of_nat (length rem))) as [Hge|Hlt].
  2:{ exists le, m, l, regs, rem, aoff.
      split; [|split; [exact Hust|split; [lia|split; [reflexivity|apply uframe_refl]]]].
      unfold uc_loop, Swhile. eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
      eapply exec_Sseq_2; [|discriminate].
      eapply exec_Sifthenelse with (b := false); [apply (uc_cond_eval le m vd vl Hdelta Hlen)| |apply exec_Sbreak].
      rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity. }
  set (d := (64 - length l)%nat).
  assert (Hd : (0 < d <= length rem)%nat) by (unfold d; lia).
  set (b1 := firstn d rem). set (b2 := skipn d rem).
  assert (Hb1 : length b1 = d) by (unfold b1; apply firstn_length_le; lia).
  assert (Hrem : rem = b1 ++ b2) by (unfold b1, b2; symmetry; apply firstn_skipn).
  assert (Hb2 : length rem = (d + length b2)%nat) by (rewrite Hrem at 1; rewrite app_length, Hb1; reflexivity).
  (* memcpy *)
  destruct (uc_memcpy_exec _delta le m ob oa vd b1 Hblock Harr Hdelta
    ltac:(rewrite Hvd, Hb1; unfold d; lia) ltac:(lia) ltac:(rewrite Hb1; lia)
    ltac:(rewrite Hob', Hb1; unfold d; lia))
    as (m1 & HE1 & HD1 & HF1 & HP1 & HV1).
  { intros i Hi. rewrite Hoa. rewrite (HRem i ltac:(lia)). rewrite Hrem at 1.
    rewrite app_nth1 by exact Hi. reflexivity. }
  { intros ofs Ho. apply HPerm. rewrite Hb1 in Ho. unfold d in Ho. lia. }
  set (oa' := Ptrofs.add oa (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 vd))).
  assert (Hoa' : Ptrofs.unsigned oa' = aoff + Z.of_nat d).
  { unfold oa'. rewrite ptr_add_long by (rewrite Hoa, Hvd; unfold d; lia). rewrite Hoa, Hvd. unfold d. lia. }
  set (le1 := PTree.set _arr (Vptr ba oa') le).
  set (le2 := PTree.set _len (Vlong (Int64.sub vl vd)) le1).
  set (le3 := PTree.set _t'3 (Vptr bo (Ptrofs.repr obase)) le2).
  set (oblk := Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16)).
  assert (Hoblk : Ptrofs.unsigned oblk = cbase + 16) by (apply (ctx_address cbase SBlock); assumption).
  set (le4 := PTree.set _block (Vptr bx oblk) le3).
  set (le5 := PTree.set _delta (Vlong (Int64.repr (Int.signed (Int.repr 64)))) le4).
  assert (Hvx : Mem.valid_block m bx).
  { apply Mem.load_valid_access in HOut. eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies; [exact HOut|constructor]. }
  assert (Hvo : Mem.valid_block m bo).
  { destruct (HRegs 0%nat ltac:(lia)) as [_ PW]. eapply Mem.valid_access_valid_block.
    eapply Mem.valid_access_implies; [exact PW|constructor]. }
  assert (HOut1 : Mem.load Mptr m1 bx cbase = Some (Vptr bo (Ptrofs.repr obase))).
  { rewrite HF1; [exact HOut|]. right; left. change (size_chunk Mptr) with 8. lia. }
  (* compression *)
  destruct (eval_sha_compression_uchar m1 bo (Ptrofs.repr obase) bx oblk regs (l ++ b1) Hr
    ltac:(rewrite app_length, Hb1; unfold d; lia)
    ltac:(rewrite Ptrofs.unsigned_repr by lia; lia) ltac:(rewrite Hoblk; lia))
    as (m2 & HE2 & HS2 & HL2 & HP2 & HV2).
  { unfold sha_dispatch_ok. rewrite HF1 by (left; exact Hgx). exact Hdisp. }
  { intros i Hi. rewrite Ptrofs.unsigned_repr by lia. destruct (HRegs i Hi) as [HLd HVa]. split.
    - rewrite HF1 by (left; exact Hox). exact HLd.
    - destruct HVa as [Pr Al]. split; [|exact Al]. intros ofs Ho. apply HP1, Pr, Ho. }
  { intros i Hi. rewrite Hoblk. destruct (lt_dec i (length l)) as [Hs|Hs].
    - rewrite app_nth1 by exact Hs. rewrite HF1; [apply HBlk; exact Hs|].
      right; left. change (size_chunk Mint8unsigned) with 1. lia.
    - rewrite app_nth2 by lia.
      replace (cbase + 16 + Z.of_nat i) with (Ptrofs.unsigned ob + Z.of_nat (i - length l)) by lia.
      apply HD1. rewrite Hb1. unfold d. lia. }
  set (regs' := SHA256.hash_block regs (be_words (l ++ b1))) in *.
  assert (Hust5 : ust m2 le5 [] regs' b2 (aoff + Z.of_nat d)).
  { unfold ust. cbn [length].
    split; [lia|]. split.
    { unfold regs'. apply sha.common_lemmas.length_hash_block; [exact Hr|].
      apply jet_sha_be32_exec.be_words_length. rewrite app_length, Hb1. unfold d. lia. }
    split; [lia|]. split; [lia|].
    split; [unfold le5, le4, le3, le2, le1; rewrite !PTree.gso by discriminate; exact Hctx|].
    split; [exists oa'; split; [unfold le5, le4, le3, le2, le1; rewrite !PTree.gso by discriminate; apply PTree.gss|exact Hoa']|].
    split.
    { exists (Int64.sub vl vd). split.
      - unfold le5, le4, le3, le2. rewrite !PTree.gso by discriminate. apply PTree.gss.
      - rewrite long_sub_unsigned by lia. rewrite Hvl, Hvd. unfold d. lia. }
    split; [exists (Int64.repr (Int.signed (Int.repr 64))); split; [apply PTree.gss|reflexivity]|].
    split; [exists oblk; split; [unfold le5; rewrite PTree.gso by discriminate; apply PTree.gss|rewrite Hoblk; lia]|].
    split.
    { rewrite HL2; [exact HOut1|apply HV1; exact Hvx|left; auto]. }
    split; [intros i Hi; lia|].
    split.
    { intros i Hi. split.
      - rewrite <- (Ptrofs.unsigned_repr obase) by lia. apply HS2. exact Hi.
      - destruct (HRegs i Hi) as [_ [Pr Al]]. split; [|exact Al].
        intros ofs Ho. apply HP2; [apply HV1; exact Hvo|]. apply HP1, Pr, Ho. }
    split.
    { intros i Hi.
      assert (Hva : Mem.valid_block m ba).
      { pose proof (HRem 0%nat ltac:(lia)) as H0. apply Mem.load_valid_access in H0.
        eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies; [exact H0|constructor]. }
      rewrite HL2; [|apply HV1; exact Hva|left; exact Hao].
      rewrite HF1 by (left; exact Hax).
      replace (aoff + Z.of_nat d + Z.of_nat i) with (aoff + Z.of_nat (d + i)) by lia.
      rewrite (HRem (d + i)%nat ltac:(lia)). rewrite Hrem at 1.
      rewrite app_nth2 by lia. rewrite Hb1. replace (d + i - d)%nat with i by lia. reflexivity. }
    split.
    { unfold sha_dispatch_ok. rewrite HL2; [|apply HV1|left; exact Hgo].
      - rewrite HF1 by (left; exact Hgx). exact Hdisp.
      - unfold sha_dispatch_ok in Hdisp. apply Mem.load_valid_access in Hdisp.
        eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies; [exact Hdisp|constructor]. }
    intros ofs Ho. apply HP2; [apply HV1; exact Hvx|]. apply HP1, HPerm, Ho. }
  destruct (IH (length b2) ltac:(lia) b2 eq_refl m2 le5 [] regs' (aoff + Z.of_nat d) Hust5)
    as (le' & m' & l1 & regs1 & rem1 & aoff1 & HEx & HU & HLen & HAbs & HFr).
  exists le', m', l1, regs1, rem1, aoff1.
  split; [|split; [exact HU|split; [exact HLen|split]]].
  - unfold uc_loop, Swhile.
    eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0) (le1 := le5) (m1 := m2)
      (le2 := le5) (m2 := m2) (out1 := Out_normal); [|constructor|apply exec_Sskip|exact HEx].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m).
    { eapply exec_Sifthenelse with (b := true); [apply (uc_cond_eval le m vd vl Hdelta Hlen)| |apply exec_Sskip].
      rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    unfold uc_loop_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HE1|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m1).
    { apply exec_Sset. eapply eval_Ebinop;
        [apply eval_Etempvar; exact Harr|apply eval_Etempvar; exact Hdelta|reflexivity]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m1).
    { apply exec_Sset. eapply eval_Ebinop;
        [apply eval_Etempvar; unfold le1; rewrite PTree.gso by discriminate; exact Hlen
        |apply eval_Etempvar; unfold le1; rewrite PTree.gso by discriminate; exact Hdelta|reflexivity]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m2).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m1).
      - apply exec_Sset. eapply (eval_ctx_field SOutput) with (chunk := Mptr); [exact Hcb|exact HcM|reflexivity| |].
        + unfold le2, le1. rewrite !PTree.gso by discriminate. exact Hctx.
        + rewrite Z.add_0_r. exact HOut1.
      - change le3 with (set_opttemp None Vundef le3) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_compression_uchar) Ptrofs.zero)
          (vargs := [Vptr bo (Ptrofs.repr obase); Vptr bx oblk]) (f := Internal f_sha256_compression_uchar).
        + reflexivity.
        + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_compression_uchar_symbol]|].
          apply deref_loc_reference; reflexivity.
        + eapply eval_Econs; [apply eval_Etempvar; apply PTree.gss|reflexivity|].
          eapply eval_Econs with (v1 := Vptr bx oblk); [|reflexivity|apply eval_Enil].
          apply eval_ctx_block. unfold le3, le2, le1. rewrite !PTree.gso by discriminate. exact Hctx.
        + exact sha_compression_uchar_funct.
        + reflexivity.
        + exact HE2. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m2).
    { apply exec_Sset. apply eval_ctx_block.
      unfold le3, le2, le1. rewrite !PTree.gso by discriminate. exact Hctx. }
    apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
  - rewrite <- HAbs. rewrite Hrem at 1. rewrite absorb_i_app.
    assert (Hfill1 : (length l + length b1 = 64)%nat) by (rewrite Hb1; unfold d; lia).
    assert (Hfill2 : b1 <> []).
    { intro Hz. apply (f_equal (@length int)) in Hz. cbn [length] in Hz. lia. }
    rewrite (absorb_i_fill l regs b1 Hfill1 Hfill2). reflexivity.
  - eapply uframe_trans; [|exact HFr]. split; [|split].
    + intros ch b ofs Hv Hx Ho. rewrite HL2; [|apply HV1; exact Hv|rewrite Ptrofs.unsigned_repr by lia; exact Ho].
      apply HF1. destruct Hx as [Hx|[Hx|Hx]]; [left; exact Hx|right; left; lia|right; right].
      rewrite Hb1. unfold d. lia.
    + intros b ofs k p Hv Hp. apply HP2; [apply HV1; exact Hv|]. apply HP1, Hp.
    + intros b Hv. apply HV2, HV1, Hv.
Qed.
End Loop.
