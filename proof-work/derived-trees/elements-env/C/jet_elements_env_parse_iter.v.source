(** One iteration of the loop of [parseNullData] against the functional
    step [pn_step]: either the function takes a failure exit
    ([result->op = NULL]) or one more opcode entry is committed. *)
From Coq Require Import ZArith List Lia PeanoNat Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_be32_exec C.jet_sha_block_local C.jet_sha_uchars_exec.
Require Import C.jet_sha_add_n_init C.jet_sha_ctx_abs.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_hashbuffer C.jet_elements_env_nulldata_count.
Require Import C.jet_elements_env_parse_defs C.jet_elements_env_parse_mem C.jet_elements_env_parse_ops.
Require Import C.jet_elements_env_parse_hash.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 300.

Ltac zi :=
  repeat match goal with
         | H : ?a <> ?b |- _ => match type of a with block => clear H end
         end; lia.

Section ParseIter.
Variable Hmodel : memcpy_model.
Variables (e : env) (bC bRs : block).
Hypothesis HeC : e!_ctx = Some (bC, CTX).
Hypothesis HeR : e!__res = Some (bRs, CTX).
Hypothesis Hg1 : e!_sha256_init = None.
Hypothesis Hg3 : e!_sha256_uchars = None.
Hypothesis Hg5 : e!_sha256_finalize = None.
Variables (br : block) (or_ : Z) (ba : block) (oa : Z) (bl : block) (ol : Z) (bop : block) (oop alen : Z).
Variables (bsp : block) (osp : Z) (len : int) (bb : block) (ob : ptrofs) (bs : list int).

Hypothesis Hor : 0 <= or_ /\ or_ + 16 <= Ptrofs.max_unsigned.
Hypothesis HorA : (8 | or_).
Hypothesis Hoa : 0 <= oa /\ oa + 8 <= Ptrofs.max_unsigned.
Hypothesis Hol : 0 <= ol /\ ol + 8 <= Ptrofs.max_unsigned.
Hypothesis Hoop : 0 <= oop /\ oop + 36 * alen <= Ptrofs.max_unsigned.
Hypothesis HoopA : (4 | oop).
Hypothesis Halen : 0 <= alen <= 4294967295.
Hypothesis Hosp : 0 <= osp /\ osp + 16 <= Ptrofs.max_unsigned.
Hypothesis HobM : Ptrofs.unsigned ob + Int.unsigned len <= Ptrofs.max_unsigned.
Hypothesis Hsep : br <> bop \/ or_ + 16 <= oop \/ oop + 36 * alen <= or_.
Hypothesis Nba : ba <> bop.
Hypothesis Nbl : bl <> bop.
Hypothesis Nbsp : bsp <> bop.
Hypothesis Nbb : bb <> bop.
Hypothesis NG : GC <> bop.
Hypothesis NM : GM <> bop.
Hypothesis Nbar : ba <> br.
Hypothesis Nblr : bl <> br.
Hypothesis Nbspr : bsp <> br.
Hypothesis Nbbr : bb <> br.
Hypothesis NGr : GC <> br.
Hypothesis NMr : GM <> br.
Hypothesis NCr : br <> bC.
Hypothesis NRr : br <> bRs.
Hypothesis NCa : ba <> bC.
Hypothesis NRa : ba <> bRs.
Hypothesis NCl : bl <> bC.
Hypothesis NRl : bl <> bRs.
Hypothesis NCo : bop <> bC.
Hypothesis NRo : bop <> bRs.
Hypothesis NCs : bsp <> bC.
Hypothesis NRs : bsp <> bRs.
Hypothesis NCb : bb <> bC.
Hypothesis NRb : bb <> bRs.
Hypothesis NCG : GC <> bC.
Hypothesis NRG : GC <> bRs.
Hypothesis NCM : GM <> bC.
Hypothesis NRM : GM <> bRs.
Hypothesis NRC : bRs <> bC.

Let PM := pm bC bRs br or_ ba oa bl ol bop oop alen bsp osp len bb ob bs.
Let PL := pl br or_ ba oa bl ol bsp osp.
Let PLS := pls br or_ ba oa bl ol bsp osp.

(** The functional step. *)
Definition pn_op (i : Z) : option (Z * pn_ent) :=
  let c := nd_byte bs i in
  if 96 <? c then None
  else if 79 <=? c then Some (i + 1, (4 + (c - 79), None))
  else match nd_skip len bs c (i + 1) with
       | None => None
       | Some (i', sk) =>
           if Int.unsigned len - i' <? sk then None else Some (i' + sk, (pn_kindv c, Some (pn_data bs i' sk)))
       end.

Definition pn_step (n i : Z) : option (Z * pn_ent) :=
  if alen <=? n then None else pn_op i.

(** What the function may change of the memory it was given: the result
    structure and the opcode array (and its two local contexts). *)
Definition pn_fr (m m' : mem) : Prop :=
  (forall ch b ofs, Mem.valid_block m b -> b <> bC -> b <> bRs ->
     (b <> br \/ ofs + size_chunk ch <= or_ \/ or_ + 16 <= ofs) ->
     (b <> bop \/ ofs + size_chunk ch <= oop \/ oop + 36 * alen <= ofs) ->
     Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
  (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
  (forall b, Mem.valid_block m b -> Mem.valid_block m' b).

Lemma pn_fr_refl m : pn_fr m m.
Proof. repeat split; auto. Qed.

Lemma pn_fr_trans m1 m2 m3 : pn_fr m1 m2 -> pn_fr m2 m3 -> pn_fr m1 m3.
Proof.
  intros (L1 & P1 & V1) (L2 & P2 & V2). split; [|split].
  - intros ch b ofs Hb N1 N2 H1 H2. rewrite L2 by (try (apply V1; exact Hb); assumption). apply L1; assumption.
  - intros b ofs k p Hb Hp. apply P2; [apply V1, Hb|apply P1; assumption].
  - intros b Hb. apply V2, V1, Hb.
Qed.

Lemma pn_fr_change n m m' : 0 <= n -> pm_change bC bRs bop oop alen n m m' -> pn_fr m m'.
Proof.
  intros Hn (LC & PC & VC). split; [|split; assumption].
  intros ch b ofs Hb N1 N2 H1 H2. apply LC; try assumption.
  destruct H2 as [H|[H|H]]; [left; exact H|right; left; zi|right; right; exact H].
Qed.

Lemma pn_fr_store_res m ch ofs v m' :
  Mem.store ch m br ofs v = Some m' -> or_ <= ofs -> ofs + size_chunk ch <= or_ + 16 -> pn_fr m m'.
Proof.
  intros HS H1 H2. split; [|split].
  - intros ch' b o Hb _ _ Hr _. apply (Mem.load_store_other _ _ _ _ _ _ HS).
    destruct Hr as [H|[H|H]]; [left; exact H|right; left; zi|right; right; zi].
  - intros b o k p _ Hp. eapply Mem.perm_store_1; [exact HS|exact Hp].
  - intros b Hb. eapply Mem.store_valid_block_1; [exact HS|exact Hb].
Qed.

Lemma pm_change_store_op n m ch ofs v m' :
  Mem.store ch m bop ofs v = Some m' -> oop + 36 * n <= ofs -> ofs + size_chunk ch <= oop + 36 * alen ->
  pm_change bC bRs bop oop alen n m m'.
Proof.
  intros HS H1 H2. split; [|split].
  - intros ch' b o Hb _ _ Hr. apply (Mem.load_store_other _ _ _ _ _ _ HS).
    destruct Hr as [H|[H|H]]; [left; exact H|right; left; zi|right; right; zi].
  - intros b o k p _ Hp. eapply Mem.perm_store_1; [exact HS|exact Hp].
  - intros b Hb. eapply Mem.store_valid_block_1; [exact HS|exact Hb].
Qed.

Lemma pm_keeps n ents m m' : PM m n ents -> pm_change bC bRs bop oop alen n m m' -> PM m' n ents.
Proof.
  exact (pm_change_keeps bC bRs br or_ ba oa bl ol bop oop alen bsp osp len bb ob bs Halen Hsep
    Nba Nbl Nbsp Nbb NG NM Nbar Nblr Nbspr Nbbr NGr NMr NCr NRr NCa NRa NCl NRl NCo NRo NCs NRs NCb NRb
    NCG NRG NCM NRM n ents m m').
Qed.

(** [++result->len]: the entry written at index [n] is committed. *)
Lemma pn_s2_exec le m n ents (en : pn_ent) i :
  PM m n ents -> PL le i -> n < alen -> pn_ent_at bop oop m n en ->
  exists le' m',
    Clight2.exec_stmt sha_ge e le m pn_s2 E0 le' m' Out_normal /\
    PM m' (n + 1) (ents ++ [en]) /\ PL le' i /\ pn_fr m m'.
Proof.
  intros HM HP Hlt HEn. pose proof HM as (HN & HNa & Hop & Hlen & _ & _ & _ & _ & _ & _ & _ & VA2 & _).
  pose proof HP as (Hli & Hr & _).
  destruct (Mem.valid_access_store m Mint64 br (or_ + 8) (Vlong (Int64.repr (n + 1))) VA2) as [m' HS].
  set (le1 := PTree.set _t'12 (Vlong (Int64.repr n)) le).
  assert (K12 : pn_keeps _t'12) by pn_keeps_tac.
  assert (HP1 : PL le1 i) by (apply pl_set; assumption).
  exists le1, m'. split; [|split; [|split; [exact HP1|]]].
  - unfold pn_s2.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
    { apply exec_Sset. exact (pn_len_value e br or_ len Hor le m _ Hr Hlen). }
    eapply exec_Sassign with (v2 := Vlong (Int64.repr (n + 1))) (v := Vlong (Int64.repr (n + 1))).
    + exact (pn_len_lvalue e br or_ len Hor le1 m (proj1 (proj2 HP1))).
    + eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|apply eval_Econst_int|].
      rewrite <- (nd_i64_add n 1) by zi. reflexivity.
    + reflexivity.
    + eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
      rewrite Ptrofs.unsigned_repr by zi. exact HS.
  - exact (pm_commit bC bRs br or_ ba oa bl ol bop oop alen bsp osp len bb ob bs Hsep Nbar Nblr Nbspr Nbbr
      NGr NMr n ents en m m' HM Hlt HEn HS).
  - eapply pn_fr_store_res; [exact HS|zi|change (size_chunk Mint64) with 8; zi].
Qed.
Lemma pn_seq1 le m s1 s2 le1 m1 le2 m2 out :
  Clight2.exec_stmt sha_ge e le m s1 E0 le1 m1 Out_normal ->
  Clight2.exec_stmt sha_ge e le1 m1 s2 E0 le2 m2 out ->
  Clight2.exec_stmt sha_ge e le m (Ssequence s1 s2) E0 le2 m2 out.
Proof. intros H1 H2. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eassumption. Qed.

Lemma pn_seqr le m s1 s2 le1 m1 :
  Clight2.exec_stmt sha_ge e le m s1 E0 le1 m1 (Out_return None) ->
  Clight2.exec_stmt sha_ge e le m (Ssequence s1 s2) E0 le1 m1 (Out_return None).
Proof. intros H1. apply exec_Sseq_2; [exact H1|discriminate]. Qed.

Lemma pn_fail_post m mk m' :
  pn_fr m mk -> Mem.store Mptr mk br or_ (Vlong Int64.zero) = Some m' ->
  Mem.load Mptr m' br or_ = Some (Vlong Int64.zero) /\ pn_fr m m'.
Proof.
  intros HF HS. split.
  - rewrite (Mem.load_store_same _ _ _ _ _ _ HS). reflexivity.
  - eapply pn_fr_trans; [exact HF|].
    eapply pn_fr_store_res; [exact HS|zi|change (size_chunk Mptr) with 8; zi].
Qed.

(** One iteration. *)
Lemma pn_iter le m n ents i :
  PM m n ents -> PL le i -> 1 <= i < Int.unsigned len ->
  match pn_step n i with
  | None =>
      exists le' m',
        Clight2.exec_stmt sha_ge e le m pn_s1 E0 le' m' (Out_return None) /\
        Mem.load Mptr m' br or_ = Some (Vlong Int64.zero) /\ pn_fr m m'
  | Some (i', en) =>
      exists le1 m1 le2 m2,
        Clight2.exec_stmt sha_ge e le m pn_s1 E0 le1 m1 Out_normal /\
        Clight2.exec_stmt sha_ge e le1 m1 pn_s2 E0 le2 m2 Out_normal /\
        PM m2 (n + 1) (ents ++ [en]) /\ PL le2 i' /\ i < i' <= Int.unsigned len /\ pn_fr m m2
  end.
Proof.
  intros HM HP Hi.
  pose proof HM as (HN & HNa & Hop & Hlen & Hal & Hall & HLen & HBuf & HBs & Hents & VA1 & VA2 & RP & RC & RR & Hdisp & HGM).
  assert (Hn0 : 0 <= n) by zi.
  pose proof HP as (Hli & Hr & Ha & Hl & Hsp).
  pose proof (Int.unsigned_range_2 len) as HLr. change Int.max_unsigned with 4294967295 in HLr.
  set (le0 := PTree.set _t'43 (Vint len) le).
  assert (K43 : pn_keeps _t'43) by pn_keeps_tac.
  assert (HP0 : PL le0 i) by (apply pl_set; assumption).
  assert (HA : Clight2.exec_stmt sha_ge e le m
     (Ssequence (Sset _t'43 (Efield PSPK _len tuint))
        (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _t'43 tuint) tint) Sskip Sbreak))
     E0 le0 m Out_normal).
  { eapply pn_seq1; [apply exec_Sset; exact (nd_ev_len e m bsp osp len Hosp HLen le Hsp)|].
    eapply pn_if with (b := true); [|reflexivity|apply exec_Sskip].
    eapply eval_Ebinop; [apply eval_Etempvar; unfold le0; rewrite PTree.gso by discriminate; exact Hli
                        |apply eval_Etempvar; apply PTree.gss|].
    change (Some (Val.of_bool (Int64.ltu (Int64.repr i) (Int64.repr (Int.unsigned len)))) = Some (Val.of_bool true)).
    rewrite nd_i64_ltu by zi. rewrite (proj2 (Z.ltb_lt i (Int.unsigned len))) by zi. reflexivity. }
  assert (T1 : pn_trip _t'2 _t'41 _t'42) by (unfold pn_trip, nd_trip; repeat split; try pn_keeps_tac;
    intros; rewrite ?PTree.gso by discriminate; repeat split; reflexivity).
  destruct (pn_read_code e br or_ ba oa bl ol bsp osp len bb ob bs Hosp m HBuf HobM HBs _t'2 _t'41 _t'42 le0 i
              T1 HP0 ltac:(zi)) as (le1 & HB & HP1 & Hc1 & Hcr).
  destruct (pn_check_exec e br or_ ba oa bl ol alen bsp osp len Hor Hol Halen m le1 (i + 1) (nd_b bs i) n
              HP1 Hc1 Hcr Hall Hlen ltac:(zi) VA1) as (le2 & HP2 & Hc2 & HC).
  change (Int.unsigned (nd_b bs i)) with (nd_byte bs i) in HC.
  assert (HE79 : eval_expr sha_ge e le2 m
     (Ebinop Ole (Econst_int (Int.repr 79) tint) (Etempvar _code tuchar) tint)
     (Val.of_bool (79 <=? nd_byte bs i))).
  { exact (nd_ev_le_code e m len le2 (nd_b bs i) 79 Hc2 ltac:(zi) Hcr). }
  unfold pn_step, pn_op, pn_s1. cbv zeta.
  destruct (alen <=? n) eqn:EA.
  { cbn [orb] in HC. destruct HC as (m' & HC & HSt). exists le2, m'. split.
    - eapply pn_seq1; [exact HA|]. eapply pn_seq1; [exact HB|]. apply pn_seqr. exact HC.
    - exact (pn_fail_post m m m' (pn_fr_refl m) HSt). }
  apply Z.leb_gt in EA.
  destruct (96 <? nd_byte bs i) eqn:E96.
  { cbn [orb] in HC. destruct HC as (m' & HC & HSt). exists le2, m'. split.
    - eapply pn_seq1; [exact HA|]. eapply pn_seq1; [exact HB|]. apply pn_seqr. exact HC.
    - exact (pn_fail_post m m m' (pn_fr_refl m) HSt). }
  cbn [orb] in HC. apply Z.ltb_ge in E96.
  pose proof HP2 as (Hli2 & Hr2 & Ha2 & Hl2 & Hsp2).
  destruct (79 <=? nd_byte bs i) eqn:E79.
  { (* a one-byte opcode *)
    apply Z.leb_le in E79.
    assert (K37 : pn_keeps _t'37) by pn_keeps_tac. assert (K38 : pn_keeps _t'38) by pn_keeps_tac.
    destruct (pn_setcode_exec e br or_ ba oa bop oop alen len Hor Hoa Hoop HoopA Halen _t'37 _t'38
       (Ebinop Oadd (Econst_int (Int.repr 4) tint)
          (Ebinop Osub (Etempvar _code tuchar) (Econst_int (Int.repr 79) tint) tint) tint)
       (Int.repr (4 + (nd_byte bs i - 79))) le2 m n Hr2 Ha2 K37 K38
       ltac:(intros; rewrite PTree.gso by discriminate; reflexivity) Hal Hlen ltac:(zi) RP) as (m3 & HS & HSt).
    { intros le' m' Hc'.
      eapply eval_Ebinop with (v1 := Vint (Int.repr 4)) (v2 := Vint (Int.repr (nd_byte bs i - 79))).
      - apply eval_Econst_int.
      - eapply eval_Ebinop with (v1 := Vint (nd_b bs i)) (v2 := Vint (Int.repr 79)).
        + apply eval_Etempvar. rewrite Hc'. exact Hc2.
        + apply eval_Econst_int.
        + change (Some (Vint (Int.sub (nd_b bs i) (Int.repr 79))) = Some (Vint (Int.repr (nd_byte bs i - 79)))).
          unfold Int.sub. rewrite (Int.unsigned_repr 79) by (vm_compute; split; discriminate). reflexivity.
      - change (Some (Vint (Int.add (Int.repr 4) (Int.repr (nd_byte bs i - 79)))) =
                Some (Vint (Int.repr (4 + (nd_byte bs i - 79))))).
        rewrite Int.add_unsigned.
        rewrite !Int.unsigned_repr by (change Int.max_unsigned with 4294967295; zi). reflexivity. }
    { reflexivity. }
    set (le3 := PTree.set _t'38 (Vlong (Int64.repr n)) (PTree.set _t'37 (Vptr bop (Ptrofs.repr oop)) le2)) in *.
    assert (HP3 : PL le3 (i + 1)) by (apply pl_set; [exact K38|]; apply pl_set; assumption).
    assert (HCh : pm_change bC bRs bop oop alen n m m3).
    { eapply pm_change_store_op; [exact HSt|zi|change (size_chunk Mint32) with 4; zi]. }
    pose proof (pm_keeps n ents m m3 HM HCh) as HM3.
    assert (HEn : pn_ent_at bop oop m3 n (4 + (nd_byte bs i - 79), None)).
    { split; [|exact I]. rewrite (Mem.load_store_same _ _ _ _ _ _ HSt). reflexivity. }
    destruct (pn_s2_exec le3 m3 n ents _ (i + 1) HM3 HP3 EA HEn) as (le4 & m4 & HX2 & HM4 & HP4 & HF4).
    exists le3, m3, le4, m4. split; [|split; [exact HX2|split; [exact HM4|split; [exact HP4|split; [zi|]]]]].
    - eapply pn_seq1; [exact HA|]. eapply pn_seq1; [exact HB|]. eapply pn_seq1; [exact HC|].
      eapply pn_if with (b := true); [exact HE79|reflexivity|exact HS].
    - eapply pn_fr_trans; [exact (pn_fr_change n m m3 Hn0 HCh)|exact HF4]. }
  apply Z.leb_gt in E79.
  (* a data push *)
  set (le3 := PTree.set _skip (Vlong (Int64.repr 0)) le2).
  assert (HP3 : PLS le3 (i + 1) (nd_b bs i) 0).
  { unfold PLS, pls, pl, le3. rewrite PTree.gss, !PTree.gso by discriminate. repeat split; assumption. }
  assert (HX3 : Clight2.exec_stmt sha_ge e le2 m (Sset _skip (Ecast (Econst_int (Int.repr 0) tint) tulong))
                  E0 le3 m Out_normal).
  { apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity]. }
  pose proof (pn_kind_exec e br or_ ba oa bl ol bop oop alen bsp osp len bb ob bs Hor Hoa Hoop HoopA Halen Hosp
                m HLen HBuf HobM HBs le3 n (i + 1) (nd_b bs i) HP3 ltac:(zi) ltac:(change (Int.unsigned (nd_b bs i)) with (nd_byte bs i); zi)
                Hal Hlen ltac:(zi) RP VA1) as HK.
  cbv zeta in HK. change (Int.unsigned (nd_b bs i)) with (nd_byte bs i) in HK.
  destruct (nd_skip len bs (nd_byte bs i) (i + 1)) as [[i' sk]|] eqn:ES.
  2: { destruct HK as (le4 & m4 & HK & HSt). exists le4, m4. split.
       - eapply pn_seq1; [exact HA|]. eapply pn_seq1; [exact HB|]. eapply pn_seq1; [exact HC|].
         eapply pn_if with (b := false); [exact HE79|reflexivity|].
         eapply pn_seq1; [exact HX3|]. apply pn_seqr. exact HK.
       - exact (pn_fail_post m m m4 (pn_fr_refl m) HSt). }
  destruct HK as (le4 & m4 & HK & HP4 & Hi' & Hsk & HSt).
  assert (HCh : pm_change bC bRs bop oop alen n m m4).
  { eapply pm_change_store_op; [exact HSt|zi|change (size_chunk Mint32) with 4; zi]. }
  pose proof (pm_keeps n ents m m4 HM HCh) as HM4.
  pose proof HM4 as (_ & _ & _ & Hlen4 & Hal4 & _ & HLen4 & HBuf4 & HBs4 & _ & VA14 & _ & RP4 & RC4 & RR4 & Hdisp4 & HGM4).
  pose proof (pn_tail_exec Hmodel e bC bRs HeC HeR Hg1 Hg3 Hg5 br or_ ba oa bl ol bop oop alen bsp osp len bb ob bs
                Hor Hoa Hoop HoopA Halen Hosp NCo NRC (not_eq_sym NRo) NCb Nbb NRb NCs Nbsp NRs NCG NG NCM NM NRG NRM
                le4 m4 n i' (nd_b bs i) sk HP4 ltac:(zi) Hsk ltac:(zi) HLen4 HBuf4 HobM HBs4 Hal4 Hlen4 VA14 RP4 RC4 RR4
                Hdisp4 HGM4) as HT.
  cbv zeta in HT.
  destruct (Int.unsigned len - i' <? sk) eqn:ET.
  { destruct HT as (le5 & m5 & HT & HSt5). exists le5, m5. split.
    - eapply pn_seq1; [exact HA|]. eapply pn_seq1; [exact HB|]. eapply pn_seq1; [exact HC|].
      eapply pn_if with (b := false); [exact HE79|reflexivity|].
      eapply pn_seq1; [exact HX3|]. eapply pn_seq1; [exact HK|exact HT].
    - exact (pn_fail_post m m4 m5 (pn_fr_change n m m4 Hn0 HCh) HSt5). }
  apply Z.ltb_ge in ET.
  destruct HT as (le5 & m5 & HT & HP5 & HH5 & HL5 & HPm5 & HV5).
  assert (HCh5 : pm_change bC bRs bop oop alen n m4 m5).
  { split; [|split; assumption]. intros ch b ofs Hb N1 N2 Hd. apply HL5; try assumption.
    destruct Hd as [H|[H|H]]; [left; exact H|right; left; exact H|right; right; zi]. }
  pose proof (pm_keeps n ents m4 m5 HM4 HCh5) as HM5.
  assert (HEn : pn_ent_at bop oop m5 n (pn_kindv (nd_byte bs i), Some (pn_data bs i' sk))).
  { split; [|exact HH5]. cbn [fst].
    pose proof (Mem.load_store_same _ _ _ _ _ _ HSt) as HLs.
    rewrite HL5; [exact HLs|eapply Mem.valid_access_valid_block; eapply Mem.valid_access_implies; [exact (Mem.load_valid_access _ _ _ _ _ HLs)|constructor]|exact NCo|exact NRo|right; right; zi]. }
  destruct (pn_s2_exec le5 m5 n ents _ (i' + sk) HM5 (proj1 HP5) EA HEn) as (le6 & m6 & HX2 & HM6 & HP6 & HF6).
  exists le5, m5, le6, m6. split; [|split; [exact HX2|split; [exact HM6|split; [exact HP6|split; [zi|]]]]].
  - eapply pn_seq1; [exact HA|]. eapply pn_seq1; [exact HB|]. eapply pn_seq1; [exact HC|].
    eapply pn_if with (b := false); [exact HE79|reflexivity|].
    eapply pn_seq1; [exact HX3|]. eapply pn_seq1; [exact HK|exact HT].
  - eapply pn_fr_trans; [exact (pn_fr_change n m m5 Hn0 (pm_change_trans bC bRs bop oop alen n m m4 m5 HCh HCh5))|exact HF6].
Qed.
(** The loop. *)
Fixpoint pn_loop (fuel : nat) (n i : Z) (ents : list pn_ent) : option (list pn_ent) :=
  match fuel with
  | O => Some ents
  | S f =>
      if i <? Int.unsigned len then
        match pn_step n i with
        | None => None
        | Some (i', en) => pn_loop f (n + 1) i' (ents ++ [en])
        end
      else Some ents
  end.

Lemma pn_loop_exec fuel : forall le m n ents i,
  PM m n ents -> PL le i -> 1 <= i <= Int.unsigned len -> Int.unsigned len - i <= Z.of_nat fuel ->
  match pn_loop fuel n i ents with
  | None =>
      exists le' m',
        Clight2.exec_stmt sha_ge e le m (Sloop pn_s1 pn_s2) E0 le' m' (Out_return None) /\
        Mem.load Mptr m' br or_ = Some (Vlong Int64.zero) /\ pn_fr m m'
  | Some ents' =>
      exists le' m' n' i',
        Clight2.exec_stmt sha_ge e le m (Sloop pn_s1 pn_s2) E0 le' m' Out_normal /\
        PM m' n' ents' /\ PL le' i' /\ pn_fr m m'
  end.
Proof.
  assert (HExit : forall le m n ents, PM m n ents -> PL le (Int.unsigned len) ->
    exists le' m' n' i',
      Clight2.exec_stmt sha_ge e le m (Sloop pn_s1 pn_s2) E0 le' m' Out_normal /\
      PM m' n' ents /\ PL le' i' /\ pn_fr m m').
  { intros le m n ents HM HP.
    pose proof HM as (_ & _ & _ & _ & _ & _ & HLen & _).
    pose proof HP as (Hli & Hr & Ha & Hl & Hsp).
    pose proof (Int.unsigned_range_2 len) as HLr. change Int.max_unsigned with 4294967295 in HLr.
    assert (K43 : pn_keeps _t'43) by pn_keeps_tac.
    exists (PTree.set _t'43 (Vint len) le), m, n, (Int.unsigned len).
    split; [|split; [exact HM|split; [apply pl_set; assumption|apply pn_fr_refl]]].
    eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
    unfold pn_s1. apply exec_Sseq_2; [|discriminate].
    eapply pn_seq1; [apply exec_Sset; exact (nd_ev_len e m bsp osp len Hosp HLen le Hsp)|].
    eapply pn_if with (b := false); [|reflexivity|apply exec_Sbreak].
    eapply eval_Ebinop; [apply eval_Etempvar; rewrite PTree.gso by discriminate; exact Hli
                        |apply eval_Etempvar; apply PTree.gss|].
    change (Some (Val.of_bool (Int64.ltu (Int64.repr (Int.unsigned len)) (Int64.repr (Int.unsigned len)))) =
            Some (Val.of_bool false)).
    rewrite nd_i64_ltu by zi. rewrite Z.ltb_irrefl. reflexivity. }
  induction fuel as [|fuel IH]; intros le m n ents i HM HP Hi Hf.
  - cbn [pn_loop]. assert (i = Int.unsigned len) by zi. subst i. exact (HExit le m n ents HM HP).
  - cbn [pn_loop]. destruct (i <? Int.unsigned len) eqn:EL.
    2: { apply Z.ltb_ge in EL. assert (i = Int.unsigned len) by zi. subst i. exact (HExit le m n ents HM HP). }
    apply Z.ltb_lt in EL.
    pose proof (pn_iter le m n ents i HM HP ltac:(zi)) as HI.
    destruct (pn_step n i) as [[i' en]|].
    2: { destruct HI as (le' & m' & HX & HL0 & HF). exists le', m'. split; [|split; assumption].
         eapply exec_Sloop_stop1 with (out' := Out_return None); [exact HX|constructor]. }
    destruct HI as (le1 & m1 & le2 & m2 & HX1 & HX2 & HM2 & HP2 & Hi2 & HF2).
    pose proof (IH le2 m2 (n + 1) (ents ++ [en]) i' HM2 HP2 ltac:(zi) ltac:(zi)) as HR.
    destruct (pn_loop fuel (n + 1) i' (ents ++ [en])) as [ents'|].
    + destruct HR as (le' & m' & n' & i'' & HX & HM' & HP' & HF').
      exists le', m', n', i''. split; [|split; [exact HM'|split; [exact HP'|eapply pn_fr_trans; eassumption]]].
      change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop; [exact HX1|constructor|exact HX2|exact HX].
    + destruct HR as (le' & m' & HX & HL0 & HF').
      exists le', m'. split; [|split; [exact HL0|eapply pn_fr_trans; eassumption]].
      change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop; [exact HX1|constructor|exact HX2|exact HX].
Qed.
End ParseIter.
