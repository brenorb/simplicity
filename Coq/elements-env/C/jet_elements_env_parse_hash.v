(** The data-hash step of [parseNullData]:
      if (len - i < skip) { result->op = NULL; return; }
      { ctx = sha256_init(op[n].dataHash.s); sha256_uchars(&ctx, &buf[i], skip);
        sha256_finalize(&ctx); }
      i += skip;
    The entry's [dataHash] receives [hash_buffer_regs] of the pushed bytes
    [pn_data]; only the local contexts and that field change. *)
From Coq Require Import ZArith List Lia PeanoNat Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_sha256_iv_init.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_be32_exec C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_be64_exec C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_add_n_init.
Require Import C.jet_sha_finalize_exec C.jet_sha_tapdata_prep C.jet_sha_ctx_abs.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_ctxo C.jet_elements_env_ctxo_uchars.
Require Import C.jet_elements_env_tx_calls C.jet_elements_env_hashbuffer C.jet_elements_env_countfee.
Require Import C.jet_elements_env_nulldata_count C.jet_elements_env_parse_defs C.jet_elements_env_parse_ops.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 300.

Ltac zh :=
  repeat match goal with
         | H : ?a <> ?b |- _ => match type of a with block => clear H end
         end; lia.

(** The bytes of a push of [sk] bytes at position [i] of the script. *)
Definition pn_data (bs : list int) (i sk : Z) : list int :=
  map (fun k => nd_b bs (i + Z.of_nat k)) (seq 0 (Z.to_nat sk)).

Lemma pn_data_length bs i sk : 0 <= sk -> Z.of_nat (length (pn_data bs i sk)) = sk.
Proof. intros H. unfold pn_data. rewrite map_length, seq_length. apply Z2Nat.id. exact H. Qed.

Lemma pn_data_nth bs i sk k : (k < length (pn_data bs i sk))%nat ->
  nth k (pn_data bs i sk) Int.zero = nd_b bs (i + Z.of_nat k).
Proof.
  unfold pn_data. rewrite map_length, seq_length. intros Hk.
  rewrite (nth_indep _ Int.zero ((fun k0 => nd_b bs (i + Z.of_nat k0)) 0%nat))
    by (rewrite map_length, seq_length; exact Hk).
  rewrite (map_nth (fun k0 => nd_b bs (i + Z.of_nat k0))). rewrite seq_nth by exact Hk. reflexivity.
Qed.

Section ParseHash.
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
Hypothesis Hoa : 0 <= oa /\ oa + 8 <= Ptrofs.max_unsigned.
Hypothesis Hoop : 0 <= oop /\ oop + 36 * alen <= Ptrofs.max_unsigned.
Hypothesis HoopA : (4 | oop).
Hypothesis Halen : 0 <= alen <= 4294967295.
Hypothesis Hosp : 0 <= osp /\ osp + 16 <= Ptrofs.max_unsigned.
Hypothesis Hox : bop <> bC.
Hypothesis Hrx : bRs <> bC.
Hypothesis Hro : bRs <> bop.
Hypothesis Hbx : bb <> bC.
Hypothesis Hbo : bb <> bop.
Hypothesis Hbr : bb <> bRs.
Hypothesis Hsx : bsp <> bC.
Hypothesis Hso : bsp <> bop.
Hypothesis Hsr : bsp <> bRs.
Hypothesis Hgx : GC <> bC.
Hypothesis Hgo : GC <> bop.
Hypothesis Hcx : GM <> bC.
Hypothesis Hco : GM <> bop.
Hypothesis Hgr : GC <> bRs.
Hypothesis Hcr : GM <> bRs.

Let L : Z := Int.unsigned len.
Let PLS := pls br or_ ba oa bl ol bsp osp.

Lemma pn_hash_out le m ta tn n :
  le!ta = Some (Vptr bop (Ptrofs.repr oop)) -> le!tn = Some (Vlong (Int64.repr n)) -> 0 <= n < alen ->
  eval_expr sha_ge e le m
    (Efield (Efield (Ederef (Ebinop Oadd (Etempvar ta PO) (Etempvar tn tulong) PO) OPC) _dataHash MID) _s
       (tarray tuint 8))
    (Vptr bop (Ptrofs.repr (oop + 36 * n))).
Proof.
  intros Ha Hn Hr.
  replace (Ptrofs.repr (oop + 36 * n)) with
    (Ptrofs.add (Ptrofs.add (Ptrofs.repr (oop + 36 * n)) (Ptrofs.repr 0)) (Ptrofs.repr 0))
    by (change (Ptrofs.repr 0) with Ptrofs.zero; rewrite !Ptrofs.add_zero; reflexivity).
  eapply eval_envu_field_array;
    [reflexivity|exact envu_sha256_midstate_s|intros ch; discriminate|reflexivity|].
  eapply eval_envu_field_struct; [reflexivity|exact envu_opcode_dataHash|].
  eapply eval_Elvalue; [|apply deref_loc_copy; reflexivity].
  apply eval_Ederef. exact (pn_opcode_ptr e bop oop alen len Hoop Halen le m ta tn n Ha Hn Hr).
Qed.

Lemma pn_tail_exec le m n i (c : int) sk :
  PLS le i c sk -> 1 <= i <= L -> 0 <= sk < 4294967296 -> 0 <= n < alen ->
  Mem.load Mint32 m bsp (osp + 8) = Some (Vint len) ->
  (0 < L -> Mem.load Mptr m bsp osp = Some (Vptr bb ob)) ->
  Ptrofs.unsigned ob + L <= Ptrofs.max_unsigned ->
  (forall k, 0 <= k < L ->
     Mem.load Mint8unsigned m bb (Ptrofs.unsigned ob + k) = Some (Vint (nth (Z.to_nat k) bs Int.zero))) ->
  Mem.load Mptr m ba oa = Some (Vptr bop (Ptrofs.repr oop)) ->
  Mem.load Mint64 m br (or_ + 8) = Some (Vlong (Int64.repr n)) ->
  Mem.valid_access m Mptr br or_ Writable ->
  Mem.range_perm m bop oop (oop + 36 * alen) Cur Writable ->
  Mem.range_perm m bC 0 88 Cur Freeable -> Mem.range_perm m bRs 0 88 Cur Freeable ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  if L - i <? sk
  then exists le' m',
         Clight2.exec_stmt sha_ge e le m pn_tail E0 le' m' (Out_return None) /\
         Mem.store Mptr m br or_ (Vlong Int64.zero) = Some m'
  else exists le' m',
         Clight2.exec_stmt sha_ge e le m pn_tail E0 le' m' Out_normal /\
         PLS le' (i + sk) c sk /\
         (forall j, (j < 8)%nat ->
            Mem.load Mint32 m' bop (oop + 36 * n + 4 * Z.of_nat j) =
              Some (Vint (nth j (hash_buffer_regs (pn_data bs i sk)) Int.zero))) /\
         (forall ch b ofs, Mem.valid_block m b -> b <> bC -> b <> bRs ->
            (b <> bop \/ ofs + size_chunk ch <= oop + 36 * n \/ oop + 36 * n + 32 <= ofs) ->
            Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
         (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
         (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HS Hi Hs Hn HLen HBuf HobM HBs HLa HLn VA PO PC PR Hdisp HMax.
  pose proof HS as (HP & Hcd & Hk). pose proof HP as (Hli & Hr & Ha & Hal & Hsp).
  pose proof (nd_L len) as HLr. fold L in HLr.
  set (le16 := PTree.set _t'16 (Vint len) le).
  assert (K16 : pn_keeps _t'16) by pn_keeps_tac.
  assert (S16 : PLS le16 i c sk) by (apply pls_set; assumption).
  pose proof S16 as ((Hli16 & Hr16 & Ha16 & _ & Hsp16) & Hcd16 & Hk16).
  assert (HC : eval_expr sha_ge e le16 m
    (Ebinop Olt (Ebinop Osub (Etempvar _t'16 tuint) (Etempvar _i tulong) tulong) (Etempvar _skip tulong) tint)
    (Val.of_bool (L - i <? sk))).
  { eapply eval_Ebinop with (v1 := Vlong (Int64.repr (L - i))) (v2 := Vlong (Int64.repr sk)).
    - eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|apply eval_Etempvar; exact Hli16|].
      rewrite <- (nd_i64_sub L i) by zh. reflexivity.
    - apply eval_Etempvar. exact Hk16.
    - change (Some (Val.of_bool (Int64.ltu (Int64.repr (L - i)) (Int64.repr sk))) =
              Some (Val.of_bool (L - i <? sk))).
      rewrite nd_i64_ltu by zh. reflexivity. }
  assert (H1 : Clight2.exec_stmt sha_ge e le m (Sset _t'16 (Efield PSPK _len tuint)) E0 le16 m Out_normal).
  { apply exec_Sset. eapply nd_ev_len; eassumption. }
  unfold pn_tail.
  destruct (L - i <? sk) eqn:ET.
  { destruct (pn_fail_exec e br or_ len Hor le16 m Hr16 VA) as (m' & XF & HSt).
    exists le16, m'. split; [|exact HSt].
    eapply exec_Sseq_2; [|discriminate].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact H1|].
    eapply exec_Sifthenelse with (v1 := Val.of_bool true) (b := true); [exact HC|reflexivity|exact XF]. }
  apply Z.ltb_ge in ET.
  set (obase := oop + 36 * n).
  assert (Hob : 0 <= obase /\ obase + 32 <= Ptrofs.max_unsigned) by (unfold obase; zh).
  assert (HoA : (4 | obase)) by (unfold obase; destruct HoopA as [q ->]; exists (q + 9 * n); zh).
  assert (VG : Mem.valid_block m GC).
  { unfold sha_dispatch_ok in Hdisp. eapply Mem.perm_valid_block.
    apply (proj1 (Mem.load_valid_access _ _ _ _ _ Hdisp) 0). cbn. zh. }
  assert (VM : Mem.valid_block m GM).
  { eapply Mem.perm_valid_block. apply (proj1 (Mem.load_valid_access _ _ _ _ _ HMax) 0). cbn. zh. }
  assert (POb : Mem.range_perm m bop obase (obase + 32) Cur Writable).
  { intros o Ho. apply PO. unfold obase in Ho. zh. }
  destruct ctxo_init with (bx := bC) (bo := bop) (obase := obase) (m := m) (br := bRs)
    as (mi & mx & bytes & HInit & HLB & HSB & C1 & L1 & P1 & V1); try assumption.
  assert (Vsp : Mem.valid_block m bsp).
  { eapply Mem.perm_valid_block. apply (proj1 (Mem.load_valid_access _ _ _ _ _ HLen) (osp + 8)). cbn. zh. }
  assert (HL0 : 0 < L) by zh.
  assert (Vbb : Mem.valid_block m bb).
  { eapply Mem.perm_valid_block.
    apply (proj1 (Mem.load_valid_access _ _ _ _ _ (HBs 0 ltac:(zh))) (Ptrofs.unsigned ob + 0)). cbn. zh. }
  assert (HBufx : Mem.load Mptr mx bsp osp = Some (Vptr bb ob)).
  { rewrite L1 by (try exact Vsp; try assumption; left; exact Hso). exact (HBuf HL0). }
  set (data := pn_data bs i sk).
  assert (HDl : Z.of_nat (length data) = sk) by (apply pn_data_length; zh).
  set (obi := Ptrofs.add ob (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr i)))).
  assert (Hobi : Ptrofs.unsigned obi = Ptrofs.unsigned ob + i) by (apply nd_index_offset; zh).
  destruct ctxo_uchars with (bx := bC) (bo := bop) (obase := obase) (m := mx) (ba := bb) (oa := obi)
    (l := @nil int) (regs := sha256_iv_words) (bs := data) (c := Int64.zero) (ovf := false)
    as (m2 & HU & C2 & L2 & P2 & V2); try assumption.
  { rewrite Hobi, HDl. zh. }
  { intros k Hk0. rewrite Hobi. unfold data. rewrite pn_data_nth by exact Hk0.
    assert (HkR : Z.of_nat k < sk) by (fold data in Hk0; zh).
    rewrite L1 by (try exact Vbb; try assumption; left; exact Hbo).
    replace (Ptrofs.unsigned ob + i + Z.of_nat k) with (Ptrofs.unsigned ob + (i + Z.of_nat k)) by zh.
    apply HBs. zh. }
  rewrite HDl in HU.
  destruct ctxo_finalize with (bx := bC) (bo := bop) (obase := obase) (m := m2)
    (l := fst (absorb_i [] sha256_iv_words data)) (regs := snd (absorb_i [] sha256_iv_words data))
    (c := Int64.add Int64.zero (Int64.repr (Z.of_nat (length data))))
    (ovf := uc_overflow false Int64.zero (Int64.repr (Z.of_nat (length data))))
    as (m3 & HF & HR3 & L3 & P3 & V3); try assumption.
  set (pv := Vptr bop (Ptrofs.repr oop)).
  set (le14 := PTree.set _t'14 pv le16).
  set (le15 := PTree.set _t'15 (Vlong (Int64.repr n)) le14).
  set (le13 := PTree.set _t'13 (Vptr bb ob) le15).
  set (leF := PTree.set _i (Vlong (Int64.repr (i + sk))) le13).
  assert (K14 : pn_keeps _t'14) by pn_keeps_tac. assert (K15 : pn_keeps _t'15) by pn_keeps_tac.
  assert (K13 : pn_keeps _t'13) by pn_keeps_tac.
  assert (S13 : PLS le13 i c sk) by (unfold le13, le15, le14; repeat apply pls_set; assumption).
  pose proof S13 as ((Hli13 & Hr13 & Ha13 & Hal13 & Hsp13) & Hcd13 & Hk13).
  exists leF, m3. split; [|split; [|split; [|split; [|split]]]].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le16) (m1 := m).
    { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact H1|].
      eapply exec_Sifthenelse with (v1 := Val.of_bool false) (b := false); [exact HC|reflexivity|apply exec_Sskip]. }
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le13) (m1 := m3).
    + cbv delta [pn_hash] beta iota.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le15) (m1 := mx).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le15) (m1 := mi).
        - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le14) (m1 := m).
          { apply exec_Sset. exact (pn_alloc_value e ba oa len Hoa le16 m _ Ha16 HLa). }
          eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le15) (m1 := m).
          { apply exec_Sset. apply (pn_len_value e br or_ len Hor le14 m _); [|exact HLn].
            unfold le14. rewrite PTree.gso by discriminate. exact Hr16. }
          change le15 with (set_opttemp None Vundef le15) at 2.
          eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_init) Ptrofs.zero)
            (vargs := [Vptr bRs Ptrofs.zero; Vptr bop (Ptrofs.repr obase)]) (f := Internal jets.f_sha256_init).
          + reflexivity.
          + eapply eval_Elvalue; [apply eval_Evar_global; [exact Hg1|exact tap_init_symbol]|].
            apply deref_loc_reference; reflexivity.
          + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact HeR|reflexivity|].
            eapply eval_Econs with (v1 := Vptr bop (Ptrofs.repr obase));
              [apply pn_hash_out; [unfold le15; rewrite PTree.gso by discriminate; apply PTree.gss|apply PTree.gss|exact Hn]
              |reflexivity|apply eval_Enil].
          + exact tap_init_funct.
          + reflexivity.
          + exact HInit.
        - eapply (exec_ctx_struct_copy e le15 mi mx _ctx __res bC bRs bytes);
            [exact HeC|exact HeR|apply not_eq_sym; exact Hrx|exact HLB|exact HSB]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le13) (m1 := m2).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le13) (m1 := mx).
        { apply exec_Sset. eapply eval_envu_field_value;
            [reflexivity|exact envu_rawElementsBuffer_buf|reflexivity|apply eval_envu_deref_struct|].
          - unfold le15, le14. rewrite !PTree.gso by discriminate. exact Hsp16.
          - rewrite envu_ptr_add_repr by zh. apply envu_loadv_repr; [zh|]. rewrite Z.add_0_r. exact HBufx. }
        match type of HU with Clight2.eval_funcall _ _ _ _ _ _ ?vr =>
          change le13 with (set_opttemp None vr le13) at 2 end.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero)
          (vargs := [Vptr bC (Ptrofs.repr 0); Vptr bb obi; Vlong (Int64.repr sk)]) (f := Internal f_sha256_uchars).
        -- reflexivity.
        -- eapply eval_Elvalue; [apply eval_Evar_global; [exact Hg3|exact sha_uchars_symbol]|].
           apply deref_loc_reference; reflexivity.
        -- eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact HeC|reflexivity|].
           eapply eval_Econs.
           ++ eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|apply eval_Etempvar; exact Hli13|reflexivity].
           ++ reflexivity.
           ++ eapply eval_Econs; [apply eval_Etempvar; exact Hk13|reflexivity|apply eval_Enil].
        -- exact sha_uchars_funct.
        -- reflexivity.
        -- exact HU.
      * eapply mt_call_finalize; [exact Hg5|exact HeC|exact HF].
    + apply exec_Sset.
      eapply eval_Ebinop; [apply eval_Etempvar; exact Hli13|apply eval_Etempvar; exact Hk13|].
      rewrite <- (nd_i64_add i sk) by zh. reflexivity.
  - destruct S13 as ((A1 & A2 & A3 & A4 & A5) & A6 & A7). unfold PLS, pls, pl, leF.
    rewrite PTree.gss. rewrite !(PTree.gso _ _ (j := _i)) by discriminate. repeat split; assumption.
  - intros j Hj. fold obase. rewrite (HR3 j Hj). do 2 f_equal.
    unfold hash_buffer_regs. fold data. rewrite Int64.add_zero_l. reflexivity.
  - intros ch b ofs Hb NbC NbR Ho. fold obase in Ho.
    rewrite L3 by (try (apply V2, V1; exact Hb); assumption).
    rewrite L2 by (try (apply V1; exact Hb); assumption).
    apply L1; assumption.
  - intros b ofs k p Hb Hp. apply P3; [apply V2, V1, Hb|]. apply P2; [apply V1, Hb|]. apply P1, Hp.
  - intros b Hb. apply V3, V2, V1, Hb.
Qed.
End ParseHash.
