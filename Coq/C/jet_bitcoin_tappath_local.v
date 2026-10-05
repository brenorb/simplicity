(** Actual Bitcoin tappath jet against the extended primitive Tappath.
    C: [i = simplicity_read8(&src);
        if (writeBit(dst, i < env->taproot->pathLen)) writeHash(dst, &env->taproot->path[i]);
        else skipBits(dst, 256);  return true;] *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_input_layout C.jet_output_layout_step.
Require Import C.jet_read8_input_word_total C.jet_uint32_array_init C.jet_word_repr.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec C.jet_exec.
Require C.jets.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_steps.
Require Import C.jet_bitcoin_indexed_exec C.jet_bitcoin_env_load C.jet_bitcoin_indexed_scalar C.jet_bitcoin_indexed_ptr.
Require Import C.jet_bitcoin_hash_write C.jet_bitcoin_hash_getters C.jet_bitcoin_script_cmr_local.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_ext_ptr_jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Import PrimitiveBitcoinExt.Primitive.Coercions.
Import PrimitiveBitcoinExt.Primitive.CanonicalStructures.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge ge0.
Set Default Timeout 120.

(** [simplicity_read8(&src)] on the local by-value copy of the source frame. *)
Lemma bitcoin_read8_step m ma mc bl bs sbase bi edge rc (x : Ty.tySem (Word 3)) bytes :
  0 <= rc <= Int64.max_unsigned - 8 ->
  frame_fields_at m bs sbase bi edge rc ->
  frame_input_word_at m bi edge rc x ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  exists mr,
    Clight2.eval_funcall bitcoin_ge mc (Internal jets.f_simplicity_read8) [Vptr bl (Ptrofs.repr 0)] E0 mr
      (Vint (Int.repr (@toZ (WordToZ 3) x))) /\
    (forall chunk b ofs, b <> bl -> Mem.load chunk mr b ofs = Mem.load chunk mc b ofs) /\
    (forall b ofs kind p, Mem.perm mc b ofs kind p -> Mem.perm mr b ofs kind p) /\
    (forall b, Mem.valid_block mc b -> Mem.valid_block mr b) /\
    (forall chunk b ofs v, Mem.load chunk m b ofs = Some v -> Mem.load chunk mr b ofs = Some v).
Proof.
  intros HRC HF HIn HA HB SC.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  destruct HF as [HSE HSO].
  destruct (read8_input_loads m bi edge rc x HRC HIn) as [_ [high [low [HH _]]]].
  assert (HLi : bl <> bi) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLs : bl <> bs) by (eapply fresh_frame_not_loaded; eauto).
  assert (HSEa : Mem.load Mptr ma bs sbase = Some (Vptr bi (Ptrofs.repr edge)))
    by (eapply Mem.load_alloc_other; eauto).
  assert (HSOa : Mem.load Mint64 ma bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (eapply Mem.load_alloc_other; eauto).
  destruct (frame_copy_fields_at ma mc bs sbase bl bytes _ _ HB SC HSEa HSOa) as [HLE HLO].
  assert (HBefore : forall chunk b ofs v, Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v).
  { intros chunk b ofs v HL.
    assert (Hbl : bl <> b) by (eapply fresh_frame_not_loaded; eauto).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (HInputC : frame_input_word_at mc bi edge rc x).
  { eapply frame_input_bits_at_preserved; [|exact HIn].
    intros ofs w' HL. apply HBefore; exact HL. }
  assert (PLC : Mem.valid_access mc Mint64 bl 8 Writable).
  { eapply Mem.storebytes_valid_access_1; [exact SC|].
    eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|].
    exists 1; reflexivity. }
  destruct (eval_read8_word_at mc bl 0 bi edge rc x HLocalBase HRC (conj HLE HLO) HInputC PLC HLi)
    as (mr & Hread & HFields & HMem & HPerm & HValid).
  exists mr. split.
  - eapply bitcoin_transport_call; [|exact Hread]. unfold bitcoin_core_helpers. simpl. tauto.
  - split.
    + intros chunk b ofs Hb. apply HMem. left; exact Hb.
    + split; [exact HPerm|]. split; [exact HValid|].
      intros chunk b ofs v HL. rewrite HMem by (left; intro Heq; subst; eapply fresh_frame_not_loaded; eauto).
      apply HBefore; exact HL.
Qed.

Definition bitcoin_env_taproot_expr : expr :=
  Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
    _taproot (tptr (Tstruct _bitcoinTapEnv noattr)).

Definition tappath_head : statement :=
  Ssequence
    (Scall (Some _t'1)
      (Evar _simplicity_read8 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tuchar cc_default))
      [Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))])
    (Sset _i (Ecast (Etempvar _t'1 tuchar) tuchar)).

Definition tappath_cond : statement :=
  Ssequence (Sset _t'5 bitcoin_env_taproot_expr)
    (Ssequence
      (Sset _t'6 (Efield (Ederef (Etempvar _t'5 (tptr (Tstruct _bitcoinTapEnv noattr)))
        (Tstruct _bitcoinTapEnv noattr)) _pathLen tuchar))
      (Scall (Some _t'2)
        (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
        [Etempvar _dst (tptr (Tstruct _frameItem noattr));
         Ebinop Olt (Etempvar _i tuchar) (Etempvar _t'6 tuchar) tint])).

Definition tappath_then : statement :=
  Ssequence (Sset _t'3 bitcoin_env_taproot_expr)
    (Ssequence
      (Sset _t'4 (Efield (Ederef (Etempvar _t'3 (tptr (Tstruct _bitcoinTapEnv noattr)))
        (Tstruct _bitcoinTapEnv noattr)) _path (tptr (Tstruct _sha256_midstate noattr))))
      (Scall None
        (Evar _writeHash (Tfunction
          (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr (Tstruct _sha256_midstate noattr)) Tnil))
          tvoid cc_default))
        [Etempvar _dst (tptr (Tstruct _frameItem noattr));
         Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sha256_midstate noattr))) (Etempvar _i tuchar)
           (tptr (Tstruct _sha256_midstate noattr))])).

Definition tappath_rest : statement :=
  Ssequence tappath_head
    (Ssequence
      (Ssequence tappath_cond (Sifthenelse (Etempvar _t'2 tbool) tappath_then (bitcoin_skip_stmt 256)))
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))).

Lemma bitcoin_tappath_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_tappath tappath_rest.
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma bitcoin_tapEnv_path : bitcoin_field_at _bitcoinTapEnv _path 0.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_tapEnv_pathLen : bitcoin_field_at _bitcoinTapEnv _pathLen 168.
Proof. vm_compute; reflexivity. Qed.

Lemma eval_bitcoin_env_taproot e le m be ebase bt tbase :
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> 0 <= ebase -> ebase + 16 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) ->
  eval_expr bitcoin_ge e le m bitcoin_env_taproot_expr (Vptr bt (Ptrofs.repr tbase)).
Proof.
  intros HE H0 HM HL. unfold bitcoin_env_taproot_expr.
  eapply eval_bitcoin_field_value with (sid := _txEnv) (delta := 8) (chunk := Mptr).
  - reflexivity.
  - exact bitcoin_txEnv_taproot.
  - reflexivity.
  - apply eval_bitcoin_deref_struct; exact HE.
  - rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HL].
Qed.

Definition tappath_cells (path : list hash256) (a : Ty.tySem (Word 3)) : list Cell :=
  match nth_error path (Z.to_nat (@toZ (WordToZ 3) a)) with
  | Some h => Some true :: hash_cells (hash256_reg h)
  | None => Some false :: repeat None 256
  end.

Definition bitcoin_tappath_env_rep (m : mem) (env : val) (e : ext_environment)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt tbase bp pbase,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= tbase /\ tbase + 176 <= Ptrofs.max_unsigned /\
    0 <= pbase /\ pbase + 32 * Z.of_nat (length (extTappath e)) <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) /\
    Mem.load Mptr m bt (tbase + 0) = Some (Vptr bp (Ptrofs.repr pbase)) /\
    Mem.load Mint8unsigned m bt (tbase + 168) =
      Some (Vint (Int.repr (Z.of_nat (length (extTappath e))))) /\
    (forall j h, nth_error (extTappath e) j = Some h ->
      hash_elem_rep m bp (pbase + 32 * Z.of_nat j) h) /\
    fp = [(be, ebase + 8, ebase + 16); (bt, tbase + 0, tbase + 8);
          (bp, pbase, pbase + 32 * Z.of_nat (length (extTappath e)))].

Definition bitcoin_tappath_spec {alg : PrimitiveBitcoinExt.Primitive.Algebra} :
    alg Word8 (Ty.Sum Ty.Unit Word256) :=
  PrimitiveBitcoinExt.Primitive.Combinators.prim BitcoinExt.Tappath.

Definition bitcoin_tappath_result (path : list hash256) (a : Ty.tySem Word8) :
    Ty.tySem (Ty.Sum Ty.Unit Word256) :=
  match nth_error path (Z.to_nat (toZ a)) with
  | Some h => inr (from_hash256 h)
  | None => inl tt
  end.

Lemma bitcoin_tappath_sem environment a :
  @bitcoin_tappath_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    a environment = Some (bitcoin_tappath_result (extTappath environment) a).
Proof.
  unfold bitcoin_tappath_result.
  assert (H : @bitcoin_tappath_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    a environment = BitcoinExt.sem BitcoinExt.Tappath a environment) by reflexivity.
  rewrite H. unfold BitcoinExt.sem. cbv zeta.
  destruct (nth_error (extTappath environment) (Z.to_nat (toZ a))); reflexivity.
Qed.

Lemma tappath_index_ptr pbase z :
  0 <= pbase -> 0 <= z < 256 -> pbase + 32 * z + 32 <= Ptrofs.max_unsigned ->
  Ptrofs.add (Ptrofs.repr pbase)
    (Ptrofs.mul (Ptrofs.repr 32) (Ptrofs.of_ints (Int.repr z))) = Ptrofs.repr (pbase + 32 * z).
Proof.
  intros Hp Hz HM.
  unfold Ptrofs.add, Ptrofs.mul, Ptrofs.of_ints.
  rewrite Int.signed_repr by
    (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
  rewrite (Ptrofs.unsigned_repr z) by lia.
  rewrite (Ptrofs.unsigned_repr 32) by lia.
  rewrite (Ptrofs.unsigned_repr (32 * z)) by lia.
  rewrite (Ptrofs.unsigned_repr pbase) by lia.
  reflexivity.
Qed.

Lemma sem_add_ptr_uchar_sizeof ce S i ofs b sz m :
  sizeof ce S = sz ->
  sem_add ce (Vptr b ofs) (tptr S) (Vint i) tuchar m =
    Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_ints i)))).
Proof. intros H. unfold sem_add. simpl. unfold sem_add_ptr_int. rewrite H. reflexivity. Qed.

Lemma bitcoin_sizeof_midstate :
  sizeof (Clight.genv_cenv bitcoin_ge) (Tstruct _sha256_midstate noattr) = 32.
Proof. vm_compute; reflexivity. Qed.

Lemma zero_ext8_small z : 0 <= z < 256 -> Int.zero_ext 8 (Int.repr z) = Int.repr z.
Proof.
  intro Hz. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr z))).
  rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia).
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  change (two_p 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma tappath_lt_small a n : 0 <= a < 256 -> 0 <= n < 256 ->
  Int.lt (Int.repr a) (Int.repr n) = (a <? n).
Proof.
  intros Ha Hn. unfold Int.lt.
  rewrite !Int.signed_repr by
    (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
  destruct (zlt a n); symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; lia.
Qed.

Theorem bitcoin_tappath_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tappath bitcoin_ge ext_environment Word8
    (Ty.Sum Ty.Unit Word256) bitcoin_tappath_env_rep
    (fun a environment => @bitcoin_tappath_spec
      (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor a fp
    (be & ebase & bt & tbase & bp & pbase & HEnvVal & He0 & He1 & Ht0 & Ht1 & Hp0 & Hp1 &
      HLtap & HLpath & HLlen & HLelem & HFp)
    HSep HBf HA [HSedge HSoff] HR0 HRmax Hin HFrame.
  subst env fp.
  set (path := extTappath environment) in *.
  set (nn := Z.of_nat (length path)) in *.
  pose proof (extTappath_len environment) as HPL. fold path in HPL.
  assert (Hnn : 0 <= nn <= 128) by (subst nn; lia).
  assert (HB : Z.of_nat (bitSize (Ty.Sum Ty.Unit Word256)) = 257) by reflexivity.
  rewrite HB in HSep, HFrame.
  change (Z.of_nat (bitSize Word8)) with 8 in HRmax.
  rewrite Forall_forall in HSep.
  assert (S1 : out_sep bd dbase bw outedge cursor 257 be (ebase + 8) (ebase + 16))
    by exact (HSep (be, ebase + 8, ebase + 16) ltac:(simpl; auto)).
  assert (S4 : out_sep bd dbase bw outedge cursor 257 bt (tbase + 0) (tbase + 8))
    by exact (HSep (bt, tbase + 0, tbase + 8) ltac:(simpl; auto)).
  assert (S5 : out_sep bd dbase bw outedge cursor 257 bp pbase (pbase + 32 * nn))
    by exact (HSep (bp, pbase, pbase + 32 * nn) ltac:(simpl; auto)).
  apply frame_input_word_at_encode in Hin.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (az := @toZ (WordToZ 3) a).
  assert (Haz : 0 <= az < 256) by (unfold az; exact (word_toZ_range 3 a)).
  set (iv := Int.repr az).
  set (b := az <? nn).
  set (V := tappath_cells path a).
  assert (HMid : bitcoin_wrapper_mid f_simplicity_bitcoin_tappath tappath_rest V
    (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 257 bytes).
  { unfold bitcoin_wrapper_mid. intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    assert (HBa : Mem.loadbytes ma bs sbase 16 = Some bytes).
    { erewrite Mem.loadbytes_alloc_unchanged; eauto.
      eapply Mem.perm_valid_block. eapply (Mem.loadbytes_range_perm _ _ _ _ _ HBytes sbase); lia. }
    destruct (bitcoin_read8_step m ma mc bl bs sbase bi edge read_cursor a bytes ltac:(lia)
      (conj HSedge HSoff) Hin HAlloc HBa HStore)
      as (mr & Hread & HRMem & HRPerm & HRValid & HRLoads).
    fold az in Hread. fold iv in Hread.
    pose proof HFrame as [HDB [[HDE HDO] [HEd [HN [HMx [HDW [PD HWords]]]]]]].
    destruct (write_frame_at_head m bd dbase bw outedge cursor 257 ltac:(lia) HFrame)
      as [_ [_ [_ [w0 Hw0]]]].
    assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
    assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
    assert (HFrameR : write_frame_at mr bd dbase bw outedge cursor 257).
    { eapply write_frame_at_preserved with (m := mc).
      - intros chunk b0 ofs v Hb HL. rewrite HRMem; [exact HL|].
        destruct Hb; subst; auto.
      - exact HRPerm.
      - exact HFrameC. }
    assert (HE0 : Mem.load Mptr mr be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)))
      by (apply HRLoads; exact HLtap).
    assert (HE1 : Mem.load Mptr mr bt (tbase + 0) = Some (Vptr bp (Ptrofs.repr pbase)))
      by (apply HRLoads; exact HLpath).
    assert (HE2 : Mem.load Mint8unsigned mr bt (tbase + 168) = Some (Vint (Int.repr nn)))
      by (apply HRLoads; exact HLlen).
    assert (HF1 : write_frame_at mr bd dbase bw outedge cursor 1).
    { eapply write_frame_at_shorter; [|exact HFrameR]. lia. }
    destruct (bitcoin_writeBit_step mr bd dbase bw outedge cursor b HF1) as (mb & Hwb1 & E1).
    assert (HFb : write_frame_at mb bd dbase bw outedge (cursor - 1) 256).
    { eapply write_frame_at_after_effect with (cells := [Some b]);
        [reflexivity|lia|exact HFrameR|exact E1]. }
    assert (HLoadB : forall chunk b0 lo hi ofs, out_sep bd dbase bw outedge cursor 257 b0 lo hi ->
      lo <= ofs -> ofs + size_chunk chunk <= hi -> Mem.load chunk mb b0 ofs = Mem.load chunk mr b0 ofs).
    { intros chunk b0 lo hi ofs Hs Hlo Hhi.
      eapply write_effect_env_load with (bf := bd) (base := dbase) (bw := bw) (edge := outedge)
        (cursor := cursor) (cursor0 := cursor) (count0 := 257) (n := 1)
        (cells := [Some b]) (lo := lo) (hi := hi);
        [lia|lia|lia|lia|exact E1|exact Hs|exact Hlo|exact Hhi]. }
    set (le0 := bitcoin_wrapper_temps f_simplicity_bitcoin_tappath (Vptr be (Ptrofs.repr ebase))
      bd dbase bs sbase).
    assert (HEnv0 : le0!_env = Some (Vptr be (Ptrofs.repr ebase)))
      by (unfold le0, bitcoin_wrapper_temps; apply PTree.gss).
    assert (HDst0 : le0!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { unfold le0, bitcoin_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss. }
    set (l1 := PTree.set _i (Vint iv) (PTree.set _t'1 (Vint iv) le0)).
    set (l2 := PTree.set _t'5 (Vptr bt (Ptrofs.repr tbase)) l1).
    set (l3 := PTree.set _t'6 (Vint (Int.repr nn)) l2).
    set (l4 := PTree.set _t'2 (Vint (if b then Int.one else Int.zero)) l3).
    assert (Hi4 : l4!_i = Some (Vint iv)).
    { unfold l4, l3, l2, l1. repeat rewrite PTree.gso by discriminate. apply PTree.gss. }
    assert (Hd4 : l4!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { unfold l4, l3, l2, l1. repeat rewrite PTree.gso by discriminate. exact HDst0. }
    assert (He4 : l4!_env = Some (Vptr be (Ptrofs.repr ebase))).
    { unfold l4, l3, l2, l1. repeat rewrite PTree.gso by discriminate. exact HEnv0. }
    assert (HHead : Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl) le0 mc tappath_head E0 l1 mr
      Out_normal).
    { unfold tappath_head.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := PTree.set _t'1 (Vint iv) le0).
      - change (PTree.set _t'1 (Vint iv) le0) with (set_opttemp (Some _t'1) (Vint iv) le0).
        eapply exec_bitcoin_helper_call with (id := _simplicity_read8) (f := jets.f_simplicity_read8)
          (vargs := [Vptr bl Ptrofs.zero]) (vres := Vint iv).
        + unfold bitcoin_core_helpers. simpl. tauto.
        + reflexivity.
        + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
        + reflexivity.
        + exact Hread.
      - apply exec_set. eapply eval_Ecast; [apply eval_Etempvar; apply PTree.gss|].
        change (Some (Vint (Int.zero_ext 8 iv)) = Some (Vint iv)).
        unfold iv. rewrite zero_ext8_small by lia. reflexivity. }
    assert (Hcmp : Int.lt iv (Int.repr nn) = b).
    { unfold iv, b. apply tappath_lt_small; lia. }
    assert (HCond : Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl) l1 mr tappath_cond E0 l4 mb
      Out_normal).
    { unfold tappath_cond.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l2).
      - apply exec_set. eapply eval_bitcoin_env_taproot; [|exact He0|lia|exact HE0].
        unfold l1. repeat rewrite PTree.gso by discriminate. exact HEnv0.
      - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l3).
        + apply exec_set.
          eapply eval_bitcoin_field_value with (sid := _bitcoinTapEnv) (delta := 168) (chunk := Mint8unsigned).
          * reflexivity.
          * exact bitcoin_tapEnv_pathLen.
          * reflexivity.
          * apply eval_bitcoin_deref_struct. unfold l2. apply PTree.gss.
          * rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HE2].
        + change l4 with (set_opttemp (Some _t'2) (Vint (if b then Int.one else Int.zero)) l3).
          eapply exec_bitcoin_helper_call with (id := _writeBit) (f := jets.f_writeBit)
            (vargs := [Vptr bd (Ptrofs.repr dbase); Vint (if b then Int.one else Int.zero)])
            (vres := Vint (if b then Int.one else Int.zero)).
          * unfold bitcoin_core_helpers. simpl. tauto.
          * reflexivity.
          * eapply eval_Econs.
            -- apply eval_Etempvar. unfold l3, l2, l1. repeat rewrite PTree.gso by discriminate. exact HDst0.
            -- reflexivity.
            -- eapply eval_Econs with (v1 := Val.of_bool b).
               ++ eapply eval_Ebinop with (v1 := Vint iv) (v2 := Vint (Int.repr nn)).
                  ** apply eval_Etempvar. unfold l3, l2. repeat rewrite PTree.gso by discriminate.
                     unfold l1. apply PTree.gss.
                  ** apply eval_Etempvar. unfold l3. apply PTree.gss.
                  ** change (Some (Val.of_bool (Int.lt iv (Int.repr nn))) = Some (Val.of_bool b)).
                     rewrite Hcmp. reflexivity.
               ++ apply bitcoin_bool_cast.
               ++ apply eval_Enil.
          * reflexivity.
          * exact Hwb1. }
    assert (HBranch : exists le'' me,
      Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl) l4 mb
        (if b then tappath_then else bitcoin_skip_stmt 256) E0 le'' me Out_normal /\
      write_effect mr me bd dbase bw outedge cursor 257 V).
    { destruct b eqn:Hb.
      - (* in range *)
        assert (Hlt : az < nn) by (apply Z.ltb_lt; exact Hb).
        destruct (nth_error path (Z.to_nat az)) as [h|] eqn:Hnth;
          [|apply nth_error_None in Hnth; subst nn; lia].
        set (ofs := pbase + 32 * az).
        assert (Hrep : hash_elem_rep m bp ofs h).
        { pose proof (HLelem _ _ Hnth) as H. rewrite Z2Nat.id in H by lia. exact H. }
        assert (Hrepb : hash_elem_rep mb bp ofs h).
        { eapply hash_elem_rep_mono; [exact Hrep|].
          intros chunk o v Hlo Hhi Hl.
          rewrite (HLoadB chunk bp pbase (pbase + 32 * nn) o S5 ltac:(unfold ofs in Hlo; lia)
            ltac:(unfold ofs in Hhi; lia)).
          apply HRLoads. exact Hl. }
        assert (Hmb0 : Mem.load Mptr mb be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase))).
        { rewrite (HLoadB Mptr be (ebase + 8) (ebase + 16) (ebase + 8) S1 ltac:(lia)
            ltac:(change (size_chunk Mptr) with 8; lia)). exact HE0. }
        assert (Hmb1 : Mem.load Mptr mb bt (tbase + 0) = Some (Vptr bp (Ptrofs.repr pbase))).
        { rewrite (HLoadB Mptr bt (tbase + 0) (tbase + 8) (tbase + 0) S4 ltac:(lia)
            ltac:(change (size_chunk Mptr) with 8; lia)). exact HE1. }
        assert (HSp : out_sep bd dbase bw outedge (cursor - 1) 256 bp ofs (ofs + 32)).
        { eapply out_sep_range with (lo := pbase) (hi := pbase + 32 * nn);
            [|unfold ofs; lia|unfold ofs; lia].
          eapply out_sep_sub with (cursor := cursor) (count := 257); [lia|lia|lia|lia|exact S5]. }
        destruct (hash_elem_pay bd dbase bw outedge mb bp ofs h (cursor - 1) Hrepb
          ltac:(unfold ofs; lia) ltac:(unfold ofs; lia) HSp HFb) as (me & HCallP & E2).
        set (la := PTree.set _t'3 (Vptr bt (Ptrofs.repr tbase)) l4).
        set (lb := PTree.set _t'4 (Vptr bp (Ptrofs.repr pbase)) la).
        exists lb, me. split.
        + unfold tappath_then.
          eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := la).
          * apply exec_set. eapply eval_bitcoin_env_taproot; [exact He4|exact He0|lia|exact Hmb0].
          * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := lb).
            -- apply exec_set.
               eapply eval_bitcoin_field_value with (sid := _bitcoinTapEnv) (delta := 0) (chunk := Mptr).
               ++ reflexivity.
               ++ exact bitcoin_tapEnv_path.
               ++ reflexivity.
               ++ apply eval_bitcoin_deref_struct. unfold la. apply PTree.gss.
               ++ rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact Hmb1].
            -- eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block _writeHash) Ptrofs.zero)
                 (f := Internal f_writeHash)
                 (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bp (Ptrofs.repr ofs)]) (vres := Vundef).
               ++ reflexivity.
               ++ eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact bitcoin_writeHash_symbol]|
                    apply deref_loc_reference; reflexivity].
               ++ eapply eval_Econs.
                  ** apply eval_Etempvar. unfold lb, la. repeat rewrite PTree.gso by discriminate. exact Hd4.
                  ** reflexivity.
                  ** eapply eval_Econs with (v1 := Vptr bp (Ptrofs.repr ofs)).
                     --- eapply eval_Ebinop with (v1 := Vptr bp (Ptrofs.repr pbase)) (v2 := Vint iv).
                         +++ apply eval_Etempvar. unfold lb. apply PTree.gss.
                         +++ apply eval_Etempvar. unfold lb, la. repeat rewrite PTree.gso by discriminate.
                             exact Hi4.
                         +++ unfold ofs, iv. rewrite <- (tappath_index_ptr pbase az Hp0 Haz ltac:(lia)).
                             cbn [typeof]. unfold sem_binary_operation.
                             exact (sem_add_ptr_uchar_sizeof (Clight.genv_cenv bitcoin_ge)
                               (Tstruct _sha256_midstate noattr) (Int.repr az) (Ptrofs.repr pbase) bp 32 mb
                               bitcoin_sizeof_midstate).
                     --- reflexivity.
                     --- apply eval_Enil.
               ++ exact bitcoin_writeHash_funct.
               ++ reflexivity.
               ++ exact HCallP.
        + pose proof (write_effect_seq mr mb me bd dbase bw outedge cursor 1 256 [Some true]
            (hash_cells (hash256_reg h)) eq_refl ltac:(lia) HFrameR E1 E2) as Eseq.
          assert (Hcells : [Some true] ++ hash_cells (hash256_reg h) = V).
          { unfold V, tappath_cells. fold az. rewrite Hnth. reflexivity. }
          exact (eq_rect _ (fun c => write_effect mr me bd dbase bw outedge cursor 257 c) Eseq _ Hcells).
      - (* out of range *)
        assert (Hge : nn <= az) by (apply Z.ltb_ge; exact Hb).
        assert (Hnth : nth_error path (Z.to_nat az) = None).
        { apply nth_error_None. subst nn. lia. }
        destruct (bitcoin_skipBits_step mb bd dbase bw outedge (cursor - 1) 256%nat HFb)
          as (me & HCallS & E2).
        exists l4, me. split.
        + unfold bitcoin_skip_stmt.
          assert (Hargs : eval_exprlist bitcoin_ge (bitcoin_version_locals bl) l4 mb
            [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 256) tint]
            (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
            [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr (Z.of_nat 256))]).
          { eapply eval_Econs; [apply eval_Etempvar; exact Hd4|reflexivity|].
            eapply eval_Econs; [apply eval_Econst_int| |apply eval_Enil].
            apply bitcoin_cast_const'; lia. }
          exact (exec_bitcoin_helper_call (bitcoin_version_locals bl) l4 mb None _skipBits jets.f_skipBits
            _ _ _ _ _ _ me ltac:(unfold bitcoin_core_helpers; simpl; tauto) ltac:(reflexivity) Hargs
            ltac:(reflexivity) HCallS).
        + pose proof (write_effect_seq mr mb me bd dbase bw outedge cursor 1 256 [Some false]
            (repeat None 256) eq_refl ltac:(lia) HFrameR E1 E2) as Eseq.
          assert (Hcells : [Some false] ++ repeat None 256 = V).
          { unfold V, tappath_cells. fold az. rewrite Hnth. reflexivity. }
          exact (eq_rect _ (fun c => write_effect mr me bd dbase bw outedge cursor 257 c) Eseq _ Hcells). }
    destruct HBranch as (lef & me & HBr & HEff).
    destruct (write_effect_lift mc mr me bl bd dbase bw outedge cursor 257 V HLd HLw
      HRMem HRPerm HRValid HEff) as (c & p & fl & l & pm & vv).
    exists lef, me. refine (conj _ (conj c (conj p (conj fl (conj l (conj pm vv)))))).
    unfold tappath_rest.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l1); [exact HHead|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := lef);
      [|apply exec_Sreturn_some, eval_Econst_int].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := l4); [exact HCond|].
    eapply exec_Sifthenelse with (v1 := Vint (if b then Int.one else Int.zero)) (b := b).
    - apply eval_Etempvar. unfold l4. apply PTree.gss.
    - destruct b; reflexivity.
    - exact HBr. }
  destruct (bitcoin_wrapper_layout f_simplicity_bitcoin_tappath tappath_rest V
    (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 257 bytes
    bitcoin_tappath_shape HBf HA HBytes ltac:(lia) HFrame HMid)
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (bitcoin_tappath_result path a). split; [apply bitcoin_tappath_sem|].
  split; [exact HCall|]. split.
  - unfold V, tappath_cells in HCells. unfold bitcoin_tappath_result.
    change (@toZ (WordToZ 3) a) with (toZ a) in HCells.
    destruct (nth_error path (Z.to_nat (toZ a))) as [h|].
    + rewrite encode_sum_inr_hash', encode_from_hash256. exact HCells.
    + exact HCells.
  - split; [exact HPrefix|]. rewrite HB. split; [exact HFields|]. exact HMem.
Qed.
