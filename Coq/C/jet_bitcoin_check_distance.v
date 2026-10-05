(** Actual Bitcoin check_lock_distance / check_lock_duration jets against the
    literal canonical TimeLock programs
      [assert (iden &&& (unit >>> txLockDistance) >>> le word16)].
    C: [if (env->tx->numInputs <= env->ix) return false;
        x = simplicity_read16(&src); return x <= lockDistance(env->tx, env->ix);] *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_exec C.jet_application_partial C.jet_partial C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout C.jet_spec C.jet_encoding.
Require Import C.jet_wide C.jet_wide_spec C.jet_word_repr C.jet_order_spec C.jet_frame_spec.
Require Import C.jet_complement_wide_layout C.jet_parse_sequence_spec C.jet_frame_copy.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_wrapper C.jet_bitcoin_bool_wrapper.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_read_step.
Require Import C.jet_bitcoin_current_exec C.jet_bitcoin_current_spec.
Require Import C.jet_bitcoin_distance_exec C.jet_bitcoin_distance_spec C.jet_bitcoin_distance_local.
Require Import C.jet_bitcoin_check_lock.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Definition bitcoin_check_distance_program (dist : bool) {alg : Primitive.Algebra} :
    alg (Word 4) Ty.Unit :=
  bitcoin_assert_spec
    (bitcoin_comp
      (bitcoin_pair (bitcoin_core (fun alg => @DC.iden (Word 4) alg))
        (bitcoin_comp (bitcoin_core (fun alg => @DC.unit (Word 4) alg))
          (bitcoin_lock_distance_program dist)))
      (bitcoin_core (fun alg => @le_word_spec alg 4))).

Definition bitcoin_check_lock_distance_spec {alg : Primitive.Algebra} : alg (Word 4) Ty.Unit :=
  bitcoin_check_distance_program true.
Definition bitcoin_check_lock_duration_spec {alg : Primitive.Algebra} : alg (Word 4) Ty.Unit :=
  bitcoin_check_distance_program false.

Lemma bitcoin_check_distance_program_value dist (x : Ty.tySem (Word 4)) (environment : Bitcoin.env) :
  exists txi, nth_error (sigTxIn (Bitcoin.envTx environment)) (Bitcoin.envIx environment) = Some txi /\
    @bitcoin_check_distance_program dist (PrimitivePrimSem option_Monad_Zero) x environment =
      if @toZ (WordToZ 4) x <=?
         dist_value dist (2 <=? Int.unsigned (sigTxVersion (Bitcoin.envTx environment)))
           (Int.unsigned (sigTxiSequence txi)) mod 65536
      then Some tt else None.
Proof.
  destruct (bitcoin_lock_distance_program_value dist environment) as (txi & Hnth & Hval).
  exists txi. split; [exact Hnth|].
  set (D := dist_value dist (2 <=? Int.unsigned (sigTxVersion (Bitcoin.envTx environment)))
    (Int.unsigned (sigTxiSequence txi))) in *.
  unfold bitcoin_check_distance_program.
  rewrite bitcoin_assert_sem, bitcoin_comp_sem, bitcoin_pair_sem.
  rewrite (bitcoin_core_sem (fun alg => @DC.iden (Word 4) alg))
    by (intros alg1 alg2 R; apply Alg.iden_Parametric).
  rewrite bitcoin_comp_sem.
  rewrite (bitcoin_core_sem (fun alg => @DC.unit (Word 4) alg))
    by (intros alg1 alg2 R; apply Alg.unit_Parametric).
  assert (HL : @bitcoin_lock_distance_program dist (PrimitivePrimSem option_Monad_Zero)
      (@DC.unit (Word 4) Alg.CoreFunSem x) environment = Some (@fromZ (WordToZ 4) D)) by exact Hval.
  rewrite HL.
  rewrite (bitcoin_core_sem (fun alg => @le_word_spec alg 4) (le_word_spec_parametric 4)).
  pose proof (le_word_spec_numeric 4 (@DC.iden (Word 4) Alg.CoreFunSem x) (@fromZ (WordToZ 4) D)) as Hle.
  rewrite to_fromZ, two_power_nat_equiv, word_bitSize in Hle.
  change (2 ^ Z.of_nat (Nat.pow 2 4)) with 65536 in Hle.
  change (@toZ (WordToZ 4) (@DC.iden (Word 4) Alg.CoreFunSem x)) with (@toZ (WordToZ 4) x) in Hle.
  rewrite <- Hle.
  apply bit_match_toBool.
Qed.

Definition bitcoin_check_distance_rest (fid : ident) : statement :=
  Ssequence
    (Ssequence (Sset _t'5 bitcoin_env_tx_expr)
      (Ssequence
        (Sset _t'6 (Efield (Ederef (Etempvar _t'5 (tptr (Tstruct _bitcoinTransaction noattr)))
          (Tstruct _bitcoinTransaction noattr)) _numInputs tulong))
        (Ssequence (Sset _t'7 bitcoin_env_ix_expr)
          (Sifthenelse (Ebinop Ole (Etempvar _t'6 tulong) (Etempvar _t'7 tulong) tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip))))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _simplicity_read16 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tulong cc_default))
          [Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))])
        (Sset _x (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence (Sset _t'3 bitcoin_env_tx_expr)
          (Ssequence (Sset _t'4 bitcoin_env_ix_expr)
            (Scall (Some _t'2) (Evar fid dist_fn_type)
              [Etempvar _t'3 (tptr (Tstruct _bitcoinTransaction noattr)); Etempvar _t'4 tulong])))
        (Sreturn (Some (Ebinop Ole (Etempvar _x tulong) (Etempvar _t'2 tulong) tint))))).

Lemma exec_bitcoin_check_distance_rest fid f bl le mc mr be ebase bt tbase (nI ixv xr r : int64) :
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) fid = Some (bitcoin_symbol_block fid) ->
  Genv.find_funct (Clight.genv_genv bitcoin_ge) (Vptr (bitcoin_symbol_block fid) Ptrofs.zero) =
    Some (Internal f) ->
  type_of_fundef (Internal f) = dist_fn_type ->
  (bitcoin_version_locals bl)!fid = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
  0 <= ebase -> ebase + 56 <= Ptrofs.max_unsigned ->
  0 <= tbase -> tbase + 488 <= Ptrofs.max_unsigned ->
  Mem.load Mptr mc be (ebase + 0) = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Mem.load Mint64 mc bt (tbase + 448) = Some (Vlong nI) ->
  Mem.load Mint64 mc be (ebase + 48) = Some (Vlong ixv) ->
  Int64.ltu ixv nI = true ->
  Clight2.eval_funcall bitcoin_ge mc (Internal jets.f_simplicity_read16)
    [Vptr bl (Ptrofs.repr 0)] E0 mr (Vlong xr) ->
  Mem.load Mptr mr be (ebase + 0) = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Mem.load Mint64 mr be (ebase + 48) = Some (Vlong ixv) ->
  Clight2.eval_funcall bitcoin_ge mr (Internal f) [Vptr bt (Ptrofs.repr tbase); Vlong ixv] E0 mr (Vlong r) ->
  exists le1, Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl) le mc
    (bitcoin_check_distance_rest fid) E0 le1 mr
    (Out_return (Some (Val.of_bool (negb (Int64.ltu r xr)), tint))).
Proof.
  intros Hsym Hfun Hty HEf HEnv He0 He1 Ht0 HtM Hl_tx Hl_cnt Hl_ix Hlt Hread Hr_tx Hr_ix HLock.
  set (la5 := PTree.set _t'5 (Vptr bt (Ptrofs.repr tbase)) le).
  set (la6 := PTree.set _t'6 (Vlong nI) la5).
  set (la7 := PTree.set _t'7 (Vlong ixv) la6).
  set (l1 := PTree.set _t'1 (Vlong xr) la7).
  set (l2 := PTree.set _x (Vlong xr) l1).
  set (l3 := PTree.set _t'3 (Vptr bt (Ptrofs.repr tbase)) l2).
  set (l4 := PTree.set _t'4 (Vlong ixv) l3).
  set (l5 := PTree.set _t'2 (Vlong r) l4).
  assert (HE5 : la5!_env = Some (Vptr be (Ptrofs.repr ebase)))
    by (unfold la5; rewrite PTree.gso by discriminate; exact HEnv).
  assert (HE6 : la6!_env = Some (Vptr be (Ptrofs.repr ebase)))
    by (unfold la6; rewrite PTree.gso by discriminate; exact HE5).
  assert (HE7 : la7!_env = Some (Vptr be (Ptrofs.repr ebase)))
    by (unfold la7; rewrite PTree.gso by discriminate; exact HE6).
  assert (HE2 : l2!_env = Some (Vptr be (Ptrofs.repr ebase)))
    by (unfold l2, l1; rewrite PTree.gso by discriminate; rewrite PTree.gso by discriminate; exact HE7).
  assert (HE3 : l3!_env = Some (Vptr be (Ptrofs.repr ebase)))
    by (unfold l3; rewrite PTree.gso by discriminate; exact HE2).
  exists l5. unfold bitcoin_check_distance_rest.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la7).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la5).
    + apply exec_set. eapply eval_bitcoin_env_tx_expr; [exact HEnv|exact He0|lia|exact Hl_tx].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la6).
      * apply exec_set.
        eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := 448) (chunk := Mint64).
        -- reflexivity.
        -- exact bitcoin_tx_numInputs.
        -- reflexivity.
        -- apply eval_bitcoin_deref_struct. unfold la5. apply PTree.gss.
        -- rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact Hl_cnt].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la7).
        -- apply exec_set. eapply eval_bitcoin_env_ix; [exact HE6|exact He0|exact He1|exact Hl_ix].
        -- eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
           ++ eapply eval_Ebinop with (v1 := Vlong nI) (v2 := Vlong ixv).
              ** apply eval_Etempvar. unfold la7. rewrite PTree.gso by discriminate. apply PTree.gss.
              ** apply eval_Etempvar. unfold la7. apply PTree.gss.
              ** change (Some (Val.of_bool (negb (Int64.ltu ixv nI))) = Some (Vint Int.zero)).
                 rewrite Hlt. reflexivity.
           ++ reflexivity.
           ++ apply exec_Sskip.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l2).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l1).
      * change l1 with (set_opttemp (Some _t'1) (Vlong xr) la7).
        eapply exec_bitcoin_helper_call with (id := _simplicity_read16) (f := jets.f_simplicity_read16)
          (vargs := [Vptr bl Ptrofs.zero]) (vres := Vlong xr).
        -- unfold bitcoin_core_helpers. simpl. tauto.
        -- reflexivity.
        -- eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
        -- reflexivity.
        -- exact Hread.
      * apply exec_set. apply eval_Etempvar. unfold l1. apply PTree.gss.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l5).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l3).
        -- apply exec_set. eapply eval_bitcoin_env_tx_expr; [exact HE2|exact He0|lia|exact Hr_tx].
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l4).
           ++ apply exec_set. eapply eval_bitcoin_env_ix; [exact HE3|exact He0|exact He1|exact Hr_ix].
           ++ change l5 with (set_opttemp (Some _t'2) (Vlong r) l4).
              eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block fid) Ptrofs.zero)
                (vargs := [Vptr bt (Ptrofs.repr tbase); Vlong ixv]) (f := Internal f).
              ** reflexivity.
              ** eapply eval_Elvalue.
                 --- apply eval_Evar_global; [exact HEf|exact Hsym].
                 --- apply deref_loc_reference; reflexivity.
              ** eapply eval_Econs.
                 --- apply eval_Etempvar. unfold l4. rewrite PTree.gso by discriminate.
                     unfold l3. apply PTree.gss.
                 --- reflexivity.
                 --- eapply eval_Econs; [apply eval_Etempvar; unfold l4; apply PTree.gss|reflexivity|
                       apply eval_Enil].
              ** exact Hfun.
              ** exact Hty.
              ** exact HLock.
      * apply exec_Sreturn_some.
        eapply eval_Ebinop with (v1 := Vlong xr) (v2 := Vlong r).
        -- apply eval_Etempvar. unfold l5, l4, l3. repeat rewrite PTree.gso by discriminate.
           unfold l2. apply PTree.gss.
        -- apply eval_Etempvar. unfold l5. apply PTree.gss.
        -- reflexivity.
Qed.

Lemma dist_result_unsigned (dist : bool) (ver seq : int64) (V S : Z) :
  Int64.unsigned ver = V -> Int64.unsigned seq = S -> 0 <= S < 4294967296 ->
  Int64.unsigned
    (dist_result ver seq (if dist then negb (parse_sequence_tag seq) else parse_sequence_tag seq)) =
    dist_value dist (2 <=? V) S mod 65536.
Proof.
  intros HV HS HR.
  assert (HX : Int64.unsigned seq = @toZ (WordToZ 5) (@fromZ (WordToZ 5) S)).
  { rewrite to_fromZ, two_power_nat_equiv, word_bitSize, Z.mod_small by exact HR. exact HS. }
  unfold dist_result, dist_value.
  rewrite (version_ok_value ver V HV).
  rewrite (parse_sequence_enabled_bit31 _ seq HX), (parse_sequence_tag_bit22 _ seq HX).
  rewrite <- HX, HS.
  destruct ((2 <=? V) && negb (Z.testbit S 31) &&
    (if dist then negb (Z.testbit S 22) else Z.testbit S 22))%bool.
  - unfold parse_sequence_payload.
    assert (HM : Int64.and seq (Int64.repr 65535) = Int64.zero_ext 16 seq).
    { symmetry. apply Int64.zero_ext_and; lia. }
    rewrite HM, Int64.zero_ext_mod by (change Int64.zwordsize with 64; lia).
    rewrite HS. reflexivity.
  - reflexivity.
Qed.

Section CheckDistanceJet.
Variable dist : bool.
Variable jet : function.
Variable fid : ident.
Variable f : function.
Hypothesis Hsym : Genv.find_symbol (Clight.genv_genv bitcoin_ge) fid = Some (bitcoin_symbol_block fid).
Hypothesis Hfun : Genv.find_funct (Clight.genv_genv bitcoin_ge)
  (Vptr (bitcoin_symbol_block fid) Ptrofs.zero) = Some (Internal f).
Hypothesis Hshape : bitcoin_wrapper_shape jet (bitcoin_check_distance_rest fid).
Hypothesis Hlocal : forall bl, (bitcoin_version_locals bl)!fid = None.
Hypothesis Hty : type_of_fundef (Internal f) = dist_fn_type.
Hypothesis Hexec : forall m bt tbase bin inbase ix nI ver seq,
  0 <= tbase -> tbase + 488 <= Ptrofs.max_unsigned -> 0 <= inbase ->
  inbase + 160 * Int64.unsigned ix + 144 + 8 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m bt (tbase + 448) = Some (Vlong nI) ->
  Mem.load Mint64 m bt (tbase + 464) = Some (Vlong ver) ->
  Mem.load Mptr m bt (tbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  Mem.load Mint64 m bin (inbase + 160 * Int64.unsigned ix + 144) = Some (Vlong seq) ->
  Int64.ltu ix nI = true ->
  Clight2.eval_funcall bitcoin_ge m (Internal f) [Vptr bt (Ptrofs.repr tbase); Vlong ix] E0 m
    (Vlong (dist_result ver seq
      (if dist then negb (parse_sequence_tag seq) else parse_sequence_tag seq))).

Lemma bitcoin_check_distance_jet_spec :
  application_jet_partial_spec jet bitcoin_ge Bitcoin.env (Word 4) Ty.Unit bitcoin_distance_env_rep
    (fun a environment =>
      @bitcoin_check_distance_program dist (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor x
    (be & ebase & bt & txbase & bin & inbase & nI & ixv & ver & HEnvVal & He0 & He1 & Ht0 & Ht1 &
      Hi0 & Hi1 & HLtx & HLarr & HLcnt & HLver & HLix & HnI & Hixv & Hver & HLelem)
    HB HA HRF HR0 HRmax Hin HFrame.
  subst env.
  pose proof HRF as [HSedge HSoff].
  apply frame_input_word_at_encode in Hin.
  change (Z.of_nat (bitSize (Word 4))) with 16 in HRmax.
  destruct (bitcoin_check_distance_program_value dist x environment) as (txi & Hnth & Hspec).
  assert (Hix_lt : (Bitcoin.envIx environment < length (sigTxIn (Bitcoin.envTx environment)))%nat)
    by (apply nth_error_Some; rewrite Hnth; discriminate).
  assert (Hlt : Int64.ltu ixv nI = true).
  { unfold Int64.ltu. rewrite zlt_true; [reflexivity|]. rewrite Hixv, HnI. lia. }
  set (seq := Int64.repr (Int.unsigned (sigTxiSequence txi))).
  pose proof (Int.unsigned_range (sigTxiSequence txi)) as HSR.
  change Int.modulus with 4294967296 in HSR.
  assert (HSU : Int64.unsigned seq = Int.unsigned (sigTxiSequence txi)).
  { unfold seq. apply Int64.unsigned_repr.
    change Int64.max_unsigned with 18446744073709551615. lia. }
  assert (Hv : Mem.load Mint64 m bin (inbase + 160 * Int64.unsigned ixv + 144) = Some (Vlong seq)).
  { rewrite Hixv. exact (HLelem _ txi Hnth). }
  assert (HiM : inbase + 160 * Int64.unsigned ixv + 144 + 8 <= Ptrofs.max_unsigned).
  { rewrite Hixv. lia. }
  set (r := dist_result ver seq
    (if dist then negb (parse_sequence_tag seq) else parse_sequence_tag seq)).
  set (D := dist_value dist (2 <=? Int.unsigned (sigTxVersion (Bitcoin.envTx environment)))
    (Int.unsigned (sigTxiSequence txi)) mod 65536) in *.
  assert (HRU : Int64.unsigned r = D).
  { unfold r, D. exact (dist_result_unsigned dist ver seq _ _ Hver HSU HSR). }
  set (ok := @toZ (WordToZ 4) x <=? D) in *.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  destruct (bitcoin_bool_wrapper jet (bitcoin_check_distance_rest fid) (Vptr be (Ptrofs.repr ebase))
    m bd dbase bs sbase bytes ok Hshape HB HA HBytes) as (mf & HCall & HMem).
  { intros ma mc bl HAlloc HBa HStore.
    assert (HBefore : forall chunk b ofs v,
      Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v).
    { intros chunk b ofs v HL.
      assert (Hbl : bl <> b) by (eapply fresh_frame_not_loaded; eauto).
      erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact HStore|auto]. }
    destruct (bitcoin_read_wide_step W16 m ma mc bl bs sbase bi edge read_cursor x bytes
      ltac:(change (wide_bits W16) with 16; lia) HRF Hin HAlloc HBa HStore)
      as (mr & xr & Hread & Hxr & _ & HMemR & HPermR & _ & HKeep).
    assert (Hok : negb (Int64.ltu r xr) = ok).
    { unfold ok, Int64.ltu. rewrite HRU, Hxr.
      change (@toZ (WordToZ (wide_log W16)) x) with (@toZ (WordToZ 4) x).
      destruct (zlt D (@toZ (WordToZ 4) x)); symmetry;
        [apply Z.leb_gt|apply Z.leb_le]; cbn [negb]; lia. }
    destruct (exec_bitcoin_check_distance_rest fid f bl
      (bitcoin_wrapper_temps jet (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase)
      mc mr be ebase bt txbase nI ixv xr r Hsym Hfun Hty (Hlocal bl)
      ltac:(unfold bitcoin_wrapper_temps; apply PTree.gss) He0 He1 Ht0 Ht1
      (HBefore _ _ _ _ HLtx) (HBefore _ _ _ _ HLcnt) (HBefore _ _ _ _ HLix) Hlt Hread
      (HKeep _ _ _ _ HLtx) (HKeep _ _ _ _ HLix)
      (Hexec mr bt txbase bin inbase ixv nI ver seq Ht0 Ht1 Hi0 HiM
        (HKeep _ _ _ _ HLcnt) (HKeep _ _ _ _ HLver) (HKeep _ _ _ _ HLarr) (HKeep _ _ _ _ Hv) Hlt))
      as [le1 HExec].
    rewrite Hok in HExec.
    exists le1, mr. split; [exact HExec|]. split; [exact HMemR|exact HPermR]. }
  exists mf. rewrite Hspec.
  split; [destruct ok; exact HCall|]. split.
  - destruct ok; [|exact I].
    destruct HFrame as (_ & [HDE HDO] & _).
    split; [intros i c Hi; destruct i; discriminate|]. split.
    + intros old HL. exists old. split.
      * rewrite HMem by (eapply load_valid_block; exact HL). exact HL.
      * intros i _ _. reflexivity.
    + change (Z.of_nat (bitSize Ty.Unit)) with 0. rewrite Z.sub_0_r. split.
      * rewrite HMem by (eapply load_valid_block; exact HDE). exact HDE.
      * rewrite HMem by (eapply load_valid_block; exact HDO). exact HDO.
  - intros chunk b ofs HV _ _. apply HMem. exact HV.
Qed.
End CheckDistanceJet.

Lemma lockDistance_exec m bt tbase bin inbase ix nI ver seq :
  0 <= tbase -> tbase + 488 <= Ptrofs.max_unsigned -> 0 <= inbase ->
  inbase + 160 * Int64.unsigned ix + 144 + 8 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m bt (tbase + 448) = Some (Vlong nI) ->
  Mem.load Mint64 m bt (tbase + 464) = Some (Vlong ver) ->
  Mem.load Mptr m bt (tbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  Mem.load Mint64 m bin (inbase + 160 * Int64.unsigned ix + 144) = Some (Vlong seq) ->
  Int64.ltu ix nI = true ->
  Clight2.eval_funcall bitcoin_ge m (Internal f_lockDistance) [Vptr bt (Ptrofs.repr tbase); Vlong ix] E0 m
    (Vlong (dist_result ver seq (negb (parse_sequence_tag seq)))).
Proof.
  intros H0 HM Hi HiM HLn HLv HLi HLs Hlt. rewrite f_lockDistance_shape.
  eapply eval_dist_fn; try eassumption.
  intros le Hle. apply lock_distance_bit_eval. exact Hle.
Qed.

Lemma lockDuration_exec m bt tbase bin inbase ix nI ver seq :
  0 <= tbase -> tbase + 488 <= Ptrofs.max_unsigned -> 0 <= inbase ->
  inbase + 160 * Int64.unsigned ix + 144 + 8 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m bt (tbase + 448) = Some (Vlong nI) ->
  Mem.load Mint64 m bt (tbase + 464) = Some (Vlong ver) ->
  Mem.load Mptr m bt (tbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  Mem.load Mint64 m bin (inbase + 160 * Int64.unsigned ix + 144) = Some (Vlong seq) ->
  Int64.ltu ix nI = true ->
  Clight2.eval_funcall bitcoin_ge m (Internal f_lockDuration) [Vptr bt (Ptrofs.repr tbase); Vlong ix] E0 m
    (Vlong (dist_result ver seq (parse_sequence_tag seq))).
Proof.
  intros H0 HM Hi HiM HLn HLv HLi HLs Hlt. rewrite f_lockDuration_shape.
  eapply eval_dist_fn; try eassumption.
  intros le Hle. apply lock_duration_bit_eval. exact Hle.
Qed.

Lemma bitcoin_check_lock_distance_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_check_lock_distance
    (bitcoin_check_distance_rest _lockDistance).
Proof. wrapper_shape. Qed.
Lemma bitcoin_check_lock_duration_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_check_lock_duration
    (bitcoin_check_distance_rest _lockDuration).
Proof. wrapper_shape. Qed.

Theorem bitcoin_check_lock_distance_local_spec :
  application_jet_partial_spec f_simplicity_bitcoin_check_lock_distance bitcoin_ge Bitcoin.env
    (Word 4) Ty.Unit bitcoin_distance_env_rep
    (fun a environment =>
      @bitcoin_check_lock_distance_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply (bitcoin_check_distance_jet_spec true) with (fid := _lockDistance) (f := f_lockDistance).
  - exact bitcoin_lockDistance_symbol.
  - exact bitcoin_lockDistance_funct.
  - exact bitcoin_check_lock_distance_shape.
  - intro bl. reflexivity.
  - reflexivity.
  - exact lockDistance_exec.
Qed.

Theorem bitcoin_check_lock_duration_local_spec :
  application_jet_partial_spec f_simplicity_bitcoin_check_lock_duration bitcoin_ge Bitcoin.env
    (Word 4) Ty.Unit bitcoin_distance_env_rep
    (fun a environment =>
      @bitcoin_check_lock_duration_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply (bitcoin_check_distance_jet_spec false) with (fid := _lockDuration) (f := f_lockDuration).
  - exact bitcoin_lockDuration_symbol.
  - exact bitcoin_lockDuration_funct.
  - exact bitcoin_check_lock_duration_shape.
  - intro bl. reflexivity.
  - reflexivity.
  - exact lockDuration_exec.
Qed.
