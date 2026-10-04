(** Actual Bitcoin tx_lock_distance / tx_lock_duration jets against the
    literal canonical TimeLock programs.
    C: [if (env->tx->numInputs <= env->ix) return false;
        simplicity_write16(dst, lockDistance(env->tx, env->ix)); return true;] *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_exec C.jet_application_contract C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_spec C.jet_encoding.
Require Import C.jet_wide C.jet_wide_spec C.jet_word_repr C.jet_parse_sequence_spec.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_steps.
Require Import C.jet_bitcoin_current_exec C.jet_bitcoin_is_final_local.
Require Import C.jet_bitcoin_distance_exec C.jet_bitcoin_distance_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Definition bit22_mask : int64 := Int64.shl Int64.one (Int64.repr 22).

Lemma eval_bit22 m seq le :
  le!_t'6 = Some (Vlong seq) ->
  eval_expr bitcoin_ge empty_env le m bit22_expr (Vlong (Int64.and seq bit22_mask)).
Proof.
  intro HT. unfold bit22_expr.
  eapply eval_Ebinop with (v2 := Vlong bit22_mask).
  - apply eval_Etempvar. exact HT.
  - eapply eval_Ebinop.
    + eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
    + apply eval_Econst_int.
    + reflexivity.
  - reflexivity.
Qed.

Lemma eval_bit22_clear m seq le :
  le!_t'6 = Some (Vlong seq) ->
  eval_expr bitcoin_ge empty_env le m (Eunop Onotbool bit22_expr tint)
    (Val.of_bool (negb (parse_sequence_tag seq))).
Proof.
  intro HT. eapply eval_Eunop; [apply eval_bit22; exact HT|reflexivity].
Qed.

Lemma lock_distance_bit_eval m seq le :
  le!_t'6 = Some (Vlong seq) ->
  eval_expr bitcoin_ge empty_env le m (Ecast lock_distance_bit tbool)
    (Vint (bool_int (negb (parse_sequence_tag seq)))).
Proof.
  intro HT. pose proof (eval_bit22_clear m seq le HT) as H1. unfold lock_distance_bit.
  destruct (parse_sequence_tag seq); (eapply eval_Ecast; [exact H1|reflexivity]).
Qed.

Lemma lock_duration_bit_eval m seq le :
  le!_t'6 = Some (Vlong seq) ->
  eval_expr bitcoin_ge empty_env le m (Ecast lock_duration_bit tbool)
    (Vint (bool_int (parse_sequence_tag seq))).
Proof.
  intro HT. pose proof (eval_bit22_clear m seq le HT) as H1. unfold lock_duration_bit.
  destruct (parse_sequence_tag seq);
    (eapply eval_Ecast; [eapply eval_Eunop; [exact H1|reflexivity]|reflexivity]).
Qed.

Lemma bitcoin_lockDistance_symbol :
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) _lockDistance = Some (bitcoin_symbol_block _lockDistance).
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_lockDistance_funct :
  Genv.find_funct (Clight.genv_genv bitcoin_ge)
    (Vptr (bitcoin_symbol_block _lockDistance) Ptrofs.zero) = Some (Internal f_lockDistance).
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_lockDuration_symbol :
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) _lockDuration = Some (bitcoin_symbol_block _lockDuration).
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_lockDuration_funct :
  Genv.find_funct (Clight.genv_genv bitcoin_ge)
    (Vptr (bitcoin_symbol_block _lockDuration) Ptrofs.zero) = Some (Internal f_lockDuration).
Proof. vm_compute; reflexivity. Qed.

Definition dist_fn_type : type :=
  Tfunction (Tcons (tptr (Tstruct _bitcoinTransaction noattr)) (Tcons tulong Tnil)) tulong cc_default.

Definition bitcoin_distance_rest (fid : ident) : statement :=
  Ssequence
    (Ssequence (Sset _t'4 bitcoin_env_tx_expr)
      (Ssequence
        (Sset _t'5 (Efield (Ederef (Etempvar _t'4 (tptr (Tstruct _bitcoinTransaction noattr)))
          (Tstruct _bitcoinTransaction noattr)) _numInputs tulong))
        (Ssequence (Sset _t'6 bitcoin_env_ix_expr)
          (Sifthenelse (Ebinop Ole (Etempvar _t'5 tulong) (Etempvar _t'6 tulong) tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip))))
    (Ssequence
      (Ssequence
        (Ssequence (Sset _t'2 bitcoin_env_tx_expr)
          (Ssequence (Sset _t'3 bitcoin_env_ix_expr)
            (Scall (Some _t'1) (Evar fid dist_fn_type)
              [Etempvar _t'2 (tptr (Tstruct _bitcoinTransaction noattr)); Etempvar _t'3 tulong])))
        (Scall None
          (Evar _simplicity_write16 (Tfunction
            (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
          [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'1 tulong]))
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))).

Lemma exec_bitcoin_distance_rest fid f e le mc me bd dbase be ebase bt tbase (nI ixv r : int64) :
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) fid = Some (bitcoin_symbol_block fid) ->
  Genv.find_funct (Clight.genv_genv bitcoin_ge) (Vptr (bitcoin_symbol_block fid) Ptrofs.zero) =
    Some (Internal f) ->
  type_of_fundef (Internal f) = dist_fn_type ->
  e!fid = None -> e!_simplicity_write16 = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ebase -> ebase + 56 <= Ptrofs.max_unsigned ->
  0 <= tbase -> tbase + 488 <= Ptrofs.max_unsigned ->
  Mem.load Mptr mc be (ebase + 0) = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Mem.load Mint64 mc bt (tbase + 448) = Some (Vlong nI) ->
  Mem.load Mint64 mc be (ebase + 48) = Some (Vlong ixv) ->
  Int64.ltu ixv nI = true ->
  Clight2.eval_funcall bitcoin_ge mc (Internal f) [Vptr bt (Ptrofs.repr tbase); Vlong ixv] E0 mc (Vlong r) ->
  Clight2.eval_funcall bitcoin_ge mc (Internal jets.f_simplicity_write16)
    [Vptr bd (Ptrofs.repr dbase); Vlong r] E0 me Vundef ->
  exists le1, Clight2.exec_stmt bitcoin_ge e le mc (bitcoin_distance_rest fid) E0 le1 me
    bitcoin_returned_one.
Proof.
  intros Hsym Hfun Hty HEf HW HEnv HDst He0 He1 Ht0 HtM Hl_tx Hl_cnt Hl_ix Hlt HLock HCall.
  set (la4 := PTree.set _t'4 (Vptr bt (Ptrofs.repr tbase)) le).
  set (la5 := PTree.set _t'5 (Vlong nI) la4).
  set (la6 := PTree.set _t'6 (Vlong ixv) la5).
  set (lb2 := PTree.set _t'2 (Vptr bt (Ptrofs.repr tbase)) la6).
  set (lb3 := PTree.set _t'3 (Vlong ixv) lb2).
  set (lb1 := PTree.set _t'1 (Vlong r) lb3).
  assert (HE4 : la4!_env = Some (Vptr be (Ptrofs.repr ebase)))
    by (unfold la4; rewrite PTree.gso by discriminate; exact HEnv).
  assert (HE5 : la5!_env = Some (Vptr be (Ptrofs.repr ebase)))
    by (unfold la5; rewrite PTree.gso by discriminate; exact HE4).
  assert (HE6 : la6!_env = Some (Vptr be (Ptrofs.repr ebase)))
    by (unfold la6; rewrite PTree.gso by discriminate; exact HE5).
  assert (HEb2 : lb2!_env = Some (Vptr be (Ptrofs.repr ebase)))
    by (unfold lb2; rewrite PTree.gso by discriminate; exact HE6).
  exists lb1. unfold bitcoin_distance_rest.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la6).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la4).
    + apply exec_set. eapply eval_bitcoin_env_tx_expr; [exact HEnv|exact He0|lia|exact Hl_tx].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la5).
      * apply exec_set.
        eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := 448) (chunk := Mint64).
        -- reflexivity.
        -- exact bitcoin_tx_numInputs.
        -- reflexivity.
        -- apply eval_bitcoin_deref_struct. unfold la4. apply PTree.gss.
        -- rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact Hl_cnt].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la6).
        -- apply exec_set. eapply eval_bitcoin_env_ix; [exact HE5|exact He0|exact He1|exact Hl_ix].
        -- eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
           ++ eapply eval_Ebinop with (v1 := Vlong nI) (v2 := Vlong ixv).
              ** apply eval_Etempvar. unfold la6. rewrite PTree.gso by discriminate. apply PTree.gss.
              ** apply eval_Etempvar. unfold la6. apply PTree.gss.
              ** change (Some (Val.of_bool (negb (Int64.ltu ixv nI))) = Some (Vint Int.zero)).
                 rewrite Hlt. reflexivity.
           ++ reflexivity.
           ++ apply exec_Sskip.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := lb1);
      [|apply exec_Sreturn_some, eval_Econst_int].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := lb1).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := lb2).
      * apply exec_set. eapply eval_bitcoin_env_tx_expr; [exact HE6|exact He0|lia|exact Hl_tx].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := lb3).
        -- apply exec_set. eapply eval_bitcoin_env_ix; [exact HEb2|exact He0|exact He1|exact Hl_ix].
        -- change lb1 with (set_opttemp (Some _t'1) (Vlong r) lb3).
           eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block fid) Ptrofs.zero)
             (vargs := [Vptr bt (Ptrofs.repr tbase); Vlong ixv]) (f := Internal f).
           ++ reflexivity.
           ++ eapply eval_Elvalue.
              ** apply eval_Evar_global; [exact HEf|exact Hsym].
              ** apply deref_loc_reference; reflexivity.
           ++ eapply eval_Econs.
              ** apply eval_Etempvar. unfold lb3. rewrite PTree.gso by discriminate.
                 unfold lb2. apply PTree.gss.
              ** reflexivity.
              ** eapply eval_Econs; [apply eval_Etempvar; unfold lb3; apply PTree.gss|reflexivity|
                   apply eval_Enil].
           ++ exact Hfun.
           ++ exact Hty.
           ++ exact HLock.
    + refine (exec_bitcoin_helper_call _ _ _ None _simplicity_write16 jets.f_simplicity_write16
        _ _ _ _ _ Vundef _ _ _ _ _ _).
      * unfold bitcoin_core_helpers. simpl. tauto.
      * exact HW.
      * eapply eval_Econs.
        -- apply eval_Etempvar. unfold lb1, lb3, lb2, la6, la5, la4.
           repeat rewrite PTree.gso by discriminate. exact HDst.
        -- reflexivity.
        -- eapply eval_Econs; [apply eval_Etempvar; unfold lb1; apply PTree.gss|reflexivity|apply eval_Enil].
      * reflexivity.
      * exact HCall.
Qed.

Definition bitcoin_distance_env_rep (m : mem) (env : val) (environment : Bitcoin.env) : Prop :=
  exists be ebase bt txbase bin inbase nI ixv ver,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= txbase /\ txbase + 488 <= Ptrofs.max_unsigned /\
    0 <= inbase /\
    inbase + 160 * Z.of_nat (length (sigTxIn (Bitcoin.envTx environment))) <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mptr m bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) /\
    Mem.load Mint64 m bt (txbase + 448) = Some (Vlong nI) /\
    Mem.load Mint64 m bt (txbase + 464) = Some (Vlong ver) /\
    Mem.load Mint64 m be (ebase + 48) = Some (Vlong ixv) /\
    Int64.unsigned nI = Z.of_nat (length (sigTxIn (Bitcoin.envTx environment))) /\
    Int64.unsigned ixv = Z.of_nat (Bitcoin.envIx environment) /\
    Int64.unsigned ver = Int.unsigned (sigTxVersion (Bitcoin.envTx environment)) /\
    (forall j txi, nth_error (sigTxIn (Bitcoin.envTx environment)) j = Some txi ->
      Mem.load Mint64 m bin (inbase + 160 * Z.of_nat j + 144) =
        Some (Vlong (Int64.repr (Int.unsigned (sigTxiSequence txi))))).

Lemma version_ok_value ver V :
  Int64.unsigned ver = V -> version_ok ver = (2 <=? V).
Proof.
  intro HV. unfold version_ok, Int64.ltu.
  rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  rewrite HV. destruct (zlt V 2); symmetry; [apply Z.leb_gt|apply Z.leb_le]; lia.
Qed.

Lemma dist_result_value (dist : bool) (ver seq : int64) (V S : Z) :
  Int64.unsigned ver = V -> Int64.unsigned seq = S -> 0 <= S < 4294967296 ->
  decode_wide W16 (Int64.zero_ext 16
    (dist_result ver seq (if dist then negb (parse_sequence_tag seq) else parse_sequence_tag seq))) =
    @fromZ (WordToZ 4) (dist_value dist (2 <=? V) S).
Proof.
  intros HV HS HR.
  assert (HX : Int64.unsigned seq = @toZ (WordToZ 5) (@fromZ (WordToZ 5) S)).
  { rewrite to_fromZ, two_power_nat_equiv, word_bitSize, Z.mod_small by exact HR. exact HS. }
  unfold dist_result, dist_value.
  rewrite (version_ok_value ver V HV).
  rewrite (parse_sequence_enabled_bit31 _ seq HX), (parse_sequence_tag_bit22 _ seq HX).
  rewrite <- HX, HS.
  destruct ((2 <=? V) && negb (Z.testbit S 31) &&
    (if dist then negb (Z.testbit S 22) else Z.testbit S 22))%bool eqn:Hc.
  - rewrite parse_sequence_payload_decode, HS. reflexivity.
  - reflexivity.
Qed.

Section DistanceJet.
Variable dist : bool.
Variable jet : function.
Variable fid : ident.
Variable f : function.
Hypothesis Hsym : Genv.find_symbol (Clight.genv_genv bitcoin_ge) fid = Some (bitcoin_symbol_block fid).
Hypothesis Hfun : Genv.find_funct (Clight.genv_genv bitcoin_ge)
  (Vptr (bitcoin_symbol_block fid) Ptrofs.zero) = Some (Internal f).
Hypothesis Hshape : bitcoin_wrapper_shape jet (bitcoin_distance_rest fid).
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

Lemma bitcoin_distance_jet_local_spec :
  application_jet_local_spec jet bitcoin_ge Bitcoin.env Ty.Unit (Word 4) bitcoin_distance_env_rep
    (fun a environment =>
      @bitcoin_lock_distance_program dist (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor []
    (be & ebase & bt & txbase & bin & inbase & nI & ixv & ver & HEnvVal & He0 & He1 & Ht0 & Ht1 &
      Hi0 & Hi1 & HLtx & HLarr & HLcnt & HLver & HLix & HnI & Hixv & Hver & HLelem)
    HB HA [HSedge HSoff] HR0 HRmax Hin HFrame.
  subst env.
  assert (HC : Z.of_nat (bitSize (Word 4)) = 16) by reflexivity.
  rewrite HC in HFrame.
  destruct (bitcoin_lock_distance_program_value dist environment) as (txi & Hnth & Hspec).
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
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (value := @fromZ (WordToZ 4) (dist_value dist
    (2 <=? Int.unsigned (sigTxVersion (Bitcoin.envTx environment)))
    (Int.unsigned (sigTxiSequence txi)))).
  assert (HMid : bitcoin_wrapper_mid jet (bitcoin_distance_rest fid) (encode value)
    (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 16 bytes).
  { unfold bitcoin_wrapper_mid. intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    destruct (bitcoin_write_wide_step W16 mc bd dbase bw outedge cursor r HFrameC)
      as (me & HCallW & E).
    destruct (exec_bitcoin_distance_rest fid f (bitcoin_version_locals bl)
      (bitcoin_wrapper_temps jet (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase)
      mc me bd dbase be ebase bt txbase nI ixv r Hsym Hfun Hty (Hlocal bl) ltac:(reflexivity)
      ltac:(unfold bitcoin_wrapper_temps; apply PTree.gss)
      ltac:(unfold bitcoin_wrapper_temps; rewrite PTree.gso by discriminate;
        rewrite PTree.gso by discriminate; apply PTree.gss)
      He0 He1 Ht0 Ht1 (HLP _ _ _ _ HLtx) (HLP _ _ _ _ HLcnt) (HLP _ _ _ _ HLix) Hlt
      (Hexec mc bt txbase bin inbase ixv nI ver seq Ht0 Ht1 Hi0 HiM
        (HLP _ _ _ _ HLcnt) (HLP _ _ _ _ HLver) (HLP _ _ _ _ HLarr) (HLP _ _ _ _ Hv) Hlt)
      HCallW) as [le1 HExec].
    destruct E as (c & p & fl & l & pm & vv).
    assert (Hd : decode_wide W16 (Int64.zero_ext 16 r) = value).
    { unfold r, value. exact (dist_result_value dist ver seq _ _ Hver HSU HSR). }
    change (wide_bits W16) with 16 in c. rewrite Hd in c.
    exists le1, me.
    refine (conj HExec (conj c (conj p (conj fl (conj _ (conj pm vv)))))).
    intros chunk b ofs _ H1' H2'. exact (l chunk b ofs H1' H2'). }
  destruct (bitcoin_wrapper_layout jet (bitcoin_distance_rest fid) (encode value)
    (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 16 bytes
    Hshape HB HA HBytes ltac:(lia) HFrame HMid)
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, value. split; [exact Hspec|].
  split; [exact HCall|]. split; [exact HCells|]. split; [exact HPrefix|].
  rewrite HC. split; [exact HFields|]. exact HMem.
Qed.
End DistanceJet.

Ltac wrapper_shape :=
  repeat split; try reflexivity;
  intros x y HX HY Hxy; cbn in HX, HY;
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].

Lemma bitcoin_tx_lock_distance_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_tx_lock_distance (bitcoin_distance_rest _lockDistance).
Proof. wrapper_shape. Qed.
Lemma bitcoin_tx_lock_duration_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_tx_lock_duration (bitcoin_distance_rest _lockDuration).
Proof. wrapper_shape. Qed.

Theorem bitcoin_tx_lock_distance_local_spec :
  application_jet_local_spec f_simplicity_bitcoin_tx_lock_distance bitcoin_ge Bitcoin.env
    Ty.Unit (Word 4) bitcoin_distance_env_rep
    (fun a environment => @bitcoin_tx_lock_distance_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply (bitcoin_distance_jet_local_spec true) with (fid := _lockDistance) (f := f_lockDistance).
  - exact bitcoin_lockDistance_symbol.
  - exact bitcoin_lockDistance_funct.
  - exact bitcoin_tx_lock_distance_shape.
  - intro bl. reflexivity.
  - reflexivity.
  - intros m bt tbase bin inbase ix nI ver seq H0 HM Hi HiM HLn HLv HLi HLs Hlt.
    rewrite f_lockDistance_shape.
    eapply eval_dist_fn; try eassumption.
    intros le Hle. apply lock_distance_bit_eval. exact Hle.
Qed.

Theorem bitcoin_tx_lock_duration_local_spec :
  application_jet_local_spec f_simplicity_bitcoin_tx_lock_duration bitcoin_ge Bitcoin.env
    Ty.Unit (Word 4) bitcoin_distance_env_rep
    (fun a environment => @bitcoin_tx_lock_duration_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply (bitcoin_distance_jet_local_spec false) with (fid := _lockDuration) (f := f_lockDuration).
  - exact bitcoin_lockDuration_symbol.
  - exact bitcoin_lockDuration_funct.
  - exact bitcoin_tx_lock_duration_shape.
  - intro bl. reflexivity.
  - reflexivity.
  - intros m bt tbase bin inbase ix nI ver seq H0 HM Hi HiM HLn HLv HLi HLs Hlt.
    rewrite f_lockDuration_shape.
    eapply eval_dist_fn; try eassumption.
    intros le Hle. apply lock_duration_bit_eval. exact Hle.
Qed.
