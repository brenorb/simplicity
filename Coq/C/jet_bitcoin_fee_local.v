(** Actual Bitcoin fee jet against the literal canonical program
    [totalInputValue &&& totalOutputValue >>> subtract word64 >>> ih].
    C: [simplicity_write64(dst, env->tx->totalInputValue - env->tx->totalOutputValue)]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_exec C.jet_application_sep C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_spec C.jet_encoding.
Require Import C.jet_wide C.jet_wide_spec C.jet_word_repr C.jet_forWhile_seq.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_hash_getters C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_steps.
Require Import C.jet_bitcoin_totals_spec C.jet_bitcoin_totals_canonical C.jet_bitcoin_totals_local.
Require Import C.jet_bitcoin_fee_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

Definition bitcoin_tx_field_set (ptr tmp : ident) (field : ident) : statement :=
  Sset tmp (Efield (Ederef (Etempvar ptr (tptr (Tstruct _bitcoinTransaction noattr)))
    (Tstruct _bitcoinTransaction noattr)) field tulong).

Definition bitcoin_env_tx_set (tmp : ident) : statement :=
  Sset tmp
    (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
      _tx (tptr (Tstruct _bitcoinTransaction noattr))).

Definition bitcoin_fee_mid : statement :=
  Ssequence (bitcoin_env_tx_set _t'1)
    (Ssequence (bitcoin_tx_field_set _t'1 _t'2 _totalInputValue)
      (Ssequence (bitcoin_env_tx_set _t'3)
        (Ssequence (bitcoin_tx_field_set _t'3 _t'4 _totalOutputValue)
          (Scall None
            (Evar _simplicity_write64 (Tfunction
              (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
            [Etempvar _dst (tptr (Tstruct _frameItem noattr));
             Ebinop Osub (Etempvar _t'2 tulong) (Etempvar _t'4 tulong) tulong])))).

Lemma exec_bitcoin_env_tx_set tmp e le m be ebase bt tbase :
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Clight2.exec_stmt bitcoin_ge e le m (bitcoin_env_tx_set tmp) E0
    (PTree.set tmp (Vptr bt (Ptrofs.repr tbase)) le) m Out_normal.
Proof.
  intros HE H0 HM HL. unfold bitcoin_env_tx_set. apply exec_set.
  eapply eval_bitcoin_field_value with (sid := _txEnv) (delta := 0) (chunk := Mptr).
  - reflexivity.
  - exact bitcoin_txEnv_tx.
  - reflexivity.
  - apply eval_bitcoin_deref_struct; exact HE.
  - rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|].
    replace (ebase + 0) with ebase by lia. exact HL.
Qed.

Lemma exec_bitcoin_tx_field_set ptr tmp field delta e le m bt tbase (x : int64) :
  bitcoin_field_at _bitcoinTransaction field delta -> 0 <= delta <= 480 ->
  le!ptr = Some (Vptr bt (Ptrofs.repr tbase)) ->
  0 <= tbase -> tbase + 488 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m bt (tbase + delta) = Some (Vlong x) ->
  Clight2.exec_stmt bitcoin_ge e le m (bitcoin_tx_field_set ptr tmp field) E0
    (PTree.set tmp (Vlong x) le) m Out_normal.
Proof.
  intros HF HD HP H0 HM HL. unfold bitcoin_tx_field_set. apply exec_set.
  eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := delta) (chunk := Mint64).
  - reflexivity.
  - exact HF.
  - reflexivity.
  - apply eval_bitcoin_deref_struct. exact HP.
  - rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HL].
Qed.

Definition bitcoin_fee_temps le bt tbase (vi vo : int64) : temp_env :=
  PTree.set _t'4 (Vlong vo) (PTree.set _t'3 (Vptr bt (Ptrofs.repr tbase))
    (PTree.set _t'2 (Vlong vi) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le))).

Lemma exec_bitcoin_fee_mid e le mc me bd dbase be ebase bt tbase (vi vo : int64) :
  e!_simplicity_write64 = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  0 <= tbase -> tbase + 488 <= Ptrofs.max_unsigned ->
  Mem.load Mptr mc be ebase = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Mem.load Mint64 mc bt (tbase + 432) = Some (Vlong vi) ->
  Mem.load Mint64 mc bt (tbase + 440) = Some (Vlong vo) ->
  Clight2.eval_funcall bitcoin_ge mc (Internal jets.f_simplicity_write64)
    [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.sub vi vo)] E0 me Vundef ->
  Clight2.exec_stmt bitcoin_ge e le mc bitcoin_fee_mid E0
    (bitcoin_fee_temps le bt tbase vi vo) me Out_normal.
Proof.
  intros HW HEnv HDst He HE0 Ht HtM HL HLi HLo HCall.
  unfold bitcoin_fee_mid, bitcoin_fee_temps.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
  { eapply exec_bitcoin_env_tx_set; [exact HEnv|exact He|exact HE0|exact HL]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
  { eapply exec_bitcoin_tx_field_set with (delta := 432) (x := vi);
      [exact bitcoin_tx_totalInputValue|lia|apply PTree.gss|exact Ht|exact HtM|exact HLi]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
  { eapply exec_bitcoin_env_tx_set with (be := be) (ebase := ebase);
      [|exact He|exact HE0|exact HL].
    rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. exact HEnv. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
  { eapply exec_bitcoin_tx_field_set with (delta := 440) (x := vo);
      [exact bitcoin_tx_totalOutputValue|lia|apply PTree.gss|exact Ht|exact HtM|exact HLo]. }
  refine (exec_bitcoin_helper_call _ _ _ None _simplicity_write64 jets.f_simplicity_write64
    _ _ _ _ _ Vundef _ _ _ _ _ _).
  - unfold bitcoin_core_helpers. simpl. tauto.
  - exact HW.
  - eapply eval_Econs.
    + apply eval_Etempvar. repeat rewrite PTree.gso by discriminate. exact HDst.
    + reflexivity.
    + eapply eval_Econs with (v1 := Vlong (Int64.sub vi vo)).
      * eapply eval_Ebinop.
        -- apply eval_Etempvar. rewrite PTree.gso by discriminate.
           rewrite PTree.gso by discriminate. apply PTree.gss.
        -- apply eval_Etempvar. apply PTree.gss.
        -- reflexivity.
      * reflexivity.
      * apply eval_Enil.
  - reflexivity.
  - exact HCall.
Qed.

Definition bitcoin_fee_env_rep (m : mem) (env : val) (environment : Bitcoin.env)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt tbase vi vo,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= tbase /\ tbase + 488 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr tbase)) /\
    Mem.load Mint64 m bt (tbase + 432) = Some (Vlong vi) /\
    Mem.load Mint64 m bt (tbase + 440) = Some (Vlong vo) /\
    Int64.unsigned vi = sigTxTotalInValue (Bitcoin.envTx environment) mod Int64.modulus /\
    Int64.unsigned vo = sigTxTotalOutValue (Bitcoin.envTx environment) mod Int64.modulus /\
    fp = [(be, ebase, ebase + 8); (bt, tbase + 432, tbase + 448)].

Lemma fw6_sub (vi vo : int64) :
  fw6 (Int64.unsigned (Int64.sub vi vo)) = fw6 (Int64.unsigned vi - Int64.unsigned vo).
Proof.
  unfold Int64.sub. rewrite Int64.unsigned_repr_eq.
  exact (word_fromZ_mod 6 (Int64.unsigned vi - Int64.unsigned vo)).
Qed.

Lemma bitcoin_fee_getter_body :
  bitcoin_wrapper_shape f_simplicity_bitcoin_fee (bitcoin_simple_rest bitcoin_fee_mid).
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Theorem bitcoin_fee_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_fee bitcoin_ge Bitcoin.env Ty.Unit Word64
    bitcoin_fee_env_rep
    (fun a environment => @bitcoin_fee_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor [] fp
    (be & ebase & bt & tbase & vi & vo & HEnvVal & He0 & HeM & Ht0 & HtM & HLoad & HVi & HVo &
      HRi & HRo & HFp)
    HSep HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env fp.
  assert (HC : Z.of_nat (bitSize Word64) = 64) by reflexivity.
  rewrite HC in HFrame.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (cells := encode (decode_wide W64 (Int64.zero_ext 64 (Int64.sub vi vo)))).
  assert (HMid : forall ma mc bl,
    Mem.alloc m 0 16 = (ma, bl) -> Mem.storebytes ma bl 0 bytes = Some mc ->
    (forall chunk b ofs v', Mem.load chunk m b ofs = Some v' -> Mem.load chunk mc b ofs = Some v') ->
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mc b ofs kind p) ->
    write_frame_at mc bd dbase bw outedge cursor 64 ->
    exists le1 me,
      Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl)
        (bitcoin_wrapper_temps f_simplicity_bitcoin_fee (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase) mc
        bitcoin_fee_mid E0 le1 me Out_normal /\
      write_effect mc me bd dbase bw outedge cursor 64 cells).
  { intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    destruct (bitcoin_write_wide_step W64 mc bd dbase bw outedge cursor (Int64.sub vi vo) HFrameC)
      as (me & HCall & HEff).
    eexists _, me. split; [|exact HEff].
    eapply exec_bitcoin_fee_mid with (be := be) (ebase := ebase) (bt := bt) (tbase := tbase)
      (vi := vi) (vo := vo).
    - reflexivity.
    - unfold bitcoin_wrapper_temps. apply PTree.gss.
    - unfold bitcoin_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact (HLP _ _ _ _ HLoad).
    - exact (HLP _ _ _ _ HVi).
    - exact (HLP _ _ _ _ HVo).
    - exact HCall. }
  destruct (bitcoin_wrapper_layout_simple f_simplicity_bitcoin_fee
    bitcoin_fee_mid cells (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 64 bytes
    bitcoin_fee_getter_body HB HA HBytes ltac:(lia) HFrame
    (fun ma mc bl HAlloc HStore HLP HPP HFrameC =>
      match HMid ma mc bl HAlloc HStore HLP HPP HFrameC with
      | ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF (conj HL (conj HPm HV))))))) =>
          ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF
            (conj (fun chunk b ofs _ H1 H2 => HL chunk b ofs H1 H2) (conj HPm HV)))))))
      end))
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (fw6 (sigTxTotalInValue (Bitcoin.envTx environment) -
                   sigTxTotalOutValue (Bitcoin.envTx environment))).
  split; [apply bitcoin_fee_spec_value|]. split; [exact HCall|].
  split; [unfold cells in HCells;
    rewrite decode_wide64_unsigned, fw6_sub, HRi, HRo, fw6_sub_mod64 in HCells; exact HCells|].
  split; [exact HPrefix|]. split; [exact HFields|]. exact HMem.
Qed.
