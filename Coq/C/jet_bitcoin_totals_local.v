(** Actual Bitcoin total_input_value / total_output_value jets against the
    literal canonical forWhile sums over InputValue / OutputValue.
    C: [simplicity_write64(dst, env->tx->totalInputValue)]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_exec C.jet_application_sep C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_spec C.jet_encoding.
Require Import C.jet_wide C.jet_wide_spec.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_hash_getters C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_steps.
Require Import C.jet_bitcoin_totals_spec C.jet_bitcoin_totals_canonical.
Require Import C.jet_word_repr.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge.
Set Default Timeout 60.

Definition bitcoin_tx64_mid (field : ident) : statement :=
  Ssequence (bitcoin_env_ptr_stmt _tx _bitcoinTransaction)
    (Ssequence
      (Sset _t'2 (Efield (Ederef (Etempvar _t'1 (tptr (Tstruct _bitcoinTransaction noattr)))
        (Tstruct _bitcoinTransaction noattr)) field tulong))
      (Scall None
        (Evar _simplicity_write64 (Tfunction
          (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
        [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'2 tulong])).

Lemma bitcoin_tx_totalInputValue : bitcoin_field_at _bitcoinTransaction _totalInputValue 432.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_tx_totalOutputValue : bitcoin_field_at _bitcoinTransaction _totalOutputValue 440.
Proof. vm_compute; reflexivity. Qed.

Lemma exec_bitcoin_tx64_mid field delta e le mc me bd dbase be ebase bt tbase (x : int64) :
  bitcoin_field_at _bitcoinTransaction field delta -> 0 <= delta <= 480 ->
  e!_simplicity_write64 = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  0 <= tbase -> tbase + 488 <= Ptrofs.max_unsigned ->
  Mem.load Mptr mc be ebase = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Mem.load Mint64 mc bt (tbase + delta) = Some (Vlong x) ->
  Clight2.eval_funcall bitcoin_ge mc (Internal jets.f_simplicity_write64)
    [Vptr bd (Ptrofs.repr dbase); Vlong x] E0 me Vundef ->
  Clight2.exec_stmt bitcoin_ge e le mc (bitcoin_tx64_mid field) E0
    (PTree.set _t'2 (Vlong x) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le)) me Out_normal.
Proof.
  intros HField HDelta HW HEnv HDst He HE0 Ht HtM HL HLv HCall.
  unfold bitcoin_tx64_mid.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
    (le1 := PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le).
  - eapply exec_bitcoin_env_ptr with (pdelta := 0);
      [exact bitcoin_txEnv_tx|exact HEnv|exact He|lia|lia|].
    replace (ebase + 0) with ebase by lia. exact HL.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
      (le1 := PTree.set _t'2 (Vlong x) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le)).
    + apply exec_set.
      eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := delta) (chunk := Mint64).
      * reflexivity.
      * exact HField.
      * reflexivity.
      * apply eval_bitcoin_deref_struct. apply PTree.gss.
      * rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HLv].
    + replace (PTree.set _t'2 (Vlong x) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le))
        with (set_opttemp None Vundef
          (PTree.set _t'2 (Vlong x) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le))) by reflexivity.
      eapply exec_bitcoin_helper_call with (id := _simplicity_write64) (f := jets.f_simplicity_write64).
      * unfold bitcoin_core_helpers. simpl. tauto.
      * exact HW.
      * eapply eval_Econs.
        -- apply eval_Etempvar. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. exact HDst.
        -- reflexivity.
        -- eapply eval_Econs; [apply eval_Etempvar; apply PTree.gss|reflexivity|apply eval_Enil].
      * reflexivity.
      * exact HCall.
Qed.

Definition bitcoin_tx64_env_rep delta (total : Bitcoin.env -> Z)
    (m : mem) (env : val) (environment : Bitcoin.env) (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt tbase value,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= tbase /\ tbase + 488 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr tbase)) /\
    Mem.load Mint64 m bt (tbase + delta) = Some (Vlong value) /\
    Int64.unsigned value = total environment mod Int64.modulus /\
    fp = [(be, ebase, ebase + 8); (bt, tbase + delta, tbase + delta + 8)].

Lemma decode_wide64_unsigned v :
  decode_wide W64 (Int64.zero_ext 64 v) = fw6 (Int64.unsigned v).
Proof.
  unfold decode_wide, fw6. change (wide_log W64) with 6%nat.
  rewrite Int64.zero_ext_above by (change Int64.zwordsize with 64; lia). reflexivity.
Qed.

(** C caches Word64 totals modulo 2^64, rather than an unbounded integer
    total.  This also covers signed representatives and aggregate overflow. *)
Lemma fw6_mod64 z : fw6 (z mod Int64.modulus) = fw6 z.
Proof. exact (word_fromZ_mod 6 z). Qed.

Lemma fw6_sub_mod64 x y :
  fw6 (x mod Int64.modulus - y mod Int64.modulus) = fw6 (x - y).
Proof.
  rewrite <- (fw6_mod64 (x mod Int64.modulus - y mod Int64.modulus)).
  rewrite <- Zminus_mod. apply fw6_mod64.
Qed.

Lemma bitcoin_tx64_getter_local_spec f field delta total
    (spec : tySem Ty.Unit -> Bitcoin.env -> option (tySem Word64)) :
  bitcoin_wrapper_shape f (bitcoin_simple_rest (bitcoin_tx64_mid field)) ->
  bitcoin_field_at _bitcoinTransaction field delta -> 0 <= delta <= 480 ->
  (forall environment, spec tt environment = Some (fw6 (total environment))) ->
  application_jet_local_spec_sep f bitcoin_ge Bitcoin.env Ty.Unit Word64
    (bitcoin_tx64_env_rep delta total) spec.
Proof.
  intros HShape HField HDelta HSpec
    environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor [] fp
    (be & ebase & bt & tbase & value & HEnvVal & He0 & HeM & Ht0 & HtM & HLoad & HVal & HR & HFp)
    HSep HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env fp.
  assert (HC : Z.of_nat (bitSize Word64) = 64) by reflexivity.
  rewrite HC in HFrame.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (cells := encode (decode_wide W64 (Int64.zero_ext 64 value))).
  assert (HMid : forall ma mc bl,
    Mem.alloc m 0 16 = (ma, bl) -> Mem.storebytes ma bl 0 bytes = Some mc ->
    (forall chunk b ofs v', Mem.load chunk m b ofs = Some v' -> Mem.load chunk mc b ofs = Some v') ->
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mc b ofs kind p) ->
    write_frame_at mc bd dbase bw outedge cursor 64 ->
    exists le1 me,
      Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl)
        (bitcoin_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase) mc
        (bitcoin_tx64_mid field) E0 le1 me Out_normal /\
      write_effect mc me bd dbase bw outedge cursor 64 cells).
  { intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    destruct (bitcoin_write_wide_step W64 mc bd dbase bw outedge cursor value HFrameC)
      as (me & HCall & HEff).
    eexists _, me. split; [|exact HEff].
    eapply exec_bitcoin_tx64_mid with (be := be) (ebase := ebase) (bt := bt) (tbase := tbase)
      (x := value) (delta := delta).
    - exact HField.
    - exact HDelta.
    - reflexivity.
    - unfold bitcoin_wrapper_temps. apply PTree.gss.
    - unfold bitcoin_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact (HLP _ _ _ _ HLoad).
    - exact (HLP _ _ _ _ HVal).
    - exact HCall. }
  destruct (bitcoin_wrapper_layout_simple f
    (bitcoin_tx64_mid field) cells (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 64 bytes
    HShape HB HA HBytes ltac:(lia) HFrame
    (fun ma mc bl HAlloc HStore HLP HPP HFrameC =>
      match HMid ma mc bl HAlloc HStore HLP HPP HFrameC with
      | ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF (conj HL (conj HPm HV))))))) =>
          ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF
            (conj (fun chunk b ofs _ H1 H2 => HL chunk b ofs H1 H2) (conj HPm HV)))))))
      end))
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (fw6 (total environment)). split; [apply HSpec|]. split; [exact HCall|].
  split; [unfold cells in HCells; rewrite decode_wide64_unsigned, HR, fw6_mod64 in HCells; exact HCells|].
  split; [exact HPrefix|]. split; [exact HFields|]. exact HMem.
Qed.

Lemma bitcoin_total_input_value_getter_body :
  bitcoin_wrapper_shape f_simplicity_bitcoin_total_input_value
    (bitcoin_simple_rest (bitcoin_tx64_mid _totalInputValue)).
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma bitcoin_total_output_value_getter_body :
  bitcoin_wrapper_shape f_simplicity_bitcoin_total_output_value
    (bitcoin_simple_rest (bitcoin_tx64_mid _totalOutputValue)).
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Definition bitcoin_total_input_value_env_rep := bitcoin_tx64_env_rep 432
  (fun environment => sigTxTotalInValue (Bitcoin.envTx environment)).
Definition bitcoin_total_output_value_env_rep := bitcoin_tx64_env_rep 440
  (fun environment => sigTxTotalOutValue (Bitcoin.envTx environment)).

Theorem bitcoin_total_input_value_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_total_input_value bitcoin_ge Bitcoin.env
    Ty.Unit Word64 bitcoin_total_input_value_env_rep
    (fun a environment => @bitcoin_total_input_value_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply bitcoin_tx64_getter_local_spec;
    [exact bitcoin_total_input_value_getter_body|exact bitcoin_tx_totalInputValue|lia|].
  apply bitcoin_total_input_value_spec_sum.
Qed.

Theorem bitcoin_total_output_value_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_total_output_value bitcoin_ge Bitcoin.env
    Ty.Unit Word64 bitcoin_total_output_value_env_rep
    (fun a environment => @bitcoin_total_output_value_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply bitcoin_tx64_getter_local_spec;
    [exact bitcoin_total_output_value_getter_body|exact bitcoin_tx_totalOutputValue|lia|].
  apply bitcoin_total_output_value_spec_sum.
Qed.
