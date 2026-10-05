(** Actual Bitcoin tx_is_final jet against the literal canonical
    TimeLock.txIsFinal loop.  C: [writeBit(dst, env->tx->isFinal)]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_exec C.jet_application_sep C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_spec C.jet_encoding.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_steps.
Require Import C.jet_bitcoin_fee_local C.jet_bitcoin_is_final_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

Definition bool_int (b : bool) : int := if b then Int.one else Int.zero.

Definition bitcoin_tx_is_final_mid : statement :=
  Ssequence (bitcoin_env_tx_set _t'1)
    (Ssequence
      (Sset _t'2 (Efield (Ederef (Etempvar _t'1 (tptr (Tstruct _bitcoinTransaction noattr)))
        (Tstruct _bitcoinTransaction noattr)) _isFinal tbool))
      (Scall None
        (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil))
          tbool cc_default))
        [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'2 tbool])).

Lemma bitcoin_tx_isFinal : bitcoin_field_at _bitcoinTransaction _isFinal 480.
Proof. vm_compute; reflexivity. Qed.

Lemma exec_bitcoin_tx_is_final_mid e le mc me bd dbase be ebase bt tbase (b : bool) :
  e!_writeBit = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  0 <= tbase -> tbase + 488 <= Ptrofs.max_unsigned ->
  Mem.load Mptr mc be ebase = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Mem.load Mint8unsigned mc bt (tbase + 480) = Some (Vint (bool_int b)) ->
  Clight2.eval_funcall bitcoin_ge mc (Internal jets.f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bool_int b)] E0 me (Vint (bool_int b)) ->
  Clight2.exec_stmt bitcoin_ge e le mc bitcoin_tx_is_final_mid E0
    (PTree.set _t'2 (Vint (bool_int b)) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le))
    me Out_normal.
Proof.
  intros HW HEnv HDst He HE0 Ht HtM HL HLb HCall.
  unfold bitcoin_tx_is_final_mid.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
  { eapply exec_bitcoin_env_tx_set; [exact HEnv|exact He|exact HE0|exact HL]. }
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
    (le1 := PTree.set _t'2 (Vint (bool_int b)) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le)).
  { apply exec_set.
    eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := 480)
      (chunk := Mint8unsigned).
    - reflexivity.
    - exact bitcoin_tx_isFinal.
    - reflexivity.
    - apply eval_bitcoin_deref_struct. apply PTree.gss.
    - rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HLb]. }
  refine (exec_bitcoin_helper_call _ _ _ None _writeBit jets.f_writeBit
    _ _ _ _ _ (Vint (bool_int b)) _ _ _ _ _ _).
  - unfold bitcoin_core_helpers. simpl. tauto.
  - exact HW.
  - eapply eval_Econs.
    + apply eval_Etempvar. repeat rewrite PTree.gso by discriminate. exact HDst.
    + reflexivity.
    + eapply eval_Econs with (v1 := Vint (bool_int b)).
      * apply eval_Etempvar. apply PTree.gss.
      * destruct b; reflexivity.
      * apply eval_Enil.
  - reflexivity.
  - destruct b; exact HCall.
Qed.

Definition bitcoin_tx_is_final_env_rep (m : mem) (env : val) (environment : Bitcoin.env)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt tbase,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= tbase /\ tbase + 488 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr tbase)) /\
    Mem.load Mint8unsigned m bt (tbase + 480) =
      Some (Vint (bool_int (forallb sequence_final (sigTxIn (Bitcoin.envTx environment))))) /\
    fp = [(be, ebase, ebase + 8); (bt, tbase + 480, tbase + 481)].

Lemma bitcoin_tx_is_final_getter_body :
  bitcoin_wrapper_shape f_simplicity_bitcoin_tx_is_final
    (bitcoin_simple_rest bitcoin_tx_is_final_mid).
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma encode_fromBool (b : bool) : @encode Bit (Bit.fromBool b) = [Some b].
Proof. destruct b; reflexivity. Qed.

Theorem bitcoin_tx_is_final_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tx_is_final bitcoin_ge Bitcoin.env Ty.Unit Bit
    bitcoin_tx_is_final_env_rep
    (fun a environment => @bitcoin_tx_is_final_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor [] fp
    (be & ebase & bt & tbase & HEnvVal & He0 & HeM & Ht0 & HtM & HLoad & HVal & HFp)
    HSep HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env fp.
  set (b := forallb sequence_final (sigTxIn (Bitcoin.envTx environment))) in *.
  assert (HC : Z.of_nat (bitSize Bit) = 1) by reflexivity.
  rewrite HC in HFrame.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  assert (HMid : forall ma mc bl,
    Mem.alloc m 0 16 = (ma, bl) -> Mem.storebytes ma bl 0 bytes = Some mc ->
    (forall chunk b' ofs v', Mem.load chunk m b' ofs = Some v' -> Mem.load chunk mc b' ofs = Some v') ->
    (forall b' ofs kind p, Mem.perm m b' ofs kind p -> Mem.perm mc b' ofs kind p) ->
    write_frame_at mc bd dbase bw outedge cursor 1 ->
    exists le1 me,
      Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl)
        (bitcoin_wrapper_temps f_simplicity_bitcoin_tx_is_final (Vptr be (Ptrofs.repr ebase))
          bd dbase bs sbase) mc bitcoin_tx_is_final_mid E0 le1 me Out_normal /\
      write_effect mc me bd dbase bw outedge cursor 1 [Some b]).
  { intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    destruct (bitcoin_writeBit_step mc bd dbase bw outedge cursor b HFrameC)
      as (me & HCall & HEff).
    eexists _, me. split; [|exact HEff].
    eapply exec_bitcoin_tx_is_final_mid with (be := be) (ebase := ebase) (bt := bt) (tbase := tbase)
      (b := b).
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
  destruct (bitcoin_wrapper_layout_simple f_simplicity_bitcoin_tx_is_final
    bitcoin_tx_is_final_mid [Some b] (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 1 bytes
    bitcoin_tx_is_final_getter_body HB HA HBytes ltac:(lia) HFrame
    (fun ma mc bl HAlloc HStore HLP HPP HFrameC =>
      match HMid ma mc bl HAlloc HStore HLP HPP HFrameC with
      | ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF (conj HL (conj HPm HV))))))) =>
          ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF
            (conj (fun chunk b' ofs _ H1 H2 => HL chunk b' ofs H1 H2) (conj HPm HV)))))))
      end))
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (Bit.fromBool b).
  split; [apply bitcoin_tx_is_final_spec_value|]. split; [exact HCall|].
  split; [rewrite encode_fromBool; exact HCells|].
  split; [exact HPrefix|]. split; [exact HFields|]. exact HMem.
Qed.
