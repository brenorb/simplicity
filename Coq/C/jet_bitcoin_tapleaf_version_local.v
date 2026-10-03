(** Actual Bitcoin tapleaf_version jet against the extended primitive
    TapleafVersion: [simplicity_write8(dst, env->taproot->leafVersion)]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_exec C.jet_application_sep C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_spec C.jet_encoding.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_hash_getters C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_write8_step C.jet_bitcoin_ext_prim.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Import PrimitiveBitcoinExt.Primitive.Coercions.
Import PrimitiveBitcoinExt.Primitive.CanonicalStructures.
Local Opaque bitcoin_ge.
Set Default Timeout 60.

Definition bitcoin_tapleaf_version_spec {alg : PrimitiveBitcoinExt.Primitive.Algebra} : alg Ty.Unit Word8 :=
  PrimitiveBitcoinExt.Primitive.Combinators.prim BitcoinExt.TapleafVersion.

Lemma bitcoin_tapleaf_version_spec_sem (environment : ext_environment) :
  @bitcoin_tapleaf_version_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    tt environment = Some (fromZ (extTapleafVersion environment)).
Proof. reflexivity. Qed.

Definition bitcoin_tapleaf_version_mid : statement :=
  Ssequence (bitcoin_env_ptr_stmt _taproot _bitcoinTapEnv)
    (Ssequence
      (Sset _t'2 (Efield (Ederef (Etempvar _t'1 (tptr (Tstruct _bitcoinTapEnv noattr)))
        (Tstruct _bitcoinTapEnv noattr)) _leafVersion tuchar))
      (Scall None
        (Evar _simplicity_write8 (Tfunction
          (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tuchar Tnil)) tvoid cc_default))
        [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'2 tuchar])).

Lemma bitcoin_tapleaf_version_getter_body :
  bitcoin_wrapper_shape f_simplicity_bitcoin_tapleaf_version
    (bitcoin_simple_rest bitcoin_tapleaf_version_mid).
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma bitcoin_tapEnv_leafVersion : bitcoin_field_at _bitcoinTapEnv _leafVersion 169.
Proof. vm_compute; reflexivity. Qed.

Lemma exec_bitcoin_tapleaf_version_mid e le mc me bd dbase be ebase bt tbase (x : int) :
  e!_simplicity_write8 = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  0 <= tbase -> tbase + 176 <= Ptrofs.max_unsigned ->
  Mem.load Mptr mc be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Mem.load Mint8unsigned mc bt (tbase + 169) = Some (Vint x) ->
  Clight2.eval_funcall bitcoin_ge mc (Internal jets.f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (Cop.cast_int_int I8 Unsigned x)] E0 me Vundef ->
  Clight2.exec_stmt bitcoin_ge e le mc bitcoin_tapleaf_version_mid E0
    (PTree.set _t'2 (Vint x) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le)) me Out_normal.
Proof.
  intros HW HEnv HDst He HE0 Ht HtM HL HLb HCall.
  unfold bitcoin_tapleaf_version_mid.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
    (le1 := PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le).
  - eapply exec_bitcoin_env_ptr; [exact bitcoin_txEnv_taproot|exact HEnv|exact He|lia|lia|exact HL].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
      (le1 := PTree.set _t'2 (Vint x) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le)).
    + apply exec_set.
      eapply eval_bitcoin_field_value with (sid := _bitcoinTapEnv) (delta := 169) (chunk := Mint8unsigned).
      * reflexivity.
      * exact bitcoin_tapEnv_leafVersion.
      * reflexivity.
      * apply eval_bitcoin_deref_struct. apply PTree.gss.
      * rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HLb].
    + replace (PTree.set _t'2 (Vint x) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le))
        with (set_opttemp None Vundef
          (PTree.set _t'2 (Vint x) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le))) by reflexivity.
      eapply exec_bitcoin_helper_call with (id := _simplicity_write8) (f := jets.f_simplicity_write8).
      * unfold bitcoin_core_helpers. simpl. tauto.
      * exact HW.
      * eapply eval_Econs.
        -- apply eval_Etempvar. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. exact HDst.
        -- reflexivity.
        -- eapply eval_Econs; [apply eval_Etempvar; apply PTree.gss|simpl; unfold Cop.sem_cast; simpl; reflexivity|apply eval_Enil].
      * reflexivity.
      * exact HCall.
Qed.

Definition bitcoin_tapleaf_version_env_rep (m : mem) (env : val) (e : ext_environment)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt tbase,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= tbase /\ tbase + 176 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) /\
    Mem.load Mint8unsigned m bt (tbase + 169) = Some (Vint (Int.repr (extTapleafVersion e))) /\
    fp = [(be, ebase + 8, ebase + 16)].

Lemma bitcoin_tapleaf_version_cast_value v :
  0 <= v < 256 ->
  decode_word8 (Int64.repr (Int.unsigned (Cop.cast_int_int I8 Unsigned (Int.repr v)))) =
    @fromZ (WordToZ 3) v.
Proof.
  intros Hv. unfold decode_word8. f_equal.
  cbn [Cop.cast_int_int]. rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia).
  change (two_p 8) with 256.
  rewrite (Int.unsigned_repr v) by (change Int.max_unsigned with 4294967295; lia).
  rewrite (Z.mod_small v 256) by lia.
  rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  reflexivity.
Qed.

Theorem bitcoin_tapleaf_version_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tapleaf_version bitcoin_ge ext_environment Ty.Unit Word8
    bitcoin_tapleaf_version_env_rep
    (fun a environment => @bitcoin_tapleaf_version_spec
      (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor [] fp
    (be & ebase & bt & tbase & HEnvVal & He0 & HeM & Ht0 & HtM & HLoad & HByte & HFp)
    HSep HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env fp.
  assert (HC : Z.of_nat (bitSize Word8) = 8) by reflexivity.
  rewrite HC in HFrame.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (v := extTapleafVersion environment).
  pose proof (extTapleafVersion_range environment) as Hv. fold v in Hv.
  set (cells := encode (decode_word8 (Int64.repr (Int.unsigned
    (Cop.cast_int_int I8 Unsigned (Int.repr v)))))).
  assert (HMid : forall ma mc bl,
    Mem.alloc m 0 16 = (ma, bl) -> Mem.storebytes ma bl 0 bytes = Some mc ->
    (forall chunk b ofs v', Mem.load chunk m b ofs = Some v' -> Mem.load chunk mc b ofs = Some v') ->
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mc b ofs kind p) ->
    write_frame_at mc bd dbase bw outedge cursor 8 ->
    exists le1 me,
      Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl)
        (bitcoin_wrapper_temps f_simplicity_bitcoin_tapleaf_version (Vptr be (Ptrofs.repr ebase))
          bd dbase bs sbase) mc bitcoin_tapleaf_version_mid E0 le1 me Out_normal /\
      write_effect mc me bd dbase bw outedge cursor 8 cells).
  { intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    destruct (bitcoin_write8_step mc bd dbase bw outedge cursor (Cop.cast_int_int I8 Unsigned (Int.repr v)) HFrameC)
      as (me & HCall & HEff).
    pose proof (Int.zero_ext_idem) as _.
    assert (HCall' : Clight2.eval_funcall bitcoin_ge mc (Internal jets.f_simplicity_write8)
      [Vptr bd (Ptrofs.repr dbase); Vint (Cop.cast_int_int I8 Unsigned (Int.repr v))] E0 me Vundef)
      by exact HCall.
    eexists _, me. split; [|exact HEff].
    eapply exec_bitcoin_tapleaf_version_mid with (be := be) (ebase := ebase) (bt := bt) (tbase := tbase)
      (x := Int.repr v).
    - reflexivity.
    - unfold bitcoin_wrapper_temps. apply PTree.gss.
    - unfold bitcoin_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact (HLP _ _ _ _ HLoad).
    - exact (HLP _ _ _ _ HByte).
    - exact HCall'. }
  destruct (bitcoin_wrapper_layout_simple f_simplicity_bitcoin_tapleaf_version
    bitcoin_tapleaf_version_mid cells (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 8 bytes
    bitcoin_tapleaf_version_getter_body HB HA HBytes ltac:(lia) HFrame
    (fun ma mc bl HAlloc HStore HLP HPP HFrameC =>
      match HMid ma mc bl HAlloc HStore HLP HPP HFrameC with
      | ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF (conj HL (conj HPm HV))))))) =>
          ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF
            (conj (fun chunk b ofs _ H1 H2 => HL chunk b ofs H1 H2) (conj HPm HV)))))))
      end))
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (@fromZ (WordToZ 3) v). split; [reflexivity|]. split; [exact HCall|].
  split; [unfold cells in HCells; rewrite bitcoin_tapleaf_version_cast_value in HCells by lia; exact HCells|].
  split; [exact HPrefix|]. split; [exact HFields|]. exact HMem.
Qed.
