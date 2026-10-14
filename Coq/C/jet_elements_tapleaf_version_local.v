(** Actual Elements tapleaf_version jet against the primitive
    TapleafVersion: [simplicity_write8(dst, env->taproot->leafVersion)]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option C.jet_elements_prim.
Require Import C.jet_exec C.jet_application_sep C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_spec C.jet_encoding.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_version_exec.
Require Import C.jet_elements_field_eval C.jet_elements_effects C.jet_elements_wrapper.
Require Import C.jet_elements_hash_getters C.jet_elements_transport C.jet_elements_call C.jet_elements_write8_step.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 60.

Definition elements_tapleaf_version_spec {alg : Primitive.Algebra} : alg Ty.Unit Word8 :=
  Primitive.Combinators.prim Elements.TapleafVersion.

Lemma elements_tapleaf_version_spec_sem (environment : Elements.env) :
  @elements_tapleaf_version_spec (PrimitivePrimSem option_Monad_Zero)
    tt environment = Some (fromZ (Byte.unsigned (tapleafVersion (Elements.envTap environment)))).
Proof. reflexivity. Qed.

Definition elements_tapleaf_version_mid : statement :=
  Ssequence (elements_env_ptr_stmt _taproot _elementsTapEnv)
    (Ssequence
      (Sset _t'2 (Efield (Ederef (Etempvar _t'1 (tptr (Tstruct _elementsTapEnv noattr)))
        (Tstruct _elementsTapEnv noattr)) _leafVersion tuchar))
      (Scall None
        (Evar _simplicity_write8 (Tfunction
          (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tuchar Tnil)) tvoid cc_default))
        [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'2 tuchar])).

Lemma elements_tapleaf_version_getter_body :
  elements_wrapper_shape f_simplicity_tapleaf_version
    (elements_simple_rest elements_tapleaf_version_mid).
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma elements_tapEnv_leafVersion : elements_field_at _elementsTapEnv _leafVersion 169.
Proof. vm_compute; reflexivity. Qed.

Lemma exec_elements_tapleaf_version_mid e le mc me bd dbase be ebase bt tbase (x : int) :
  e!_simplicity_write8 = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  0 <= tbase -> tbase + 176 <= Ptrofs.max_unsigned ->
  Mem.load Mptr mc be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Mem.load Mint8unsigned mc bt (tbase + 169) = Some (Vint x) ->
  Clight2.eval_funcall elements_ge mc (Internal jets.f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (Cop.cast_int_int I8 Unsigned x)] E0 me Vundef ->
  Clight2.exec_stmt elements_ge e le mc elements_tapleaf_version_mid E0
    (PTree.set _t'2 (Vint x) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le)) me Out_normal.
Proof.
  intros HW HEnv HDst He HE0 Ht HtM HL HLb HCall.
  unfold elements_tapleaf_version_mid.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
    (le1 := PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le).
  - eapply exec_elements_env_ptr; [exact elements_txEnv_taproot|exact HEnv|exact He|lia|lia|exact HL].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
      (le1 := PTree.set _t'2 (Vint x) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le)).
    + apply exec_set.
      eapply eval_elements_field_value with (sid := _elementsTapEnv) (delta := 169) (chunk := Mint8unsigned).
      * reflexivity.
      * exact elements_tapEnv_leafVersion.
      * reflexivity.
      * apply eval_elements_deref_struct. apply PTree.gss.
      * rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HLb].
    + replace (PTree.set _t'2 (Vint x) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le))
        with (set_opttemp None Vundef
          (PTree.set _t'2 (Vint x) (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le))) by reflexivity.
      eapply exec_elements_helper_call with (id := _simplicity_write8) (f := jets.f_simplicity_write8).
      * unfold elements_core_helpers. simpl. tauto.
      * exact HW.
      * eapply eval_Econs.
        -- apply eval_Etempvar. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. exact HDst.
        -- reflexivity.
        -- eapply eval_Econs; [apply eval_Etempvar; apply PTree.gss|simpl; unfold Cop.sem_cast; simpl; reflexivity|apply eval_Enil].
      * reflexivity.
      * exact HCall.
Qed.

Definition elements_tapleaf_version_env_rep (m : mem) (env : val) (e : Elements.env)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt tbase,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
    0 <= tbase /\ tbase + 176 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) /\
    Mem.load Mint8unsigned m bt (tbase + 169) = Some (Vint (Int.repr (Byte.unsigned (tapleafVersion (Elements.envTap e))))) /\
    fp = [(be, ebase + 8, ebase + 16)].

Lemma elements_tapleaf_version_cast_value v :
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

Theorem elements_tapleaf_version_local_spec :
  application_jet_local_spec_sep f_simplicity_tapleaf_version elements_ge Elements.env Ty.Unit Word8
    elements_tapleaf_version_env_rep
    (fun a environment => @elements_tapleaf_version_spec
      (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor [] fp
    (be & ebase & bt & tbase & HEnvVal & He0 & HeM & Ht0 & HtM & HLoad & HByte & HFp)
    HSep HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env fp.
  assert (HC : Z.of_nat (bitSize Word8) = 8) by reflexivity.
  rewrite HC in HFrame.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (v := Byte.unsigned (tapleafVersion (Elements.envTap environment))).
  pose proof (Byte.unsigned_range (tapleafVersion (Elements.envTap environment))) as Hv.
  change Byte.modulus with 256 in Hv. fold v in Hv.
  set (cells := encode (decode_word8 (Int64.repr (Int.unsigned
    (Cop.cast_int_int I8 Unsigned (Int.repr v)))))).
  assert (HMid : forall ma mc bl,
    Mem.alloc m 0 16 = (ma, bl) -> Mem.storebytes ma bl 0 bytes = Some mc ->
    (forall chunk b ofs v', Mem.load chunk m b ofs = Some v' -> Mem.load chunk mc b ofs = Some v') ->
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mc b ofs kind p) ->
    write_frame_at mc bd dbase bw outedge cursor 8 ->
    exists le1 me,
      Clight2.exec_stmt elements_ge (elements_version_locals bl)
        (elements_wrapper_temps f_simplicity_tapleaf_version (Vptr be (Ptrofs.repr ebase))
          bd dbase bs sbase) mc elements_tapleaf_version_mid E0 le1 me Out_normal /\
      write_effect mc me bd dbase bw outedge cursor 8 cells).
  { intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    destruct (elements_write8_step mc bd dbase bw outedge cursor (Cop.cast_int_int I8 Unsigned (Int.repr v)) HFrameC)
      as (me & HCall & HEff).
    pose proof (Int.zero_ext_idem) as _.
    assert (HCall' : Clight2.eval_funcall elements_ge mc (Internal jets.f_simplicity_write8)
      [Vptr bd (Ptrofs.repr dbase); Vint (Cop.cast_int_int I8 Unsigned (Int.repr v))] E0 me Vundef)
      by exact HCall.
    eexists _, me. split; [|exact HEff].
    eapply exec_elements_tapleaf_version_mid with (be := be) (ebase := ebase) (bt := bt) (tbase := tbase)
      (x := Int.repr v).
    - reflexivity.
    - unfold elements_wrapper_temps. apply PTree.gss.
    - unfold elements_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact (HLP _ _ _ _ HLoad).
    - exact (HLP _ _ _ _ HByte).
    - exact HCall'. }
  destruct (elements_wrapper_layout_simple f_simplicity_tapleaf_version
    elements_tapleaf_version_mid cells (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 8 bytes
    elements_tapleaf_version_getter_body HB HA HBytes ltac:(lia) HFrame
    (fun ma mc bl HAlloc HStore HLP HPP HFrameC =>
      match HMid ma mc bl HAlloc HStore HLP HPP HFrameC with
      | ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF (conj HL (conj HPm HV))))))) =>
          ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF
            (conj (fun chunk b ofs _ H1 H2 => HL chunk b ofs H1 H2) (conj HPm HV)))))))
      end))
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (@fromZ (WordToZ 3) v). split; [reflexivity|]. split; [exact HCall|].
  split; [unfold cells in HCells; rewrite elements_tapleaf_version_cast_value in HCells by lia; exact HCells|].
  split; [exact HPrefix|]. split; [exact HFields|]. exact HMem.
Qed.
