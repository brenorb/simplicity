(** Actual Elements genesis_block_hash jet against primitive GenesisBlockHash
    (Haskell: [specificationTransaction GenesisBlockHash = primitive
    Prim.GenesisBlockHash]): [write32s(dst, env->genesisHash.s, 8)].  The
    hash is a field of the environment record itself, so no pointer is
    followed; the body is otherwise that of the pointer-field getters. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option C.jet_elements_prim.
Require Import C.jet_exec C.jet_frame_copy_layout C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_uint32_array_init C.jet_application_sep.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval C.jet_elements_effects.
Require Import C.jet_elements_wrapper C.jet_elements_version_exec.
Require Import C.jet_elements_write32s_exec C.jet_elements_write32s_layout C.jet_elements_hash_write.
Require Import C.jet_elements_hash_getters C.jet_elements_script_cmr_local.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Set Default Timeout 60.

Definition elements_genesis_hash_spec {alg : Primitive.Algebra} : alg Ty.Unit Word256 :=
  Primitive.Combinators.prim Elements.GenesisBlockHash.

Lemma elements_genesis_hash_spec_parametric :
  Primitive.Parametric (@elements_genesis_hash_spec).
Proof. intros alg1 alg2 R. apply prim_Parametric. Qed.

Definition elements_genesis_mid : statement :=
  Scall None
    (Evar _write32s (Tfunction
      (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr tuint) (Tcons tulong Tnil)))
      tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr));
     Efield (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
       _genesisHash (Tstruct _sha256_midstate noattr)) _s (tarray tuint 8);
     Econst_int (Int.repr 8) tint].

Lemma elements_genesis_hash_body :
  elements_wrapper_shape f_simplicity_genesis_block_hash (elements_simple_rest elements_genesis_mid).
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma elements_txEnv_genesisHash : elements_field_at _txEnv _genesisHash 16.
Proof. vm_compute; reflexivity. Qed.

Lemma eval_elements_genesis_array_arg e le m be ebase :
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
  0 <= ebase -> ebase + 16 <= Ptrofs.max_unsigned ->
  eval_expr elements_ge e le m
    (Efield (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
      _genesisHash (Tstruct _sha256_midstate noattr)) _s (tarray tuint 8))
    (Vptr be (Ptrofs.repr (ebase + 16))).
Proof.
  intros HE H0 HM.
  assert (Hr : Ptrofs.repr (ebase + 16) =
    Ptrofs.add (Ptrofs.repr (ebase + 16)) (Ptrofs.repr 0))
    by (rewrite Ptrofs.add_zero; reflexivity).
  rewrite Hr.
  eapply eval_elements_field_array with (sid := _sha256_midstate) (delta := 0);
    [reflexivity|exact elements_midstate_s|intros chunk; discriminate|reflexivity|].
  rewrite <- (elements_ptr_add_repr ebase 16) by lia.
  eapply eval_elements_field_struct; [reflexivity|exact elements_txEnv_genesisHash|].
  apply eval_elements_deref_struct; exact HE.
Qed.

Lemma exec_elements_genesis_mid e le mc me bd dbase be ebase :
  e!_write32s = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ebase -> ebase + 16 <= Ptrofs.max_unsigned ->
  Clight2.eval_funcall elements_ge mc (Internal f_write32s)
    [Vptr bd (Ptrofs.repr dbase); Vptr be (Ptrofs.repr (ebase + 16)); Vlong (Int64.repr 8)]
    E0 me Vundef ->
  Clight2.exec_stmt elements_ge e le mc elements_genesis_mid E0 le me Out_normal.
Proof.
  intros HW HEnv HDst He HM HCall. unfold elements_genesis_mid.
  change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (elements_symbol_block _write32s) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr be (Ptrofs.repr (ebase + 16));
      Vlong (Int64.repr 8)])
    (f := Internal f_write32s) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [exact HW|exact elements_write32s_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply eval_Etempvar; exact HDst|reflexivity|].
    eapply eval_Econs; [eapply eval_elements_genesis_array_arg; [exact HEnv|lia|lia]|reflexivity|].
    eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
  - exact elements_write32s_funct.
  - reflexivity.
  - exact HCall.
Qed.

Definition elements_genesis_hash_env_rep (m : mem) (env : val) (environment : Elements.env)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
    uint32_array_at m be (ebase + 16) (hash256_reg (Elements.envGenesisBlock environment)) /\
    fp = [(be, ebase + 16, ebase + 48)].

Theorem elements_genesis_block_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_genesis_block_hash elements_ge Elements.env
    Ty.Unit Word256 elements_genesis_hash_env_rep
    (fun a environment => @elements_genesis_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor [] fp
    (be & ebase & HEnvVal & He0 & HeM & HArr & HFp)
    HSep HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env fp.
  assert (HC : Z.of_nat (bitSize Word256) = 256) by reflexivity.
  rewrite Forall_forall in HSep.
  specialize (HSep (be, ebase + 16, ebase + 48) (or_introl eq_refl)). cbn beta iota in HSep.
  rewrite HC in HSep. rewrite HC in HFrame.
  assert (HArrSep : out_sep bd dbase bw outedge cursor 256 be (ebase + 16) (ebase + 16 + 32)).
  { replace (ebase + 16 + 32) with (ebase + 48) by lia. exact HSep. }
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (hash := Elements.envGenesisBlock environment).
  assert (HLen : length (hash256_reg hash) = 8%nat) by exact (hash256_len hash).
  assert (HMid : forall ma mc bl,
    Mem.alloc m 0 16 = (ma, bl) -> Mem.storebytes ma bl 0 bytes = Some mc ->
    (forall chunk b ofs v, Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v) ->
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mc b ofs kind p) ->
    write_frame_at mc bd dbase bw outedge cursor 256 ->
    exists le1 me,
      Clight2.exec_stmt elements_ge (elements_version_locals bl)
        (elements_wrapper_temps f_simplicity_genesis_block_hash (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase) mc
        elements_genesis_mid E0 le1 me Out_normal /\
      write_effect mc me bd dbase bw outedge cursor 256 (hash_cells (hash256_reg hash))).
  { intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    destruct (eval_elements_write_hash_array mc be (ebase + 16) bd dbase bw outedge cursor
      (hash256_reg hash) HLen ltac:(lia) ltac:(lia) HArrSep
      (fun i x Hi => HLP _ _ _ _ (HArr i x Hi)) HFrameC) as (me & HCall & HEff).
    exists (elements_wrapper_temps f_simplicity_genesis_block_hash (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase), me.
    split; [|exact HEff].
    eapply exec_elements_genesis_mid with (be := be) (ebase := ebase).
    - reflexivity.
    - unfold elements_wrapper_temps. apply PTree.gss.
    - unfold elements_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss.
    - lia.
    - lia.
    - exact HCall. }
  destruct (elements_wrapper_layout_simple f_simplicity_genesis_block_hash
    elements_genesis_mid
    (hash_cells (hash256_reg hash)) (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 256 bytes
    elements_genesis_hash_body HB HA HBytes ltac:(lia) HFrame
    (fun ma mc bl HAlloc HStore HLP HPP HFrameC =>
      match HMid ma mc bl HAlloc HStore HLP HPP HFrameC with
      | ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF (conj HL (conj HPm HV))))))) =>
          ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF
            (conj (fun chunk b ofs _ H1 H2 => HL chunk b ofs H1 H2) (conj HPm HV)))))))
      end))
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (from_hash256 hash). split; [reflexivity|]. split; [exact HCall|].
  split; [rewrite encode_from_hash256; exact HCells|].
  split; [exact HPrefix|]. split; [exact HFields|]. exact HMem.
Qed.
