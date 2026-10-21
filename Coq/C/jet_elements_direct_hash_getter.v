(** A complete original-C getter for a midstate stored directly in txEnv.
    This shares the existing wrapper, writeHash execution and frame effects. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_copy_layout C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_uint32_array_init C.jet_application_sep.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval C.jet_elements_effects.
Require Import C.jet_elements_wrapper C.jet_elements_version_exec.
Require Import C.jet_elements_hash_helpers C.jet_elements_hash_write C.jet_elements_hash_getters.
Require Import C.jet_elements_script_cmr_local.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition elements_direct_hash_mid (field : ident) : statement :=
  Scall None
    (Evar _writeHash (Tfunction
      (Tcons (tptr (Tstruct _frameItem noattr))
        (Tcons (tptr (Tstruct _sha256_midstate noattr)) Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr));
     Eaddrof (Efield
       (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
       field (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr))].

Lemma exec_elements_direct_hash_mid e le mc me bd dbase be ebase field delta :
  e!_writeHash = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ebase -> 0 <= delta -> ebase + delta <= Ptrofs.max_unsigned ->
  elements_field_at _txEnv field delta ->
  Clight2.eval_funcall elements_ge mc (Internal f_writeHash)
    [Vptr bd (Ptrofs.repr dbase); Vptr be (Ptrofs.repr (ebase + delta))] E0 me Vundef ->
  Clight2.exec_stmt elements_ge e le mc (elements_direct_hash_mid field) E0 le me Out_normal.
Proof.
  intros HW HE HD He Hdelta HM Hfield HCall. unfold elements_direct_hash_mid.
  change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (elements_symbol_block _writeHash) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr be (Ptrofs.repr (ebase + delta))])
    (f := Internal f_writeHash) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact HW|exact elements_writeHash_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs with (v1 := Vptr be (Ptrofs.repr (ebase + delta)));
      [|reflexivity|apply eval_Enil].
    eapply eval_Eaddrof. rewrite <- (elements_ptr_add_repr ebase delta) by lia.
    eapply eval_elements_field_lvalue; [reflexivity|exact Hfield|].
    apply eval_elements_deref_struct. exact HE.
  - exact elements_writeHash_funct.
  - reflexivity.
  - exact HCall.
Qed.

Definition elements_direct_hash_rep {E : Set} (hash_of : E -> hash256) (delta : Z)
    (m : mem) (env : val) (environment : E) (fp : list (block * Z * Z)) : Prop :=
  exists be ebase,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
    uint32_array_at m be (ebase + delta) (hash256_reg (hash_of environment)) /\
    fp = [(be, ebase + delta, ebase + delta + 32)].

Theorem elements_direct_hash_getter_local {E : Set} (hash_of : E -> hash256) (delta : Z)
    (field : ident) (f : function)
    (spec : Ty.tySem Ty.Unit -> E -> option (Ty.tySem Word256))
    (Hspec : forall e, spec tt e = Some (from_hash256 (hash_of e)))
    (Hshape : elements_wrapper_shape f (elements_simple_rest (elements_direct_hash_mid field)))
    (Hfield : elements_field_at _txEnv field delta) (Hrange : 0 <= delta /\ delta + 32 <= 88) :
  application_jet_local_spec_sep f elements_ge E Ty.Unit Word256
    (elements_direct_hash_rep hash_of delta) spec.
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor [] fp
    (be & ebase & HEnvVal & He0 & HeM & HArr & HFp)
    HSep HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env fp.
  assert (HC : Z.of_nat (bitSize Word256) = 256) by reflexivity.
  rewrite Forall_forall in HSep.
  specialize (HSep (be, ebase + delta, ebase + delta + 32) (or_introl eq_refl)).
  cbn beta iota in HSep. rewrite HC in HSep, HFrame.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (hash := hash_of environment).
  assert (HLen : length (hash256_reg hash) = 8%nat) by exact (hash256_len hash).
  assert (HMid : forall ma mc bl,
    Mem.alloc m 0 16 = (ma, bl) -> Mem.storebytes ma bl 0 bytes = Some mc ->
    (forall chunk b ofs v, Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v) ->
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mc b ofs kind p) ->
    write_frame_at mc bd dbase bw outedge cursor 256 ->
    exists le1 me,
      Clight2.exec_stmt elements_ge (elements_version_locals bl)
        (elements_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase) mc
        (elements_direct_hash_mid field) E0 le1 me Out_normal /\
      write_effect mc me bd dbase bw outedge cursor 256 (hash_cells (hash256_reg hash))).
  { intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    destruct (eval_elements_writeHash_layout mc be (ebase + delta) bd dbase bw outedge cursor
      (hash256_reg hash) HLen ltac:(lia) ltac:(lia) HSep
      (fun i x Hi => HLP _ _ _ _ (HArr i x Hi)) HFrameC) as (me & HCall & HEff).
    exists (elements_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase), me.
    split; [|exact HEff].
    eapply exec_elements_direct_hash_mid with (be := be) (ebase := ebase) (delta := delta).
    - reflexivity.
    - unfold elements_wrapper_temps. apply PTree.gss.
    - unfold elements_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss.
    - lia.
    - lia.
    - lia.
    - exact Hfield.
    - exact HCall. }
  destruct (elements_wrapper_layout_simple f (elements_direct_hash_mid field)
    (hash_cells (hash256_reg hash)) (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 256 bytes
    Hshape HB HA HBytes ltac:(lia) HFrame
    (fun ma mc bl HAlloc HStore HLP HPP HFrameC =>
      match HMid ma mc bl HAlloc HStore HLP HPP HFrameC with
      | ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF (conj HL (conj HPm HV))))))) =>
          ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF
            (conj (fun chunk b ofs _ H1 H2 => HL chunk b ofs H1 H2) (conj HPm HV)))))))
      end)) as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (from_hash256 hash). split; [exact (Hspec environment)|]. split; [exact HCall|].
  split; [rewrite encode_from_hash256; exact HCells|].
  split; [exact HPrefix|]. split; [exact HFields|]. exact HMem.
Qed.
