(** The Bitcoin sig_all_hash jet, [writeHash(dst, &env->sigAllHash)], against
    the literal program
      sigAllHash = (ctx8Init &&& (txHash &&& tapEnvHash) >>> ctx8Addn vector64)
               &&& primitive CurrentIndex >>> ctx8Addn vector4 >>> ctx8Finalize. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Maps Errors Events Cop.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_uint32_array_init.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_write32s_layout C.jet_bitcoin_hash_write C.jet_bitcoin_hash_getters.
Require Import C.jet_bitcoin_script_cmr_local C.jet_bitcoin_hash_getter_local C.jet_bitcoin_hash_helpers.
Require Import C.jet_bitcoin_call C.jet_bitcoin_hash_getter_writehash.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_spec C.jet_sha_finalize_spec C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_sha_hash_loop C.jet_sha_hash_words.
Require Import C.jet_bitcoin_words_hash C.jet_bitcoin_composite_hash C.jet_bitcoin_tx_hash.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 120.

(** ** The getter of a hash stored in the environment structure itself *)
Definition bitcoin_hash_mid_env_writeHash hashfield : statement :=
  Scall None
    (Evar _writeHash (Tfunction
      (Tcons (tptr (Tstruct _frameItem noattr))
        (Tcons (tptr (Tstruct _sha256_midstate noattr)) Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr));
     Eaddrof (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
       hashfield (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr))].

Lemma exec_bitcoin_env_hash_getter e le mc me bd dbase be ebase hashfield hdelta :
  e!_writeHash = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ebase -> 0 <= hdelta -> ebase + hdelta <= Ptrofs.max_unsigned ->
  bitcoin_field_at _txEnv hashfield hdelta ->
  Clight2.eval_funcall bitcoin_ge mc (Internal f_writeHash)
    [Vptr bd (Ptrofs.repr dbase); Vptr be (Ptrofs.repr (ebase + hdelta))] E0 me Vundef ->
  Clight2.exec_stmt bitcoin_ge e le mc (bitcoin_hash_mid_env_writeHash hashfield) E0 le me Out_normal.
Proof.
  intros HW HEnv HDst He Hd Hm HF HCall.
  unfold bitcoin_hash_mid_env_writeHash.
  change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block _writeHash) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr be (Ptrofs.repr (ebase + hdelta))])
    (f := Internal f_writeHash) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [exact HW|exact bitcoin_writeHash_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply eval_Etempvar; exact HDst|reflexivity|].
    eapply eval_Econs with (v1 := Vptr be (Ptrofs.repr (ebase + hdelta))); [|reflexivity|apply eval_Enil].
    eapply eval_Eaddrof.
    rewrite <- (bitcoin_ptr_add_repr ebase hdelta) by lia.
    eapply eval_bitcoin_field_lvalue; [reflexivity|exact HF|].
    apply eval_bitcoin_deref_struct. exact HEnv.
  - exact bitcoin_writeHash_funct.
  - reflexivity.
  - exact HCall.
Qed.

Definition env_hash_rep {E : Set} (hash_of : E -> hash256) (hdelta : Z)
    (m : mem) (env : val) (e : E) (fp : list (block * Z * Z)) : Prop :=
  exists be ebase,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    uint32_array_at m be (ebase + hdelta) (hash256_reg (hash_of e)) /\
    fp = [(be, ebase + hdelta, ebase + hdelta + 32)].

Theorem bitcoin_env_hash_getter_local {E : Set} (hash_of : E -> hash256) (hdelta : Z)
    (hashfield : ident) (f : function)
    (spec : Ty.tySem Ty.Unit -> E -> option (Ty.tySem Word256))
    (Hspec : forall e, spec tt e = Some (from_hash256 (hash_of e)))
    (Hshape : bitcoin_wrapper_shape f (bitcoin_simple_rest (bitcoin_hash_mid_env_writeHash hashfield)))
    (Hhf : bitcoin_field_at _txEnv hashfield hdelta)
    (Hh : 0 <= hdelta /\ hdelta + 32 <= 56) :
  application_jet_local_spec_sep f bitcoin_ge E Ty.Unit Word256 (env_hash_rep hash_of hdelta) spec.
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor [] fp
    (be & ebase & HEnvVal & He0 & HeM & HArr & HFp)
    HSep HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env fp.
  assert (HC : Z.of_nat (bitSize Word256) = 256) by reflexivity.
  assert (HArrSep0 : In (be, ebase + hdelta, ebase + hdelta + 32)
    [(be, ebase + hdelta, ebase + hdelta + 32)]) by (left; reflexivity).
  rewrite Forall_forall in HSep.
  specialize (HSep _ HArrSep0). cbn beta iota in HSep.
  rewrite HC in HSep.
  assert (HArrSep := HSep). clear HSep HArrSep0.
  rewrite HC in HFrame.
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
      Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl)
        (bitcoin_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase) mc
        (bitcoin_hash_mid_env_writeHash hashfield) E0 le1 me Out_normal /\
      write_effect mc me bd dbase bw outedge cursor 256 (hash_cells (hash256_reg hash))).
  { intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    destruct (eval_bitcoin_writeHash_layout mc be (ebase + hdelta) bd dbase bw outedge cursor
      (hash256_reg hash) HLen ltac:(lia) ltac:(lia) HArrSep
      (fun i x Hi => HLP _ _ _ _ (HArr i x Hi)) HFrameC) as (me & HCall & HEff).
    exists (bitcoin_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase), me.
    split; [|exact HEff].
    eapply exec_bitcoin_env_hash_getter with (be := be) (ebase := ebase) (hdelta := hdelta).
    - reflexivity.
    - unfold bitcoin_wrapper_temps. apply PTree.gss.
    - unfold bitcoin_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss.
    - lia.
    - lia.
    - lia.
    - exact Hhf.
    - exact HCall. }
  destruct (bitcoin_wrapper_layout_simple f
    (bitcoin_hash_mid_env_writeHash hashfield)
    (hash_cells (hash256_reg hash)) (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 256 bytes
    Hshape HB HA HBytes ltac:(lia) HFrame
    (fun ma mc bl HAlloc HStore HLP HPP HFrameC =>
      match HMid ma mc bl HAlloc HStore HLP HPP HFrameC with
      | ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF (conj HL (conj HPm HV))))))) =>
          ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF
            (conj (fun chunk b ofs _ H1 H2 => HL chunk b ofs H1 H2) (conj HPm HV)))))))
      end))
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (from_hash256 hash). split; [exact (Hspec environment)|]. split; [exact HCall|].
  split; [rewrite encode_from_hash256; exact HCells|].
  split; [exact HPrefix|]. split; [exact HFields|]. exact HMem.
Qed.

(** ** sigAllHash *)
Definition sig_all_hash_spec {alg : PF.Algebra} : PF.domain alg Ty.Unit Word256 :=
  let term := PF.CanonicalStructures.toAssertion alg in
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core
      (@AC.comp _ _ _ core
        (@AC.pair _ _ _ core (@sha256_ctx8_init_spec core)
          (@AC.pair _ _ _ core (@tx_hash_spec alg) (@tap_env_hash_spec alg)))
        (@ctx8_addn_spec 6 term))
      (@PF.Combinators.prim _ _ alg (BitcoinFull.Base Bitcoin.CurrentIndex)))
    (@AC.comp _ _ _ core (@ctx8_addn_spec 2 term) (@ctx8_finalize_spec term)).

Lemma sig_all_hash_spec_parametric : PF.Parametric (@sig_all_hash_spec).
Proof.
  intros alg1 alg2 R.
  pose proof (tx_hash_spec_parametric alg1 alg2 R) as HT.
  pose proof (tap_env_hash_spec_parametric alg1 alg2 R) as HE.
  destruct R as [R [HA [HP]]].
  set (RA := Alg.Assertion.Parametric.Pack HA).
  pose proof (ctx8_addn_spec_parametric 2 _ _ RA) as H2.
  pose proof (ctx8_addn_spec_parametric 6 _ _ RA) as H6.
  pose proof (ctx8_finalize_spec_parametric _ _ RA) as HF.
  destruct HA as [HC HAm]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold sig_all_hash_spec. cbv zeta.
  apply (Alg.comp_Parametric RC); [|apply (Alg.comp_Parametric RC); [exact H2|exact HF]].
  apply (Alg.pair_Parametric RC); [|apply HP].
  apply (Alg.comp_Parametric RC); [|exact H6].
  apply (Alg.pair_Parametric RC); [apply (sha256_ctx8_init_spec_parametric _ _ RC)|].
  apply (Alg.pair_Parametric RC); [exact HT|exact HE].
Qed.

Definition current_index_word (e : ext_environment) : Ty.tySem (Word 5) :=
  @fromZ (WordToZ 5) (Z.of_nat (Bitcoin.envIx (extBase e))).

Definition sig_all_hash_of (e : ext_environment) : hash256 :=
  sha256_bytes_of
    (vector_values (Word 3) 6 (from_hash256 (tx_hash_of e), from_hash256 (tap_env_hash_of e)) ++
     vector_values (Word 3) 2 (current_index_word e)).

Lemma sig_all_hash_spec_sem e :
  @sig_all_hash_spec fullalg tt e = Some (from_hash256 (sig_all_hash_of e)).
Proof.
  unfold sig_all_hash_spec. cbv zeta.
  rewrite fx_comp, fx_pair, fx_comp, fx_pair, fx_pair.
  rewrite (fx_core (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric).
  rewrite tx_hash_spec_sem, tap_env_hash_spec_sem, fx_prim.
  change (BitcoinFull.sem (BitcoinFull.Base Bitcoin.CurrentIndex) tt e) with
    (Some (current_index_word e)).
  cbv beta iota.
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 6 alg) (ctx8_addn_spec_parametric 6)), (ctx8_addn_option 6).
  destruct (init_hash_sem
    (vector_values (Word 3) 6 (from_hash256 (tx_hash_of e), from_hash256 (tap_env_hash_of e)) ++
     vector_values (Word 3) 2 (current_index_word e)))
    as (cf & H1 & H2).
  { rewrite app_length, !vector_values_length. reflexivity. }
  destruct (add_app_some _ _ _ _ H1) as (c1 & E1 & E2).
  use_add E1. cbv beta iota. rewrite fx_comp.
  rewrite (fx_assert (fun alg => @ctx8_addn_spec 2 alg) (ctx8_addn_spec_parametric 2)), (ctx8_addn_option 2).
  use_add E2.
  rewrite (fx_assert (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
  exact H2.
Qed.

Theorem bitcoin_sig_all_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_sig_all_hash bitcoin_ge ext_environment
    Ty.Unit Word256 (env_hash_rep sig_all_hash_of 16)
    (fun a environment => @sig_all_hash_spec fullalg a environment).
Proof.
  eapply bitcoin_env_hash_getter_local with (hashfield := _sigAllHash).
  - exact sig_all_hash_spec_sem.
  - getter_shape.
  - vm_compute; reflexivity.
  - lia.
Qed.
