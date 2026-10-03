(** Generic proof of the Bitcoin getters of the shape
      t = env->PTR; writeHash(dst, &t->HASH);
    (internal_key), parametric in the logical environment type. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_application_sep C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_uint32_array_init.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_write32s_layout C.jet_bitcoin_hash_write C.jet_bitcoin_hash_getters.
Require Import C.jet_bitcoin_script_cmr_local C.jet_bitcoin_hash_getter_local C.jet_bitcoin_hash_helpers.
From compcert Require Import Cop.
Require Import C.jet_bitcoin_call.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 60.

Lemma exec_bitcoin_hash_getter_writeHash e le mc me bd dbase be ebase bt tbase
    ptrfield pdelta sid hashfield hdelta :
  e!_writeHash = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ebase -> 0 <= pdelta -> ebase + pdelta <= Ptrofs.max_unsigned ->
  0 <= tbase -> 0 <= hdelta -> tbase + hdelta <= Ptrofs.max_unsigned ->
  bitcoin_field_at _txEnv ptrfield pdelta -> bitcoin_field_at sid hashfield hdelta ->
  Mem.load Mptr mc be (ebase + pdelta) = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Clight2.eval_funcall bitcoin_ge mc (Internal f_writeHash)
    [Vptr bd (Ptrofs.repr dbase); Vptr bt (Ptrofs.repr (tbase + hdelta))] E0 me Vundef ->
  Clight2.exec_stmt bitcoin_ge e le mc (bitcoin_hash_mid_writeHash ptrfield sid hashfield) E0
    (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le) me Out_normal.
Proof.
  intros HW HEnv HDst He H0 HD Ht Hd Hm HF1 HF2 HL HCall.
  unfold bitcoin_hash_mid_writeHash.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
    (le1 := PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le).
  - eapply exec_bitcoin_env_ptr; [exact HF1|exact HEnv|exact He|exact H0|exact HD|exact HL].
  - eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block _writeHash) Ptrofs.zero)
      (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bt (Ptrofs.repr (tbase + hdelta))])
      (f := Internal f_writeHash) (vres := Vundef).
    + reflexivity.
    + eapply eval_Elvalue.
      * apply eval_Evar_global; [exact HW|exact bitcoin_writeHash_symbol].
      * apply deref_loc_reference; reflexivity.
    + eapply eval_Econs; [apply eval_Etempvar; rewrite PTree.gso by discriminate; exact HDst|reflexivity|].
      eapply eval_Econs with (v1 := Vptr bt (Ptrofs.repr (tbase + hdelta))); [|reflexivity|apply eval_Enil].
      eapply eval_Eaddrof.
      rewrite <- (bitcoin_ptr_add_repr tbase hdelta) by lia.
      eapply eval_bitcoin_field_lvalue; [reflexivity|exact HF2|].
      apply eval_bitcoin_deref_struct. apply PTree.gss.
    + exact bitcoin_writeHash_funct.
    + reflexivity.
    + exact HCall.
Qed.

Theorem bitcoin_hash_getter_writeHash_local {E : Set} (hash_of : E -> hash256) (pdelta hdelta psz : Z)
    (ptrfield sid hashfield : ident) (f : function)
    (spec : Ty.tySem Ty.Unit -> E -> option (Ty.tySem Word256))
    (Hspec : forall e, spec tt e = Some (from_hash256 (hash_of e)))
    (Hshape : bitcoin_wrapper_shape f (bitcoin_simple_rest (bitcoin_hash_mid_writeHash ptrfield sid hashfield)))
    (Hpf : bitcoin_field_at _txEnv ptrfield pdelta) (Hhf : bitcoin_field_at sid hashfield hdelta)
    (Hb : 0 <= pdelta /\ pdelta + 8 <= 56) (Hh : 0 <= hdelta /\ hdelta + 32 <= psz) :
  application_jet_local_spec_sep f bitcoin_ge E Ty.Unit Word256
    (hash_getter_rep hash_of pdelta hdelta psz) spec.
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor [] fp
    (be & ebase & bt & tbase & HEnvVal & He0 & HeM & Ht0 & HtM & HLoad & HArr & HFp)
    HSep HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env fp.
  assert (HC : Z.of_nat (bitSize Word256) = 256) by reflexivity.
  assert (HArrSep0 : In (bt, tbase + hdelta, tbase + hdelta + 32)
    [(be, ebase + pdelta, ebase + pdelta + 8); (bt, tbase + hdelta, tbase + hdelta + 32)])
    by (right; left; reflexivity).
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
        (bitcoin_hash_mid_writeHash ptrfield sid hashfield) E0 le1 me Out_normal /\
      write_effect mc me bd dbase bw outedge cursor 256 (hash_cells (hash256_reg hash))).
  { intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    destruct (eval_bitcoin_writeHash_layout mc bt (tbase + hdelta) bd dbase bw outedge cursor
      (hash256_reg hash) HLen ltac:(lia) ltac:(lia) HArrSep
      (fun i x Hi => HLP _ _ _ _ (HArr i x Hi)) HFrameC) as (me & HCall & HEff).
    exists (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase))
      (bitcoin_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase)), me.
    split; [|exact HEff].
    eapply exec_bitcoin_hash_getter_writeHash with (be := be) (ebase := ebase) (pdelta := pdelta)
      (hdelta := hdelta) (sid := sid) (hashfield := hashfield) (ptrfield := ptrfield).
    - reflexivity.
    - unfold bitcoin_wrapper_temps. apply PTree.gss.
    - unfold bitcoin_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Hpf.
    - exact Hhf.
    - exact (HLP _ _ _ _ HLoad).
    - exact HCall. }
  destruct (bitcoin_wrapper_layout_simple f
    (bitcoin_hash_mid_writeHash ptrfield sid hashfield)
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
