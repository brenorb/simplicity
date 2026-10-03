(** Generic proof of the Bitcoin getters of the shape
      t = env->PTR; write32s(dst, t->HASH.s, 8);
    parametric in the logical environment type, so it applies to both the base
    [Bitcoin.env] and the extended environment of [jet_bitcoin_ext_prim]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_application_sep C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_uint32_array_init.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_write32s_layout C.jet_bitcoin_hash_write C.jet_bitcoin_hash_getters.
Require Import C.jet_bitcoin_script_cmr_local.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 60.

Definition hash_getter_rep {E : Set} (hash_of : E -> hash256) (pdelta hdelta psz : Z)
    (m : mem) (env : val) (e : E) (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt tbase,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= tbase /\ tbase + psz <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + pdelta) = Some (Vptr bt (Ptrofs.repr tbase)) /\
    uint32_array_at m bt (tbase + hdelta) (hash256_reg (hash_of e)) /\
    fp = [(be, ebase + pdelta, ebase + pdelta + 8); (bt, tbase + hdelta, tbase + hdelta + 32)].

Theorem bitcoin_hash_getter_write32s_local {E : Set} (hash_of : E -> hash256) (pdelta hdelta psz : Z)
    (ptrfield sid hashfield : ident) (f : function)
    (spec : Ty.tySem Ty.Unit -> E -> option (Ty.tySem Word256))
    (Hspec : forall e, spec tt e = Some (from_hash256 (hash_of e)))
    (Hshape : bitcoin_wrapper_shape f (bitcoin_simple_rest (bitcoin_hash_mid_write32s ptrfield sid hashfield)))
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
        (bitcoin_hash_mid_write32s ptrfield sid hashfield) E0 le1 me Out_normal /\
      write_effect mc me bd dbase bw outedge cursor 256 (hash_cells (hash256_reg hash))).
  { intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    destruct (eval_bitcoin_write_hash_array mc bt (tbase + hdelta) bd dbase bw outedge cursor
      (hash256_reg hash) HLen ltac:(lia) ltac:(lia) HArrSep
      (fun i x Hi => HLP _ _ _ _ (HArr i x Hi)) HFrameC) as (me & HCall & HEff).
    exists (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase))
      (bitcoin_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase)), me.
    split; [|exact HEff].
    eapply exec_bitcoin_hash_getter_write32s with (be := be) (ebase := ebase) (pdelta := pdelta)
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
    (bitcoin_hash_mid_write32s ptrfield sid hashfield)
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
