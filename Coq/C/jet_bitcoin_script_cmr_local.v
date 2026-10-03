(** Actual Bitcoin script_cmr jet against the literal canonical primitive
    ScriptCMR.  The C jet copies the eight words of
    [env->taproot->scriptCMR] with write32s; the abstract environment's
    script CMR is its hash256 registers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_uint32_array_init.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_write32s_layout C.jet_bitcoin_hash_write C.jet_bitcoin_hash_getters.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 30.

Definition bitcoin_script_cmr_spec {alg : Primitive.Algebra} : alg Ty.Unit Word256 :=
  Primitive.Combinators.prim Bitcoin.ScriptCMR.

Lemma bitcoin_script_cmr_spec_parametric :
  Primitive.Parametric (@bitcoin_script_cmr_spec).
Proof. intros alg1 alg2 R. apply prim_Parametric. Qed.

Lemma bitcoin_script_cmr_spec_sem (environment : Bitcoin.env) :
  @bitcoin_script_cmr_spec (PrimitivePrimSem option_Monad_Zero) tt environment =
    Some (from_hash256 (Bitcoin.envScriptCMR environment)).
Proof. reflexivity. Qed.

Lemma encode_word_pair n (hi lo : Ty.tySem (Word n)) :
  @encode (Word (S n)) (hi, lo) = @encode (Word n) hi ++ @encode (Word n) lo.
Proof. reflexivity. Qed.

(** The Simplicity encoding of a hash is the concatenation of its eight words. *)
Lemma encode_from_hash256 (h : hash256) :
  encode (from_hash256 h) = hash_cells (hash256_reg h).
Proof.
  destruct h as [regs Hlen].
  destruct regs as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 [|a7 [|a8 regs]]]]]]]]];
    cbn in Hlen; try discriminate.
  unfold hash_cells, uint32_word_cells, from_hash256; cbn [hash256_reg map concat].
  rewrite !encode_word_pair. rewrite ?app_nil_r, ?app_assoc. reflexivity.
Qed.

Lemma bitcoin_script_cmr_getter_body :
  bitcoin_wrapper_shape f_simplicity_bitcoin_script_cmr (bitcoin_simple_rest
    (bitcoin_hash_mid_write32s _taproot _bitcoinTapEnv _scriptCMR)).
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma bitcoin_tapEnv_scriptCMR_at : bitcoin_field_at _bitcoinTapEnv _scriptCMR 136.
Proof. exact bitcoin_tapEnv_scriptCMR. Qed.

Definition bitcoin_script_cmr_env_rep (m : mem) (env : val) (environment : Bitcoin.env)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt tbase,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= tbase /\ tbase + 176 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) /\
    uint32_array_at m bt (tbase + 136) (hash256_reg (Bitcoin.envScriptCMR environment)) /\
    fp = [(be, ebase + 8, ebase + 16); (bt, tbase + 136, tbase + 168)].

Theorem bitcoin_script_cmr_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_script_cmr bitcoin_ge Bitcoin.env Ty.Unit Word256
    bitcoin_script_cmr_env_rep
    (fun a environment => @bitcoin_script_cmr_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor [] fp
    (be & ebase & bt & tbase & HEnvVal & He0 & HeM & Ht0 & HtM & HLoad & HArr & HFp)
    HSep HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env fp.
  assert (HC : Z.of_nat (bitSize Word256) = 256) by reflexivity.
  assert (HArrSep : out_sep bd dbase bw outedge cursor 256 bt (tbase + 136) (tbase + 168)).
  { rewrite <- HC. exact (proj1 (Forall_forall _ _) HSep (bt, tbase + 136, tbase + 168)
      ltac:(simpl; auto)). }
  rewrite HC in HFrame.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (hash := Bitcoin.envScriptCMR environment).
  assert (HLen : length (hash256_reg hash) = 8%nat) by exact (hash256_len hash).
  assert (HArrSep' : out_sep bd dbase bw outedge cursor 256 bt (tbase + 136) (tbase + 136 + 32)).
  { replace (tbase + 136 + 32) with (tbase + 168) by lia. exact HArrSep. }
  assert (HMid : forall ma mc bl,
    Mem.alloc m 0 16 = (ma, bl) -> Mem.storebytes ma bl 0 bytes = Some mc ->
    (forall chunk b ofs v, Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v) ->
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mc b ofs kind p) ->
    write_frame_at mc bd dbase bw outedge cursor 256 ->
    exists le1 me,
      Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl)
        (bitcoin_wrapper_temps f_simplicity_bitcoin_script_cmr (Vptr be (Ptrofs.repr ebase))
          bd dbase bs sbase) mc
        (bitcoin_hash_mid_write32s _taproot _bitcoinTapEnv _scriptCMR) E0 le1 me Out_normal /\
      write_effect mc me bd dbase bw outedge cursor 256 (hash_cells (hash256_reg hash))).
  { intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    destruct (eval_bitcoin_write_hash_array mc bt (tbase + 136) bd dbase bw outedge cursor
      (hash256_reg hash) HLen ltac:(lia) ltac:(lia) HArrSep'
      (fun i x Hi => HLP _ _ _ _ (HArr i x Hi)) HFrameC) as (me & HCall & HEff).
    exists (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase))
      (bitcoin_wrapper_temps f_simplicity_bitcoin_script_cmr (Vptr be (Ptrofs.repr ebase))
        bd dbase bs sbase)), me.
    split; [|exact HEff].
    eapply exec_bitcoin_hash_getter_write32s with (be := be) (ebase := ebase) (pdelta := 8)
      (hdelta := 136) (sid := _bitcoinTapEnv) (hashfield := _scriptCMR) (ptrfield := _taproot).
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
    - exact bitcoin_txEnv_taproot.
    - exact bitcoin_tapEnv_scriptCMR.
    - exact (HLP _ _ _ _ HLoad).
    - exact HCall. }
  destruct (bitcoin_wrapper_layout_simple f_simplicity_bitcoin_script_cmr
    (bitcoin_hash_mid_write32s _taproot _bitcoinTapEnv _scriptCMR)
    (hash_cells (hash256_reg hash)) (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 256 bytes
    bitcoin_script_cmr_getter_body HB HA HBytes ltac:(lia) HFrame
    (fun ma mc bl HAlloc HStore HLP HPP HFrameC =>
      match HMid ma mc bl HAlloc HStore HLP HPP HFrameC with
      | ex_intro _ le1 (ex_intro _ me (conj HEx HEff)) =>
          ex_intro _ le1 (ex_intro _ me (conj HEx HEff))
      end))
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (from_hash256 hash). split; [reflexivity|]. split; [exact HCall|].
  split; [rewrite encode_from_hash256; exact HCells|].
  split; [exact HPrefix|]. split; [exact HFields|]. exact HMem.
Qed.
