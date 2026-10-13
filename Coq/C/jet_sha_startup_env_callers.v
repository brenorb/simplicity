(** Environment-reading hash jets with the global-object obligations removed
    from the caller's side of the environment relation. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_exec C.jet_memcpy_model C.jet_bitmachine_rep C.jet_application_sep.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_output_layout C.jet_output_layout_step C.jet_write_layout C.jet_encoding.
Require Import C.jet_constant_layout C.jet_wide C.jet_complement_wide_layout.
Require Import C.jet_read32s_layout C.jet_write32s_layout C.jet_uint32_array_init C.jet_sha256_iv_init.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_transport C.jet_sha_compress_call C.jet_sha_block_local.
Require Import C.jet_sha_ctx8_model C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep.
Require Import C.jet_sha_uchars_exec C.jet_sha_hash_exec C.jet_sha_finalize_exec.
Require Import C.jet_sha_add_n_init C.jet_sha_add_n_calls C.jet_sha_add_n_exec C.jet_sha_ctx8_add_jets.
Require Import C.jet_sha_ctx8_finalize_jet.
Require Import C.jet_sha_tapdata_prep C.jet_sha_tapdata_jet.
Require Import C.jet_sha_ctx_abs C.jet_sha_ctxi C.jet_sha_tagged_ctx C.jet_sha_hash_io.
Require Import C.jet_bitcoin_make_tapleaf_exec.
Require Import C.jet_bitcoin_effects C.jet_bitcoin_env_load.
Require Import C.jet_sha_indexed_exec C.jet_sha_index_eval C.jet_sha_steps.
Require Import C.jet_forWhile_seq C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim.
Require Import C.jet_bitcoin_words_hash C.jet_bitcoin_composite_hash.
Require Import C.jet_bitcoin_vh_hash_spec C.jet_bitcoin_vh_hash_prep.
Require Import C.jet_bitcoin_vh_hash_spec C.jet_bitcoin_vh_hash_prep C.jet_bitcoin_output_hash_jet.
Require Import C.jet_bitcoin_input_utxo_hash_jet.
Require Import C.jet_sha_u32be_exec C.jet_sha_ctxi_u32 C.jet_bitcoin_ctx_hash_spec C.jet_bitcoin_tx_hash.
Require Import C.jet_bitcoin_build_tapleaf_spec C.jet_bitcoin_input_hash_spec.
Require Import C.jet_buffer_input C.jet_read8s_layout C.jet_word32_chunks C.jet_readBit_layout.
Require Import C.jet_bitcoin_output_hash_jet C.jet_bitcoin_input_utxo_hash_jet C.jet_bitcoin_input_hash_jet.
Require Import C.jet_clight_forward C.jet_sha_initial_globals.
Require Import C.jet_sha_startup_globals C.jet_sha_startup_state.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.


(** ** The caller's side of the environment relations

    The three environment-reading hash jets take a representation relation
    that contains [sha_globals_ok] and lists the two global objects in the
    footprint the caller must keep apart from the output frame.  Neither is
    an input requirement: both follow from the startup invariant.  Here the
    caller supplies the representation only *modulo* those facts (it may
    assume [sha_globals_ok] when establishing it) and a footprint without the
    global objects; their separation from the output frame is derived. *)
Definition sha_global_footprint : list (block * Z * Z) :=
  [(sha_symbol_block _simplicity_sha256_compression, 0, 8);
   (sha_symbol_block _sha256_max_counter, 0, 8)].

Definition sha_env_rep_modulo_globals {E : Set}
    (rep : mem -> val -> E -> list (block * Z * Z) -> Prop)
    (m : mem) (env : val) (e : E) (fp : list (block * Z * Z)) : Prop :=
  sha_globals_ok m -> rep m env e (fp ++ sha_global_footprint).

Definition sha_startup_env_spec (f : function) (E : Set) (A B : Ty)
    (env_rep : mem -> val -> E -> list (block * Z * Z) -> Prop)
    (spec : A -> E -> option B) : Prop :=
  forall logical_env env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A) fp,
    sha_startup_state m ->
    sha_env_rep_modulo_globals env_rep m env logical_env fp ->
    Forall (fun '(b, lo, hi) => out_sep bd dbase bw outedge cursor (Z.of_nat (bitSize B)) b lo hi) fp ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    exists mf value,
      spec a logical_env = Some value /\
      Clight2.eval_funcall sha_ge m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
        E0 mf (Vint Int.one) /\
      frame_output_cells_at mf bw outedge cursor (encode value) /\
      write_prefix_at m mf bw outedge cursor /\
      frame_fields_at mf bd dbase bw outedge (cursor - Z.of_nat (bitSize B)) /\
      (forall chunk b ofs, Mem.valid_block m b ->
        (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
        (b <> bw \/
          ofs + size_chunk chunk <= outedge + 8 * ((cursor - Z.of_nat (bitSize B)) / 64) \/
          write_word_address outedge cursor + 8 <= ofs) ->
        Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
      sha_startup_state mf.

Theorem sha_startup_env_from_sep f (E : Set) A B env_rep spec :
  64 < Z.of_nat (bitSize B) ->
  application_jet_local_spec_sep f sha_ge E A B env_rep spec ->
  sha_startup_env_spec f E A B env_rep spec.
Proof.
  intros HWide HLocal logical_env env m bd dbase bs sbase bi bw edge outedge cursor rc a fp
    HState HRep HSep HBase HAlign HFields HCursor HMax HInput HOutput.
  destruct (sha_write_frame_global_separation m bd dbase bw outedge cursor
    (Z.of_nat (bitSize B))
    (sha_persistent_globals_original m (proj1 HState)) ltac:(lia) HOutput)
    as [HFD [HWD [HFC HWC]]].
  assert (HSepAll : Forall (fun '(b, lo, hi) =>
      out_sep bd dbase bw outedge cursor (Z.of_nat (bitSize B)) b lo hi)
      (fp ++ sha_global_footprint)).
  { apply Forall_app. split; [exact HSep|].
    unfold sha_global_footprint.
    apply Forall_cons; [split; left; congruence|].
    apply Forall_cons; [split; left; congruence|]. apply Forall_nil. }
  exact (sha_startup_application_from_sep f E A B env_rep spec HWide HLocal
    logical_env env m bd dbase bs sbase bi bw edge outedge cursor rc a
    (fp ++ sha_global_footprint) HState (HRep (sha_startup_state_globals m HState))
    HSepAll HBase HAlign HFields HCursor HMax HInput HOutput).
Qed.

Theorem bitcoin_output_hash_startup_env_spec : memcpy_model ->
  sha_startup_env_spec f_simplicity_bitcoin_output_hash ext_environment
    (Word 5) (Ty.Sum Ty.Unit (Word 8)) output_hash_rep
    (fun a e => @vh_hash_spec (BitcoinFull.Base Bitcoin.OutputValue)
      (BitcoinFull.Base Bitcoin.OutputScriptHash) fullalg a e).
Proof.
  intros Hmodel. apply sha_startup_env_from_sep; [vm_compute; reflexivity|exact (bitcoin_output_hash_local_spec Hmodel)].
Qed.

Theorem bitcoin_input_utxo_hash_startup_env_spec : memcpy_model ->
  sha_startup_env_spec f_simplicity_bitcoin_input_utxo_hash ext_environment
    (Word 5) (Ty.Sum Ty.Unit (Word 8)) input_utxo_hash_rep
    (fun a e => @vh_hash_spec (BitcoinFull.Base Bitcoin.InputValue)
      (BitcoinFull.Ext BitcoinExt.InputScriptHash) fullalg a e).
Proof.
  intros Hmodel. apply sha_startup_env_from_sep; [vm_compute; reflexivity|exact (bitcoin_input_utxo_hash_local_spec Hmodel)].
Qed.

Theorem bitcoin_input_hash_startup_env_spec : memcpy_model ->
  sha_startup_env_spec f_simplicity_bitcoin_input_hash ext_environment
    (Word 5) (Ty.Sum Ty.Unit (Word 8)) input_hash_rep
    (fun a e => @input_hash_spec fullalg a e).
Proof.
  intros Hmodel. apply sha_startup_env_from_sep; [vm_compute; reflexivity|exact (bitcoin_input_hash_local_spec Hmodel)].
Qed.
