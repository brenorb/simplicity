(** [readHash] and [writeHash] (bitcoinJets.c) in the SHA translation unit:
    each is one call to the core [read32s] / [write32s] with the eight words
    of a midstate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_read32s_layout C.jet_write32s_layout C.jet_uint32_array_init C.jet_encoding.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_transport C.jet_sha_add_n_init.
Require Import C.jet_sha_read_context_layout C.jet_sha_ctx8_finalize_jet.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Lemma hio_read32s_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _read32s = Some (sha_symbol_block _read32s).
Proof. vm_compute; reflexivity. Qed.
Lemma hio_read32s_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _read32s) Ptrofs.zero) =
    Some (Internal jets.f_read32s).
Proof. vm_compute; reflexivity. Qed.
Lemma hio_write32s_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _write32s = Some (sha_symbol_block _write32s).
Proof. vm_compute; reflexivity. Qed.
Lemma hio_write32s_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _write32s) Ptrofs.zero) =
    Some (Internal jets.f_write32s).
Proof. vm_compute; reflexivity. Qed.
Lemma hio_readHash_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _readHash = Some (sha_symbol_block _readHash).
Proof. vm_compute; reflexivity. Qed.
Lemma hio_readHash_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _readHash) Ptrofs.zero) =
    Some (Internal f_readHash).
Proof. vm_compute; reflexivity. Qed.
Lemma hio_writeHash_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _writeHash = Some (sha_symbol_block _writeHash).
Proof. vm_compute; reflexivity. Qed.
Lemma hio_writeHash_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _writeHash) Ptrofs.zero) =
    Some (Internal f_writeHash).
Proof. vm_compute; reflexivity. Qed.

Lemma hio_cast8 m : sem_cast (Vint (Int.repr 8)) tint tulong m = Some (Vlong (Int64.repr 8)).
Proof. vm_compute. reflexivity. Qed.

Local Opaque sha_ge.

(** The array of a midstate reached through a pointer temporary. *)
Lemma eval_sha_midstate_array e le m x b hbase :
  le!x = Some (Vptr b (Ptrofs.repr hbase)) ->
  eval_expr sha_ge e le m
    (Efield (Ederef (Etempvar x (tptr MID)) MID) _s (tarray tuint 8)) (Vptr b (Ptrofs.repr hbase)).
Proof.
  intros HX.
  assert (Hr : Ptrofs.repr hbase = Ptrofs.add (Ptrofs.repr hbase) (Ptrofs.repr 0))
    by (rewrite Ptrofs.add_zero; reflexivity).
  rewrite Hr.
  eapply eval_Elvalue.
  - eapply eval_Efield_struct with (delta := 0).
    + eapply eval_Elvalue; [eapply eval_Ederef; apply eval_Etempvar; exact HX|apply deref_loc_copy; reflexivity].
    + reflexivity.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
  - apply deref_loc_reference; reflexivity.
Qed.

Theorem eval_sha_readHash m bo output bf base bi edge cursor (xs : list (Ty.tySem (Word 5))) :
  length xs = 8%nat ->
  0 <= output -> output + 32 <= Ptrofs.max_unsigned -> (4 | output) ->
  Mem.range_perm m bo output (output + 32) Cur Writable ->
  bf <> bo -> bf <> bi -> bo <> bi ->
  frame_base_valid base -> 0 <= cursor -> cursor + 256 <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable ->
  (forall i x, nth_error xs i = Some x ->
    frame_input_word_at m bi edge (cursor + 32 * Z.of_nat i) x) ->
  exists mf,
    Clight2.eval_funcall sha_ge m (Internal f_readHash)
      [Vptr bo (Ptrofs.repr output); Vptr bf (Ptrofs.repr base)] E0 mf Vundef /\
    uint32_array_at mf bo output (map word32_array_value xs) /\
    frame_fields_at mf bf base bi edge (cursor + 256) /\
    (forall chunk b ofs,
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bo \/ ofs + size_chunk chunk <= output \/ output + 32 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HL HB HM HA HP Hfo Hfi Hoi Hbase HC Hmax HF HW HI.
  destruct (eval_read32s_layout m bo output bf base bi edge cursor xs HB
    ltac:(rewrite HL; change (4 * Z.of_nat 8) with 32; exact HM) HA
    ltac:(rewrite HL; change (4 * Z.of_nat 8) with 32; exact HP) Hfo Hfi Hoi Hbase HC
    ltac:(rewrite HL; change (32 * Z.of_nat 8) with 256; exact Hmax) HF HW HI)
    as (mf & HCall & HArr & HFld & HMem & HPerm & HVal).
  rewrite HL in HCall, HFld, HMem.
  change (Z.of_nat 8) with 8 in HCall. change (32 * Z.of_nat 8) with 256 in HFld.
  change (4 * Z.of_nat 8) with 32 in HMem.
  apply (sha_transport_call _ _ sg_in_read32s) in HCall.
  exists mf. split; [|split; [exact HArr|split; [exact HFld|split; [exact HMem|split; [exact HPerm|exact HVal]]]]].
  set (le := PTree.set _src (Vptr bf (Ptrofs.repr base))
    (PTree.set _h (Vptr bo (Ptrofs.repr output)) (create_undef_temps (fn_temps f_readHash)))).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le) (le2 := le)
    (m1 := m) (m2 := mf) (out := Out_normal).
  - constructor.
    + constructor.
    + cbn. repeat constructor; cbn; intuition discriminate.
    + intros i j HI0 HJ. cbn in HJ. contradiction.
    + constructor.
    + reflexivity.
  - unfold f_readHash. cbn [fn_body]. change le with (set_opttemp None Vundef le) at 2.
    eapply exec_Scall with (vf := Vptr (sha_symbol_block _read32s) Ptrofs.zero)
      (vargs := [Vptr bo (Ptrofs.repr output); Vlong (Int64.repr 8); Vptr bf (Ptrofs.repr base)])
      (f := Internal jets.f_read32s).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact hio_read32s_symbol]|].
      apply deref_loc_reference; reflexivity.
    + eapply eval_Econs; [apply eval_sha_midstate_array; reflexivity|reflexivity|].
      eapply eval_Econs; [apply eval_Econst_int|apply hio_cast8|].
      eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|apply eval_Enil].
    + exact hio_read32s_funct.
    + reflexivity.
    + exact HCall.
  - reflexivity.
  - reflexivity.
Qed.

Theorem eval_sha_writeHash m bh hbase bf base bw edge cursor xs :
  length xs = 8%nat -> 0 <= hbase -> hbase + 32 <= Ptrofs.max_unsigned ->
  bh <> bf -> bh <> bw -> uint32_array_at m bh hbase xs ->
  write_frame_at m bf base bw edge cursor 256 ->
  exists mf,
    Clight2.eval_funcall sha_ge m (Internal f_writeHash)
      [Vptr bf (Ptrofs.repr base); Vptr bh (Ptrofs.repr hbase)] E0 mf Vundef /\
    frame_output_cells_at mf bw edge cursor (uint32_word_cells xs) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - 256) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - 256) / 64)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HL H0 HM Hhf Hhw HA HF.
  destruct (eval_write32s_layout m bh hbase bf base bw edge cursor xs H0
    ltac:(rewrite HL; change (4 * Z.of_nat 8) with 32; exact HM) Hhf Hhw HA
    ltac:(rewrite HL; change (32 * Z.of_nat 8) with 256; exact HF))
    as (mf & HCall & HCells & HPrefix & HFields & HLoads & HPerm & HValid).
  rewrite HL in HCall, HFields, HLoads.
  change (Z.of_nat 8) with 8 in HCall. change (32 * Z.of_nat 8) with 256 in HFields, HLoads.
  apply (sha_transport_call _ _ sg_in_write32s) in HCall.
  exists mf. split; [|split; [exact HCells|split; [exact HPrefix|split; [exact HFields|
    split; [exact HLoads|split; [exact HPerm|exact HValid]]]]]].
  set (le := PTree.set _h (Vptr bh (Ptrofs.repr hbase))
    (PTree.set _dst (Vptr bf (Ptrofs.repr base)) (create_undef_temps (fn_temps f_writeHash)))).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le) (le2 := le)
    (m1 := m) (m2 := mf) (out := Out_normal).
  - constructor.
    + constructor.
    + cbn. repeat constructor; cbn; intuition discriminate.
    + intros i j HI0 HJ. cbn in HJ. contradiction.
    + constructor.
    + reflexivity.
  - unfold f_writeHash. cbn [fn_body]. change le with (set_opttemp None Vundef le) at 2.
    eapply exec_Scall with (vf := Vptr (sha_symbol_block _write32s) Ptrofs.zero)
      (vargs := [Vptr bf (Ptrofs.repr base); Vptr bh (Ptrofs.repr hbase); Vlong (Int64.repr 8)])
      (f := Internal jets.f_write32s).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact hio_write32s_symbol]|].
      apply deref_loc_reference; reflexivity.
    + eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
      eapply eval_Econs; [apply eval_sha_midstate_array; reflexivity|reflexivity|].
      eapply eval_Econs; [apply eval_Econst_int|apply hio_cast8|apply eval_Enil].
    + exact hio_write32s_funct.
    + reflexivity.
    + exact HCall.
  - reflexivity.
  - reflexivity.
Qed.
