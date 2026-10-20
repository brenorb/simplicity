(** Public names for the recovered original-C calculation contracts.
    The libc model and concrete initial SHA global values remain explicit. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_memcpy_model C.jet_frame_layout C.jet_input_layout C.jet_output_layout.
Require Import C.jet_write_layout C.jet_encoding C.jets_elements C.jet_elements_linkage.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_block_local.
Require Import C.jet_elements_issuance_calc_spec.
Require Import C.jet_entropy_local_local C.jet_entropy_frame_read.
Require Import C.jet_elements_support_sha_uchars_exec.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_entropy_local_spec (f : function)
    (spec : Ty.tySem entropy_input_type -> Ty.tySem Word256) : Prop :=
  forall env m bd dbase bs sbase bi bw edge outedge cursor rc (a : Ty.tySem entropy_input_type),
    Mem.load Mptr m (elements_symbol_block _simplicity_sha256_compression) 0 =
      Some (Vptr (elements_symbol_block _sha256_compression_portable) Ptrofs.zero) ->
    Mem.load Mint64 m (elements_symbol_block _sha256_max_counter) 0 = Some (Vlong sha_max_counter) ->
    frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
    0 <= rc -> rc + 544 <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge rc (@encode entropy_input_type a) ->
    write_frame_at m bd dbase bw outedge cursor 256 ->
    exists mf,
      Clight2.eval_funcall elements_ge m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
      frame_output_cells_at mf bw outedge cursor (@encode Word256 (spec a)) /\
      write_prefix_at m mf bw outedge cursor /\
      frame_fields_at mf bd dbase bw outedge (cursor - 256) /\
      (forall ch b ofs, Mem.valid_block m b ->
        (b <> bd \/ ofs + size_chunk ch <= dbase + 8 \/ dbase + 16 <= ofs) ->
        (b <> bw \/ ofs + size_chunk ch <= outedge + 8 * ((cursor - 256) / 64) \/
          write_word_address outedge cursor + 8 <= ofs) ->
        Mem.load ch mf b ofs = Mem.load ch m b ofs).

Theorem calculate_issuance_entropy_canonical_local_spec : memcpy_model ->
  elements_entropy_local_spec f_simplicity_calculate_issuance_entropy
    (fun a => @calculate_issuance_entropy_spec Alg.CoreFunSem a).
Proof.
  intros HM env m bd dbase bs sbase bi bw edge outedge cursor rc [[h ix] con].
  exact (calculate_issuance_entropy_local_spec HM env m bd dbase bs sbase
    bi bw edge outedge cursor rc h ix con).
Qed.
