(** Outpoint input encodings, byte streams and normal-sequence composition facts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_memcpy_model C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_readBit_layout C.jet_read8s_layout C.jet_elements_support_sha_ctx_abs C.jet_sha_ctx8_model.
Require Import C.jet_elements_support_sha_uchars_exec C.jet_elements_support_sha_add_n_init C.jet_elements_support_sha_linkage C.jet_elements_support_sha_block_local.
Require Import C.jets_elements C.jet_elements_linkage.
Require Import C.jet_nonce_context_spec C.jet_nonce_context_shape C.jet_nonce_exec_effects C.jet_nonce_exec_calls.
Import Mem Values Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Require Import C.jet_forwardBits_layout C.jet_elements_support_sha_transport C.jet_elements_sha_program C.jet_nonce_exec_prefix C.jet_outpoint_exec_shape.

Require Import C.jet_buffer_input C.jet_outpoint_exec_read C.jet_outpoint_exec_absorb C.jet_outpoint_exec_payload C.jet_outpoint_exec_frame_ops.

Definition op_pegin_type := Ty.Sum Ty.Unit Word256.
Definition op_bytes (a : Ty.tySem op_pegin_type) : list (Ty.tySem Word8) :=
  match a with inl _ => [nonce_byte 0] | inr h => nonce_byte 1 :: vector_values Word8 5 h end.
Definition op_count (a : Ty.tySem op_pegin_type) : Z := match a with inl _ => 1 | inr _ => 33 end.
Definition op_bit (a : Ty.tySem op_pegin_type) := match a with inl _ => false | inr _ => true end.
Definition op_overflow ovf c (a : Ty.tySem op_pegin_type) :=
  match a with
  | inl _ => uc_overflow ovf c (Int64.repr 1)
  | inr _ => uc_overflow (uc_overflow ovf c (Int64.repr 1)) (Int64.add c (Int64.repr 1)) (Int64.repr 32)
  end.
Definition op_outpoint_bytes (h : Ty.tySem Word256) (ix : Ty.tySem Word32) :=
  vector_values Word8 5 h ++ vector_values Word8 2 ix.
Definition op_full_bytes a h ix := op_bytes a ++ op_outpoint_bytes h ix.
Definition op_total_count a := op_count a + 36.
Definition op_middle := Ssequence op_pegin (Ssequence (op_read 36) (op_absorb 36)).

Lemma op_none_encoding : @encode op_pegin_type (inl tt) = Some false :: repeat None 256.
Proof. reflexivity. Qed.
Lemma op_some_encoding h : @encode op_pegin_type (inr h) = Some true :: @encode Word256 h.
Proof. reflexivity. Qed.
Lemma op_bytes_length a : Z.of_nat (length (op_bytes a)) = op_count a.
Proof. destruct a; cbn [op_bytes op_count length]; [reflexivity|]. rewrite vector_values_length; reflexivity. Qed.
Lemma op_outpoint_bytes_length h ix : Z.of_nat (length (op_outpoint_bytes h ix)) = 36.
Proof. unfold op_outpoint_bytes. rewrite app_length, !vector_values_length. reflexivity. Qed.
Lemma op_outpoint_encoding h ix :
  concat (map (@encode Word8) (op_outpoint_bytes h ix)) = @encode (Ty.Prod Word256 Word32) (h, ix).
Proof.
  unfold op_outpoint_bytes. rewrite map_app, concat_app.
  rewrite <- (encode_vector_values Word8 5 h), <- (encode_vector_values Word8 2 ix). reflexivity.
Qed.
Lemma op_full_bytes_length a h ix : Z.of_nat (length (op_full_bytes a h ix)) = op_total_count a.
Proof. unfold op_full_bytes, op_total_count. rewrite app_length, Nat2Z.inj_add, op_bytes_length, op_outpoint_bytes_length. reflexivity. Qed.
Lemma op_counter_one_then_32 c :
  Int64.add (Int64.add c (Int64.repr 1)) (Int64.repr 32) = Int64.add c (Int64.repr 33).
Proof. rewrite Int64.add_assoc. reflexivity. Qed.

Lemma op_seq_normal_inv ge e le m a b le' mf :
  Clight2.exec_stmt ge e le m (Ssequence a b) E0 le' mf Out_normal ->
  exists le1 m1,
    Clight2.exec_stmt ge e le m a E0 le1 m1 Out_normal /\
    Clight2.exec_stmt ge e le1 m1 b E0 le' mf Out_normal.
Proof.
  intro HS. inversion HS; subst; try contradiction.
  match goal with H : ?t1 ** ?t2 = E0 |- _ =>
    apply app_eq_nil in H; destruct H; subst end.
  eauto.
Qed.
