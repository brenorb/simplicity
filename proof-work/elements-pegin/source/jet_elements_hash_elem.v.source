(** Element relation and payload lemmas for a 256-bit hash stored as eight
    32-bit words, shared by the Elements indexed hash getters (ported from the
    Bitcoin unit). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option C.jet_elements_prim.
Require Import C.jet_application_sep C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_uint32_array_init.
Require Import C.jets_elements C.jet_elements_linkage C.jet_exec.
Require C.jets.
Require Import C.jet_elements_version_exec C.jet_elements_field_eval C.jet_elements_wrapper C.jet_elements_effects.
Require Import C.jet_elements_transport C.jet_elements_call C.jet_elements_index_eval.
Require Import C.jet_elements_indexed_exec C.jet_elements_indexed_ptr_then C.jet_elements_indexed_scalar.
Require Import C.jet_elements_hash_write C.jet_elements_hash_helpers C.jet_elements_indexed_ptr.
Require Import C.jet_elements_script_cmr_local C.jet_elements_indexed_scalar_jets C.jet_elements_indexed_ptr_jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.


Lemma encode_sum_inr_hash' (w : Ty.tySem Word256) :
  @encode (Ty.Sum Ty.Unit Word256) (inr w) = Some true :: @encode Word256 w.
Proof. reflexivity. Qed.

Definition hash_elem_rep (m : mem) (b : block) (ofs : Z) (h : hash256) : Prop :=
  uint32_array_at m b ofs (hash256_reg h).

Lemma hash_elem_rep_mono m1 m2 b ofs h :
  hash_elem_rep m1 b ofs h ->
  (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + 32 ->
    Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) ->
  hash_elem_rep m2 b ofs h.
Proof. intros Hr Hl. eapply uint32_array_at_mono; [exact (hash256_len _)|exact Hr|exact Hl]. Qed.

Lemma hash_elem_pay bd dbase bw outedge m' bin ofs (x : hash256) cur :
  hash_elem_rep m' bin ofs x -> 0 <= ofs -> ofs + 32 <= Ptrofs.max_unsigned ->
  out_sep bd dbase bw outedge cur 256 bin ofs (ofs + 32) ->
  write_frame_at m' bd dbase bw outedge cur 256 ->
  exists me, Clight2.eval_funcall elements_ge m' (Internal f_writeHash)
    [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr ofs)] E0 me Vundef /\
    write_effect m' me bd dbase bw outedge cur 256 (hash_cells (hash256_reg x)).
Proof.
  intros Hr H0 HM HSep HF.
  destruct (eval_elements_writeHash_layout m' bin ofs bd dbase bw outedge cur (hash256_reg x)
    (hash256_len x) H0 HM HSep Hr HF) as (me & HC & HE).
  exists me. split; [exact HC|exact HE].
Qed.

Lemma hash_cells_len_256 (x : hash256) : Z.of_nat (length (hash_cells (hash256_reg x))) = 256.
Proof.
  rewrite hash_cells_length. rewrite (hash256_len x). reflexivity.
Qed.
