(** Total generated read32 contract: construct cursor stores and frame all
    memory effects from the initial writable-field contract. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Events Memory.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_read32_layout_exec.
Import Values Mem Ctypes ListNotations.
Require Import C.jet_reader_total.
Local Open Scope Z_scope.

Definition read32_layout_value (cursor : Z) (high low : int64) : int64 :=
  if Z_le_dec (cursor mod 64) 32
  then read32_non_crossing_at cursor high
  else read32_crossing_at cursor high low.

Theorem eval_read32_layout_total m bf base bw edge cursor high low :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - 32 ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  (32 < cursor mod 64 ->
    8 * (2 + cursor / 64) <= edge /\
    Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)) ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bw ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read32)
      [Vptr bf (Ptrofs.repr base)] E0 mf
      (Vlong (read32_layout_value cursor high low)) /\
    frame_fields_at mf bf base bw edge (cursor + 32) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  exact (eval_reader_layout_total 32 f_simplicity_read32
    read32_non_crossing_at read32_crossing_at
    eval_read32_layout_non_crossing eval_read32_layout_crossing
    m bf base bw edge cursor high low).
Qed.
