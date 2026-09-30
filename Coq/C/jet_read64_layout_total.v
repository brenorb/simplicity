(** Total generated read64 contract for aligned and crossing cursor layouts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Events Memory.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_read64_input_word.
Require Import C.jet_read64_layout_exec.
Import Values Mem Ctypes ListNotations.
Require Import C.jet_reader_total.
Local Open Scope Z_scope.

Definition read64_layout_value (cursor : Z) (high low : int64) : int64 :=
  if Z.eq_dec (cursor mod 64) 0
  then read64_aligned_at high
  else read64_crossing_at cursor high low.

Lemma eval_read64_layout_noncross_kernel m mf bf base bw edge cursor high :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - 64 ->
  cursor mod 64 <= 0 ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.store Mint64 m bf (base + 8) (Vlong (Int64.repr (cursor + 64))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read64)
    [Vptr bf (Ptrofs.repr base)] E0 mf (Vlong high).
Proof.
  intros HB HC Hmod HE HF HH HS.
  assert (Hz : cursor mod 64 = 0).
  { pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)); lia. }
  exact (eval_read64_layout_aligned m mf bf base bw edge cursor high
    HB HC Hz HE HF HH HS).
Qed.

Theorem eval_read64_layout_total m bf base bw edge cursor high low :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - 64 ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  (cursor mod 64 <> 0 ->
    8 * (2 + cursor / 64) <= edge /\
    Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)) ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bw ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_read64)
      [Vptr bf (Ptrofs.repr base)] E0 mf
      (Vlong (read64_layout_value cursor high low)) /\
    frame_fields_at mf bf base bw edge (cursor + 64) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HC HE HF HH HLow PW HD.
  assert (Hmod : 0 <= cursor mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  pose proof (eval_reader_layout_total 64 f_simplicity_read64
    (fun _ high => high) read64_crossing_at
    eval_read64_layout_noncross_kernel
    eval_read64_layout_crossing m bf base bw edge cursor high low
    HB HC HE HF HH ltac:(intros; apply HLow; lia) PW HD) as H.
  unfold reader_layout_value in H. unfold read64_layout_value.
  destruct (Z_le_dec (cursor mod 64) (64 - 64)), (Z.eq_dec (cursor mod 64) 0);
    try lia; exact H.
Qed.
