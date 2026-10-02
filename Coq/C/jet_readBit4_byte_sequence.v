(** Initial-only mixed bit/nibble/byte reader sequence, retaining the exact
    carriers needed by fill-controlled byte operations and memory framing. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_word_repr.
Require Import C.jet_readBit_layout C.jet_read4_byte_sequence.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_readBit4_byte_sequence m bf base bi edge rc fill
    (amount : Ty.tySem (Word 2)) (x : Ty.tySem (Word 3)) :
  frame_base_valid base -> 0 <= rc <= Int64.max_unsigned - (1 + 4 + 8) ->
  frame_fields_at m bf base bi edge rc ->
  frame_input_bit_at m bi edge rc fill ->
  frame_input_word_at m bi edge (rc + 1) amount ->
  frame_input_word_at m bi edge (rc + (1 + 4)) x ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bi ->
  exists mb mr mf a r,
    Clight2.eval_funcall ge0 m (Internal f_readBit)
      [Vptr bf (Ptrofs.repr base)] E0 mb (Vint (bit_int fill)) /\
    Clight2.eval_funcall ge0 mb (Internal f_simplicity_read4)
      [Vptr bf (Ptrofs.repr base)] E0 mr (Vint a) /\
    Int.unsigned a = @toZ (WordToZ 2) amount /\
    Int.zero_ext 8 a = a /\
    Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8)
      [Vptr bf (Ptrofs.repr base)] E0 mf (Vint r) /\
    Int.unsigned r = @toZ (WordToZ 3) x /\
    frame_fields_at mf bf base bi edge (rc + (1 + 4 + 8)) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB Hrc HF Hfill Ha Hx PW HD.
  destruct (eval_readBit_layout m bf base bi edge rc fill HB ltac:(lia) HF Hfill PW)
    as (mb & HreadBit & HfieldsBit & HmemBit & HpermBit & HvalidBit).
  assert (HaB : frame_input_word_at mb bi edge (rc + 1) amount).
  { eapply frame_input_bits_at_preserved; [|exact Ha].
    intros ofs w HL. rewrite HmemBit by (left; congruence); exact HL. }
  assert (HxB : frame_input_word_at mb bi edge (rc + 1 + 4) x).
  { replace (rc + 1 + 4) with (rc + (1 + 4)) by lia.
    eapply frame_input_bits_at_preserved; [|exact Hx].
    intros ofs w HL. rewrite HmemBit by (left; congruence); exact HL. }
  assert (PWB : Mem.valid_access mb Mint64 bf (base + 8) Writable).
  { destruct PW as [HP HAlign]. split; [|exact HAlign].
    intros ofs Hrange. apply HpermBit. apply HP; exact Hrange. }
  destruct (eval_read4_byte_sequence mb bf base bi edge (rc + 1) amount x
    HB ltac:(lia) HfieldsBit HaB HxB PWB HD)
    as (mr & mf & a & r & Hread4 & Hamount & Hcast & Hread8 & Hpayload &
      Hfields & Hmem & Hperm & Hvalid).
  exists mb, mr, mf, a, r.
  split; [exact HreadBit|]. split; [exact Hread4|]. split; [exact Hamount|].
  split; [exact Hcast|]. split; [exact Hread8|]. split; [exact Hpayload|]. split.
  - replace (rc + (1 + 4 + 8)) with (rc + 1 + (4 + 8)) by lia; exact Hfields.
  - split.
    + intros chunk b ofs Houtside. rewrite Hmem, HmemBit by exact Houtside; reflexivity.
    + split; [intros; apply Hperm, HpermBit; assumption|intros; apply Hvalid, HvalidBit; assumption].
Qed.
