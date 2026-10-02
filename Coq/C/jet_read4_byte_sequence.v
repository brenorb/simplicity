(** Initial-only mixed nibble and byte readers. Both exact C carriers,
    cursor updates and memory observations are derived from initial frames. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_word_repr.
Require Import C.jet_wide C.jet_read4_input_word C.jet_rotate_count_exec.
Require Import C.jet_spec C.jet_read8 C.jet_read8_wide_sequence C.jet_encoding C.jet_bitmachine_rep.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_read4_byte_sequence m bf base bi edge rc
    (amount : Ty.tySem (Word 2)) (x : Ty.tySem (Word 3)) :
  frame_base_valid base -> 0 <= rc <= Int64.max_unsigned - (4 + 8) ->
  frame_fields_at m bf base bi edge rc ->
  frame_input_word_at m bi edge rc amount ->
  frame_input_word_at m bi edge (rc + 4) x ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bi ->
  exists mr mf a r,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_read4)
      [Vptr bf (Ptrofs.repr base)] E0 mr (Vint a) /\
    Int.unsigned a = @toZ (WordToZ 2) amount /\
    Int.zero_ext 8 a = a /\
    Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8)
      [Vptr bf (Ptrofs.repr base)] E0 mf (Vint r) /\
    Int.unsigned r = @toZ (WordToZ 3) x /\
    frame_fields_at mf bf base bi edge (rc + (4 + 8)) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB Hrc HF Ha Hx PW HD.
  destruct (eval_read4_word_at m bf base bi edge rc amount HB ltac:(lia) HF Ha PW HD)
    as (mr & a & Hread4 & Hamount & Hfields4 & Hmem4 & Hperm4 & Hvalid4).
  assert (HxR : frame_input_word_at mr bi edge (rc + 4) x).
  { eapply frame_input_bits_at_preserved; [|exact Hx].
    intros ofs w HL. rewrite Hmem4 by (left; congruence); exact HL. }
  assert (PWR : Mem.valid_access mr Mint64 bf (base + 8) Writable).
  { destruct PW as [HP HAlign]. split; [|exact HAlign].
    intros ofs Hrange. apply Hperm4. apply HP; exact Hrange. }
  assert (HSlice : byte_slice_at mr bi edge (rc + 4) x).
  { apply byte_slice_at_encode. split; [lia|apply frame_input_word_at_encode; exact HxR]. }
  destruct (eval_read8_byte_at mr bf base bi edge (rc + 4) x HB Hfields4 HSlice PWR HD)
    as (mf & payload & Hread & Hdecode & Hfields & Hmem & Hperm & Hvalid).
  assert (Hr : Int.unsigned (read8_result payload) = @toZ (WordToZ 3) x).
  { rewrite read8_result_exact_unsigned, Hdecode; reflexivity. }
  exists mr, mf, a, (read8_result payload). split; [exact Hread4|]. split; [exact Hamount|]. split.
  - apply byte_carrier_cast_id. rewrite Hamount. pose proof (word_toZ_range 2 amount) as HR.
    change (0 <= @toZ (WordToZ 2) amount < 16) in HR. lia.
  - split; [exact Hread|]. split; [exact Hr|]. split.
    + replace (rc + (4 + 8)) with (rc + 4 + 8) by lia; exact Hfields.
    + split.
      * intros chunk b ofs Houtside. rewrite Hmem, Hmem4 by exact Houtside; reflexivity.
      * split; [intros; apply Hperm, Hperm4; assumption|intros; apply Hvalid, Hvalid4; assumption].
Qed.
