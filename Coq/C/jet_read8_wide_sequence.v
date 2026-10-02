(** Initial-only mixed readers for byte-controlled wide scalar jets.
    Derives both actual calls, exact carrier values and their combined cursor
    and memory footprint. This helper alone is not jet-equivalence coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_spec C.jet_read8 C.jet_add8 C.jet_add8_word.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_wide C.jet_complement_wide_layout.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma read8_result_cast_id w : Int.zero_ext 8 (read8_result w) = read8_result w.
Proof. unfold read8_result at 1; rewrite Int.zero_ext_idem by lia; reflexivity. Qed.

Lemma read8_result_exact_unsigned w :
  Int.unsigned (read8_result w) = @toZ (WordToZ 3) (decode_word8 w).
Proof.
  pose proof (read8_result_unsigned w) as H.
  unfold add8_u in H. rewrite read8_result_cast_id in H; exact H.
Qed.

Theorem eval_read8_wide_sequence s m bf base bi edge rc
    (amount : Ty.tySem (Word 3)) (x : Ty.tySem (Word (wide_log s))) :
  frame_base_valid base -> 0 <= rc <= Int64.max_unsigned - (8 + wide_bits s) ->
  frame_fields_at m bf base bi edge rc ->
  frame_input_word_at m bi edge rc amount ->
  frame_input_word_at m bi edge (rc + 8) x ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bi ->
  exists mr mf a r,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_read8)
      [Vptr bf (Ptrofs.repr base)] E0 mr (Vint a) /\
    Int.unsigned a = @toZ (WordToZ 3) amount /\
    Int.zero_ext 8 a = a /\
    Clight2.eval_funcall ge0 mr (Internal (wide_reader s))
      [Vptr bf (Ptrofs.repr base)] E0 mf (Vlong r) /\
    Int64.unsigned r = @toZ (WordToZ (wide_log s)) x /\
    frame_fields_at mf bf base bi edge (rc + (8 + wide_bits s)) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB Hrc HF Ha Hx PW HD.
  pose proof (wide_bits_bounds s) as Hwidth.
  assert (HSlice : byte_slice_at m bi edge rc amount).
  { apply byte_slice_at_encode. split; [lia|apply frame_input_word_at_encode; exact Ha]. }
  destruct (eval_read8_byte_at m bf base bi edge rc amount HB HF HSlice PW HD)
    as (mr & payload & Hread8 & Hdecode & Hfields8 & Hmem8 & Hperm8 & Hvalid8).
  assert (HxR : frame_input_word_at mr bi edge (rc + 8) x).
  { eapply frame_input_bits_at_preserved; [|exact Hx].
    intros ofs w HL. rewrite Hmem8 by (left; congruence); exact HL. }
  assert (PWR : Mem.valid_access mr Mint64 bf (base + 8) Writable).
  { destruct PW as [HP HAlign]. split; [|exact HAlign].
    intros ofs Hrange. apply Hperm8. apply HP; exact Hrange. }
  destruct (eval_read_wide_word_at s mr bf base bi edge (rc + 8) x HB ltac:(lia)
    Hfields8 HxR PWR HD)
    as (mf & r & Hread & Hr & Hfields & Hmem & Hperm & Hvalid).
  exists mr, mf, (read8_result payload), r.
  split; [exact Hread8|]. split.
  - rewrite read8_result_exact_unsigned, Hdecode; reflexivity.
  - split; [apply read8_result_cast_id|]. split; [exact Hread|]. split; [exact Hr|]. split.
    + replace (rc + (8 + wide_bits s)) with (rc + 8 + wide_bits s) by lia; exact Hfields.
    + split.
      * intros chunk b ofs Houtside. rewrite Hmem, Hmem8 by exact Houtside; reflexivity.
      * split; [intros; apply Hperm, Hperm8; assumption|intros; apply Hvalid, Hvalid8; assumption].
Qed.
