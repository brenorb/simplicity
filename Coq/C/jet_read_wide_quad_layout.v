(** Four actual wide reader calls derived from initial frame observations.
    Shared across word widths and consumers; not independent jet coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Memory Events Clight ClightBigstep.
Require Import Simplicity.Word.
Require Import C.jet_exec C.jet_wide C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_two_word_input C.jet_complement_wide_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_read_wide_quad_at s m bl base bi edge rc
    (x y z w : Ty.tySem (Word (wide_log s))) :
  frame_base_valid base -> 0 <= rc <= Int64.max_unsigned - 4 * wide_bits s ->
  frame_fields_at m bl base bi edge rc ->
  frame_input_word_at m bi edge rc x ->
  frame_input_word_at m bi edge (rc + wide_bits s) y ->
  frame_input_word_at m bi edge (rc + 2 * wide_bits s) z ->
  frame_input_word_at m bi edge (rc + 3 * wide_bits s) w ->
  Mem.valid_access m Mint64 bl (base + 8) Writable -> bl <> bi ->
  exists mr1 mr2 mr3 mr4 a b u v,
    Clight2.eval_funcall ge0 m (Internal (wide_reader s)) [Vptr bl (Ptrofs.repr base)] E0 mr1 (Vlong a) /\
    Clight2.eval_funcall ge0 mr1 (Internal (wide_reader s)) [Vptr bl (Ptrofs.repr base)] E0 mr2 (Vlong b) /\
    Clight2.eval_funcall ge0 mr2 (Internal (wide_reader s)) [Vptr bl (Ptrofs.repr base)] E0 mr3 (Vlong u) /\
    Clight2.eval_funcall ge0 mr3 (Internal (wide_reader s)) [Vptr bl (Ptrofs.repr base)] E0 mr4 (Vlong v) /\
    Int64.unsigned a = @toZ (WordToZ (wide_log s)) x /\
    Int64.unsigned b = @toZ (WordToZ (wide_log s)) y /\
    Int64.unsigned u = @toZ (WordToZ (wide_log s)) z /\
    Int64.unsigned v = @toZ (WordToZ (wide_log s)) w /\
    frame_fields_at mr4 bl base bi edge (rc + 4 * wide_bits s) /\
    (forall chunk bb ofs, bb <> bl \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mr4 bb ofs = Mem.load chunk m bb ofs) /\
    (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mr4 bb ofs kind p) /\
    (forall bb, Mem.valid_block m bb -> Mem.valid_block mr4 bb).
Proof.
  intros HB Hrc HF HX HY HZ HW PC HN. pose proof (wide_bits_bounds s) as Hwidth.
  destruct (eval_read_wide_word_at s m bl base bi edge rc x HB ltac:(lia) HF HX PC HN)
    as (mr1 & a & HR1 & HA & HF1 & HM1 & HP1 & HV1).
  assert (HY1 : frame_input_word_at mr1 bi edge (rc + wide_bits s) y).
  { eapply frame_input_bits_at_preserved; [|exact HY]. intros ofs v HL. rewrite HM1 by auto; exact HL. }
  assert (PC1 : Mem.valid_access mr1 Mint64 bl (base + 8) Writable)
    by (eapply permissions_preserve_access; eauto).
  destruct (eval_read_wide_word_at s mr1 bl base bi edge (rc + wide_bits s) y HB ltac:(lia) HF1 HY1 PC1 HN)
    as (mr2 & b & HR2 & HBy & HF2 & HM2 & HP2 & HV2).
  assert (HZ2 : frame_input_word_at mr2 bi edge (rc + 2 * wide_bits s) z).
  { eapply frame_input_bits_at_preserved; [|exact HZ]. intros ofs v HL. rewrite HM2, HM1 by auto; exact HL. }
  assert (PC2 : Mem.valid_access mr2 Mint64 bl (base + 8) Writable)
    by (eapply permissions_preserve_access; eauto).
  replace (rc + wide_bits s + wide_bits s) with (rc + 2 * wide_bits s) in HF2 by lia.
  destruct (eval_read_wide_word_at s mr2 bl base bi edge (rc + 2 * wide_bits s) z HB ltac:(lia) HF2 HZ2 PC2 HN)
    as (mr3 & u & HR3 & HU & HF3 & HM3 & HP3 & HV3).
  assert (HW3 : frame_input_word_at mr3 bi edge (rc + 3 * wide_bits s) w).
  { eapply frame_input_bits_at_preserved; [|exact HW]. intros ofs v HL. rewrite HM3, HM2, HM1 by auto; exact HL. }
  assert (PC3 : Mem.valid_access mr3 Mint64 bl (base + 8) Writable)
    by (eapply permissions_preserve_access; eauto).
  replace (rc + 2 * wide_bits s + wide_bits s) with (rc + 3 * wide_bits s) in HF3 by lia.
  destruct (eval_read_wide_word_at s mr3 bl base bi edge (rc + 3 * wide_bits s) w HB ltac:(lia) HF3 HW3 PC3 HN)
    as (mr4 & v & HR4 & HV & HF4 & HM4 & HP4 & HV4).
  replace (rc + 3 * wide_bits s + wide_bits s) with (rc + 4 * wide_bits s) in HF4 by lia.
  exists mr1, mr2, mr3, mr4, a, b, u, v. do 9 (split; [assumption|]). split.
  - intros chunk bb ofs Hout. rewrite HM4, HM3, HM2, HM1 by exact Hout. reflexivity.
  - split.
    + intros bb ofs kind p H. apply HP4, HP3, HP2, HP1; exact H.
    + intros bb H. apply HV4, HV3, HV2, HV1; exact H.
Qed.
