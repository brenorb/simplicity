(** Derive the actual 64/32/32/64 reader sequence from initial input words.
    No intermediate memory or reader executions are assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word.
Require Import C.jets C.jet_exec C.jet_wide C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_complement_wide_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma divmod128_access_preserved m mf chunk b ofs p :
  (forall bb addr kind permission, Mem.perm m bb addr kind permission -> Mem.perm mf bb addr kind permission) ->
  Mem.valid_access m chunk b ofs p -> Mem.valid_access mf chunk b ofs p.
Proof.
  intros Hperms [HP Halign]. split; [|exact Halign].
  intros addr Haddr. apply Hperms. apply HP. exact Haddr.
Qed.

Theorem eval_divmod128_readers m bf base bi edge rc
    (xh : Ty.tySem (Word 6)) (xm xl : Ty.tySem (Word 5)) (y : Ty.tySem (Word 6)) :
  frame_base_valid base -> 0 <= rc <= Int64.max_unsigned - 192 ->
  frame_fields_at m bf base bi edge rc ->
  frame_input_word_at m bi edge rc xh -> frame_input_word_at m bi edge (rc + 64) xm ->
  frame_input_word_at m bi edge (rc + 96) xl -> frame_input_word_at m bi edge (rc + 128) y ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bi ->
  exists m1 m2 m3 mf ah am al b,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_read64) [Vptr bf (Ptrofs.repr base)] E0 m1 (Vlong ah) /\
    Clight2.eval_funcall ge0 m1 (Internal f_simplicity_read32) [Vptr bf (Ptrofs.repr base)] E0 m2 (Vlong am) /\
    Clight2.eval_funcall ge0 m2 (Internal f_simplicity_read32) [Vptr bf (Ptrofs.repr base)] E0 m3 (Vlong al) /\
    Clight2.eval_funcall ge0 m3 (Internal f_simplicity_read64) [Vptr bf (Ptrofs.repr base)] E0 mf (Vlong b) /\
    Int64.unsigned ah = @toZ (WordToZ 6) xh /\ Int64.unsigned am = @toZ (WordToZ 5) xm /\
    Int64.unsigned al = @toZ (WordToZ 5) xl /\ Int64.unsigned b = @toZ (WordToZ 6) y /\
    frame_fields_at mf bf base bi edge (rc + 192) /\
    (forall chunk bb ofs, bb <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf bb ofs = Mem.load chunk m bb ofs) /\
    (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mf bb ofs kind p) /\
    (forall bb, Mem.valid_block m bb -> Mem.valid_block mf bb).
Proof.
  intros Hbase Hrc Hfields Hxh Hxm Hxl Hy HP Hsep.
  destruct (eval_read_wide_word_at W64 m bf base bi edge rc xh Hbase ltac:(change (0 <= rc <= Int64.max_unsigned - 64); lia)
    Hfields Hxh HP Hsep) as (m1 & ah & HC1 & Hah & HF1 & HM1 & HP1 & HV1).
  assert (Hxm1 : frame_input_word_at m1 bi edge (rc + 64) xm).
  { eapply frame_input_bits_at_preserved; [|exact Hxm]. intros ofs w HL. rewrite HM1 by auto. exact HL. }
  assert (Hxl1 : frame_input_word_at m1 bi edge (rc + 96) xl).
  { eapply frame_input_bits_at_preserved; [|exact Hxl]. intros ofs w HL. rewrite HM1 by auto. exact HL. }
  assert (Hy1 : frame_input_word_at m1 bi edge (rc + 128) y).
  { eapply frame_input_bits_at_preserved; [|exact Hy]. intros ofs w HL. rewrite HM1 by auto. exact HL. }
  assert (HA1 : Mem.valid_access m1 Mint64 bf (base + 8) Writable).
  { eapply divmod128_access_preserved; eauto. }
  destruct (eval_read_wide_word_at W32 m1 bf base bi edge (rc + 64) xm Hbase
    ltac:(change (0 <= rc + 64 <= Int64.max_unsigned - 32); lia) HF1 Hxm1 HA1 Hsep)
    as (m2 & am & HC2 & Ham & HF2 & HM2 & HP2 & HV2).
  replace (rc + 64 + wide_bits W32) with (rc + 96) in HF2 by (cbn; lia).
  assert (Hxl2 : frame_input_word_at m2 bi edge (rc + 96) xl).
  { eapply frame_input_bits_at_preserved; [|exact Hxl1]. intros ofs w HL. rewrite HM2 by auto. exact HL. }
  assert (Hy2 : frame_input_word_at m2 bi edge (rc + 128) y).
  { eapply frame_input_bits_at_preserved; [|exact Hy1]. intros ofs w HL. rewrite HM2 by auto. exact HL. }
  assert (HA2 : Mem.valid_access m2 Mint64 bf (base + 8) Writable).
  { eapply divmod128_access_preserved; eauto. }
  destruct (eval_read_wide_word_at W32 m2 bf base bi edge (rc + 96) xl Hbase
    ltac:(change (0 <= rc + 96 <= Int64.max_unsigned - 32); lia) HF2 Hxl2 HA2 Hsep)
    as (m3 & al & HC3 & Hal & HF3 & HM3 & HP3 & HV3).
  replace (rc + 96 + wide_bits W32) with (rc + 128) in HF3 by (cbn; lia).
  assert (Hy3 : frame_input_word_at m3 bi edge (rc + 128) y).
  { eapply frame_input_bits_at_preserved; [|exact Hy2]. intros ofs w HL. rewrite HM3 by auto. exact HL. }
  assert (HA3 : Mem.valid_access m3 Mint64 bf (base + 8) Writable).
  { eapply divmod128_access_preserved; eauto. }
  destruct (eval_read_wide_word_at W64 m3 bf base bi edge (rc + 128) y Hbase
    ltac:(change (0 <= rc + 128 <= Int64.max_unsigned - 64); lia) HF3 Hy3 HA3 Hsep)
    as (mf & b & HC4 & Hb & HF4 & HM4 & HP4 & HV4).
  replace (rc + 128 + wide_bits W64) with (rc + 192) in HF4 by (cbn; lia).
  exists m1, m2, m3, mf, ah, am, al, b.
  do 9 (split; [assumption|]). split.
  - intros chunk bb ofs Hout. rewrite HM4, HM3, HM2, HM1 by exact Hout. reflexivity.
  - split.
    + intros bb ofs kind p Hperm. apply HP4, HP3, HP2, HP1; exact Hperm.
    + intros bb Hvalid. apply HV4, HV3, HV2, HV1; exact Hvalid.
Qed.
