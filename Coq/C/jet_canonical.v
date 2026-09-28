(** The twelve public jet theorems in canonical-encoding form.

    Each [*_local_spec] restates a public implementation-to-specification
    theorem as [jet_local_spec]: the input is the frame cells holding
    [Translate.encode a] and the output is the frame cells holding
    [Translate.encode (spec a)].  The equivalences in [jet_encoding] do the
    translation; the value theorems themselves are reused unchanged, so the
    frame, block and cursor generality of the originals is kept. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Simplicity.Alg Simplicity.Bit.
Require Import Simplicity.Ty Simplicity.Bit Simplicity.Word Simplicity.BitMachine Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_output_slice C.jet_wide C.jet_wide_spec.
Require Import C.jet_spec C.jet_add8_word C.jet_increment_wide_word C.jet_increment32_wide_word.
Require Import C.jet_increment64_wide_word C.jet_add16_wide_word C.jet_add32_wide_word.
Require Import C.jet_add64_wide_word.
Require Import C.jet_one8_layout C.jet_one_wide_layout C.jet_increment8_layout C.jet_add8_layout.
Require Import C.jet_increment16_layout C.jet_add16_layout C.jet_increment32_layout.
Require Import C.jet_add32_layout C.jet_increment64_layout C.jet_add64_layout.
Require Import C.jet_carry_wide_layout C.jet_carry_byte_layout.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Lemma frame_fields_loadbytes m b base bw edge cursor :
  frame_fields_at m b base bw edge cursor ->
  exists bytes, Mem.loadbytes m b base 16 = Some bytes.
Proof.
  intros [HE HC].
  apply Mem.load_loadbytes in HE. destruct HE as [b1 [H1 _]].
  apply Mem.load_loadbytes in HC. destruct HC as [b2 [H2 _]].
  change (size_chunk Mptr) with 8 in H1. change (size_chunk Mint64) with 8 in H2.
  exists (b1 ++ b2). change 16 with (8 + 8).
  apply Mem.loadbytes_concat; auto; lia.
Qed.

(** Weaken the modified-range exclusion of a value theorem. *)
Lemma loads_weaken m mf bd dbase bw lo lo' hi :
  lo' <= lo ->
  (forall chunk b ofs, Mem.valid_block m b ->
    (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
    (b <> bw \/ ofs + size_chunk chunk <= lo \/ hi <= ofs) ->
    Mem.load chunk mf b ofs = Mem.load chunk m b ofs) ->
  (forall chunk b ofs, Mem.valid_block m b ->
    (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
    (b <> bw \/ ofs + size_chunk chunk <= lo' \/ hi <= ofs) ->
    Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros Hle H chunk b ofs Hv Hd Hw. apply H; auto.
  destruct Hw as [Hw|[Hw|Hw]]; [left|right; left|right; right]; lia || auto.
Qed.

Lemma write_frame_at_count m bd dbase bw edge cursor count :
  write_frame_at m bd dbase bw edge cursor count -> count <= cursor.
Proof. intros (_ & _ & _ & HC & _). lia. Qed.

(** * Parametricity of the specifications *)

Lemma increment16_spec_parametric : Alg.Core.Parametric (@increment16_spec).
Proof. exact (increment_word_spec_parametric 4). Qed.
Lemma increment32_spec_parametric : Alg.Core.Parametric (@increment32_spec).
Proof. exact (increment_word_spec_parametric 5). Qed.
Lemma increment64_spec_parametric : Alg.Core.Parametric (@increment64_spec).
Proof. exact (increment_word_spec_parametric 6). Qed.
Lemma add16_spec_parametric : Alg.Core.Parametric (@add16_spec).
Proof. intros alg1 alg2 R. apply Word.adder_Parametric. Qed.
Lemma add32_spec_parametric : Alg.Core.Parametric (@add32_spec).
Proof. intros alg1 alg2 R. apply Word.adder_Parametric. Qed.
Lemma add64_spec_parametric : Alg.Core.Parametric (@add64_spec).
Proof. intros alg1 alg2 R. apply Word.adder_Parametric. Qed.

(** * one_N *)

Theorem one8_local_spec :
  jet_local_spec f_simplicity_one_8 Ty.Unit Word8 (fun a => @one8_spec Alg.CoreFunSem a).
Proof.
  intros m bd dbase bs sbase bi bw edge outedge cursor rc [] HB HA HF _ _ _ Hout.
  change (Z.of_nat (bitSize Word8)) with 8 in *.
  destruct (frame_fields_loadbytes _ _ _ _ _ _ HF) as [bytes Hbytes].
  pose proof (write_frame_at_count _ _ _ _ _ _ _ Hout) as HC.
  destruct (eval_one8_layout_matches_spec m bd dbase bs sbase bw outedge cursor bytes
    HB HA Hbytes Hout) as (mf & Hcall & Hobs & Hpre & Hfld & Hpres).
  exists mf. split; [exact Hcall|]. split; [apply byte_output_at_encode; [lia|exact Hobs]|].
  split; [exact Hpre|]. split; [exact Hfld|].
  eapply loads_weaken; [|exact Hpres]. rewrite byte_write_low_slice.
  apply slice_write_low_bound; lia.
Qed.

Theorem one_wide_local_spec s :
  jet_local_spec (wide_one s) Ty.Unit (Word (wide_log s))
    (fun a => @wide_one_spec s Alg.CoreFunSem a).
Proof.
  intros m bd dbase bs sbase bi bw edge outedge cursor rc [] HB HA HF _ _ _ Hout.
  replace (Z.of_nat (bitSize (Word (wide_log s)))) with (wide_bits s) in *
    by (destruct s; reflexivity).
  pose proof (wide_bits_bounds s) as Hs.
  destruct (frame_fields_loadbytes _ _ _ _ _ _ HF) as [bytes Hbytes].
  pose proof (write_frame_at_count _ _ _ _ _ _ _ Hout) as HC.
  destruct (eval_one_wide_layout_matches_spec s m bd dbase bs sbase bw outedge cursor bytes
    HB HA Hbytes Hout) as (mf & Hcall & Hobs & Hpre & Hfld & Hpres).
  exists mf. split; [exact Hcall|]. split; [apply wide_output_at_encode; [lia|exact Hobs]|].
  split; [exact Hpre|]. split; [exact Hfld|].
  eapply loads_weaken; [|exact Hpres]. apply slice_write_low_bound; lia.
Qed.

Corollary one16_local_spec :
  jet_local_spec f_simplicity_one_16 Ty.Unit (Word 4) (fun a => @wide_one_spec W16 Alg.CoreFunSem a).
Proof. exact (one_wide_local_spec W16). Qed.
Corollary one32_local_spec :
  jet_local_spec f_simplicity_one_32 Ty.Unit (Word 5) (fun a => @wide_one_spec W32 Alg.CoreFunSem a).
Proof. exact (one_wide_local_spec W32). Qed.
Corollary one64_local_spec :
  jet_local_spec f_simplicity_one_64 Ty.Unit (Word 6) (fun a => @wide_one_spec W64 Alg.CoreFunSem a).
Proof. exact (one_wide_local_spec W64). Qed.

(** * increment_N and add_N at 8 bits *)

Theorem increment8_local_spec :
  jet_local_spec f_simplicity_increment_8 Word8 (Ty.Prod Bit Word8)
    (fun a => @increment8_spec Alg.CoreFunSem a).
Proof.
  intros m bd dbase bs sbase bi bw edge outedge cursor rc x HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize Word8)) with 8 in Hmax.
  change (Z.of_nat (bitSize (Ty.Prod Bit Word8))) with 9 in *.
  pose proof (write_frame_at_count _ _ _ _ _ _ _ Hout) as HC.
  assert (Hbyte : byte_input_at m bs sbase bi edge rc [x])
    by (apply byte_input_single_encode; refine (conj HB (conj HF (conj _ Hin))); lia).
  destruct (eval_increment8_layout_matches_spec m bd dbase bs sbase bi bw edge outedge x
    cursor rc Hbyte Hout) as (mf & Hcall & Hobs & Hpre & Hfld & Hpres).
  exists mf. split; [exact Hcall|].
  split; [apply carry_byte_output_encode; [lia|exact Hobs]|].
  split; [exact Hpre|]. split; [exact Hfld|].
  eapply loads_weaken; [|exact Hpres]. rewrite byte_write_low_slice.
  replace (cursor - 9) with (cursor - 1 - 8) by lia. apply slice_write_low_bound; lia.
Qed.

Theorem add8_local_spec :
  jet_local_spec f_simplicity_add_8 (Ty.Prod Word8 Word8) (Ty.Prod Bit Word8)
    (fun a => @add8_spec Alg.CoreFunSem a).
Proof.
  intros m bd dbase bs sbase bi bw edge outedge cursor rc [x y] HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Ty.Prod Word8 Word8))) with 16 in Hmax.
  change (Z.of_nat (bitSize (Ty.Prod Bit Word8))) with 9 in *.
  pose proof (write_frame_at_count _ _ _ _ _ _ _ Hout) as HC.
  assert (Hbyte : byte_input_at m bs sbase bi edge rc [x; y])
    by (apply byte_input_pair_encode; refine (conj HB (conj HF (conj _ Hin))); lia).
  destruct (eval_add8_layout_matches_spec m bd dbase bs sbase bi bw edge outedge x y
    cursor rc Hbyte Hout) as (mf & Hcall & Hobs & Hpre & Hfld & Hpres).
  exists mf. split; [exact Hcall|].
  split; [apply carry_byte_output_encode; [lia|exact Hobs]|].
  split; [exact Hpre|]. split; [exact Hfld|].
  eapply loads_weaken; [|exact Hpres]. rewrite byte_write_low_slice.
  replace (cursor - 9) with (cursor - 1 - 8) by lia. apply slice_write_low_bound; lia.
Qed.

(** * increment_N and add_N at 16, 32 and 64 bits *)

Ltac wide_local_output s n Hcall Hobs Hpre Hfld Hpres cursor :=
  eexists; split; [exact Hcall|];
  split; [apply (carry_wide_output_encode s); [cbn; lia|exact Hobs]|];
  split; [exact Hpre|]; split; [exact Hfld|];
  eapply loads_weaken; [|exact Hpres];
  replace (cursor - (n + 1)) with (cursor - 1 - n) by lia;
  apply slice_write_low_bound; lia.

Theorem increment16_local_spec :
  jet_local_spec f_simplicity_increment_16 (Word 4) (Ty.Prod Bit (Word 4))
    (fun a => @increment16_spec Alg.CoreFunSem a).
Proof.
  intros m bd dbase bs sbase bi bw edge outedge cursor rc x HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Word 4))) with 16 in Hmax.
  change (Z.of_nat (bitSize (Ty.Prod Bit (Word 4)))) with (16 + 1) in *.
  pose proof (write_frame_at_count _ _ _ _ _ _ _ Hout) as HC.
  apply frame_input_word_at_encode in Hin.
  destruct (eval_increment16_layout_matches_spec m bd dbase bs sbase bi bw edge outedge x
    cursor rc HB HA HF ltac:(lia) Hin Hout) as (mf & Hcall & Hobs & Hpre & Hfld & Hpres).
  wide_local_output W16 16 Hcall Hobs Hpre Hfld Hpres cursor.
Qed.

Theorem increment32_local_spec :
  jet_local_spec f_simplicity_increment_32 (Word 5) (Ty.Prod Bit (Word 5))
    (fun a => @increment32_spec Alg.CoreFunSem a).
Proof.
  intros m bd dbase bs sbase bi bw edge outedge cursor rc x HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Word 5))) with 32 in Hmax.
  change (Z.of_nat (bitSize (Ty.Prod Bit (Word 5)))) with (32 + 1) in *.
  pose proof (write_frame_at_count _ _ _ _ _ _ _ Hout) as HC.
  apply frame_input_word_at_encode in Hin.
  destruct (eval_increment32_layout_matches_spec m bd dbase bs sbase bi bw edge outedge x
    cursor rc HB HA HF ltac:(lia) Hin Hout) as (mf & Hcall & Hobs & Hpre & Hfld & Hpres).
  wide_local_output W32 32 Hcall Hobs Hpre Hfld Hpres cursor.
Qed.

Theorem increment64_local_spec :
  jet_local_spec f_simplicity_increment_64 (Word 6) (Ty.Prod Bit (Word 6))
    (fun a => @increment64_spec Alg.CoreFunSem a).
Proof.
  intros m bd dbase bs sbase bi bw edge outedge cursor rc x HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Word 6))) with 64 in Hmax.
  change (Z.of_nat (bitSize (Ty.Prod Bit (Word 6)))) with (64 + 1) in *.
  pose proof (write_frame_at_count _ _ _ _ _ _ _ Hout) as HC.
  apply frame_input_word_at_encode in Hin.
  destruct (eval_increment64_layout_matches_spec m bd dbase bs sbase bi bw edge outedge x
    cursor rc HB HA HF ltac:(lia) Hin Hout) as (mf & Hcall & Hobs & Hpre & Hfld & Hpres).
  wide_local_output W64 64 Hcall Hobs Hpre Hfld Hpres cursor.
Qed.

Theorem add16_local_spec :
  jet_local_spec f_simplicity_add_16 (Ty.Prod (Word 4) (Word 4)) (Ty.Prod Bit (Word 4))
    (fun a => @add16_spec Alg.CoreFunSem a).
Proof.
  intros m bd dbase bs sbase bi bw edge outedge cursor rc [x y] HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Ty.Prod (Word 4) (Word 4)))) with 32 in Hmax.
  change (Z.of_nat (bitSize (Ty.Prod Bit (Word 4)))) with (16 + 1) in *.
  pose proof (write_frame_at_count _ _ _ _ _ _ _ Hout) as HC.
  apply frame_input_word_pair_encode in Hin. destruct Hin as [Hx Hy].
  change (Z.of_nat (Nat.pow 2 4)) with 16 in Hy.
  destruct (eval_add16_layout_matches_spec m bd dbase bs sbase bi bw edge outedge x y
    cursor rc HB HA HF ltac:(lia) Hx Hy Hout) as (mf & Hcall & Hobs & Hpre & Hfld & Hpres).
  wide_local_output W16 16 Hcall Hobs Hpre Hfld Hpres cursor.
Qed.

Theorem add32_local_spec :
  jet_local_spec f_simplicity_add_32 (Ty.Prod (Word 5) (Word 5)) (Ty.Prod Bit (Word 5))
    (fun a => @add32_spec Alg.CoreFunSem a).
Proof.
  intros m bd dbase bs sbase bi bw edge outedge cursor rc [x y] HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Ty.Prod (Word 5) (Word 5)))) with 64 in Hmax.
  change (Z.of_nat (bitSize (Ty.Prod Bit (Word 5)))) with (32 + 1) in *.
  pose proof (write_frame_at_count _ _ _ _ _ _ _ Hout) as HC.
  apply frame_input_word_pair_encode in Hin. destruct Hin as [Hx Hy].
  change (Z.of_nat (Nat.pow 2 5)) with 32 in Hy.
  destruct (eval_add32_layout_matches_spec m bd dbase bs sbase bi bw edge outedge x y
    cursor rc HB HA HF ltac:(lia) Hx Hy Hout) as (mf & Hcall & Hobs & Hpre & Hfld & Hpres).
  wide_local_output W32 32 Hcall Hobs Hpre Hfld Hpres cursor.
Qed.

Theorem add64_local_spec :
  jet_local_spec f_simplicity_add_64 (Ty.Prod (Word 6) (Word 6)) (Ty.Prod Bit (Word 6))
    (fun a => @add64_spec Alg.CoreFunSem a).
Proof.
  intros m bd dbase bs sbase bi bw edge outedge cursor rc [x y] HB HA HF H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Ty.Prod (Word 6) (Word 6)))) with 128 in Hmax.
  change (Z.of_nat (bitSize (Ty.Prod Bit (Word 6)))) with (64 + 1) in *.
  pose proof (write_frame_at_count _ _ _ _ _ _ _ Hout) as HC.
  apply frame_input_word_pair_encode in Hin. destruct Hin as [Hx Hy].
  change (Z.of_nat (Nat.pow 2 6)) with 64 in Hy.
  destruct (eval_add64_layout_matches_spec m bd dbase bs sbase bi bw edge outedge x y
    cursor rc HB HA HF ltac:(lia) Hx Hy Hout) as (mf & Hcall & Hobs & Hpre & Hfld & Hpres).
  wide_local_output W64 64 Hcall Hobs Hpre Hfld Hpres cursor.
Qed.

(** * Local replacement for all twelve jets *)

(** For each jet, a represented state that satisfies the noninterference and
    permission premises is carried by the C call to a represented state that is
    also the final state of the Bit Machine translation of the jet's Simplicity
    expression ([Translate.Naive.translate_correct]).  The premises are those of
    [jet_context]; they are local to one call and are not claimed to be
    maintained by the whole evaluator. *)

Definition jet_context_for (f : function) {A B : Ty}
    (t : forall alg : Alg.Core.Algebra, Alg.Core.domain alg A B) : Prop :=
  forall m L (ctx : Context) (a : A),
  let s0 := fillContext ctx
    {| readLocalState := encode a; writeLocalState := newWriteFrame (bitSize B) |} in
  let s1 := fillContext ctx
    {| readLocalState := encode a;
       writeLocalState := fullWriteFrame (encode (@t Alg.CoreFunSem a)) |} in
  bm_rep m L s0 -> bm_separated L s0 -> active_write_writable m L s0 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f) (jet_args L) E0 mf (Vint Int.one) /\
    bm_rep mf L s1 /\ (s0 >>- @t Naive.translate ->> s1).

Ltac size_pos := vm_compute; lia.

Theorem one8_context : jet_context_for f_simplicity_one_8 (@one8_spec).
Proof. exact (jet_context _ _ one8_spec_parametric one8_local_spec ltac:(size_pos)). Qed.
Theorem one16_context : jet_context_for f_simplicity_one_16 (@wide_one_spec W16).
Proof. exact (jet_context _ _ (wide_one_spec_parametric W16) one16_local_spec ltac:(size_pos)). Qed.
Theorem one32_context : jet_context_for f_simplicity_one_32 (@wide_one_spec W32).
Proof. exact (jet_context _ _ (wide_one_spec_parametric W32) one32_local_spec ltac:(size_pos)). Qed.
Theorem one64_context : jet_context_for f_simplicity_one_64 (@wide_one_spec W64).
Proof. exact (jet_context _ _ (wide_one_spec_parametric W64) one64_local_spec ltac:(size_pos)). Qed.

Theorem increment8_context :
  jet_context_for f_simplicity_increment_8 (@increment8_spec).
Proof. exact (jet_context _ _ increment8_spec_parametric increment8_local_spec ltac:(size_pos)). Qed.
Theorem increment16_context :
  jet_context_for f_simplicity_increment_16 (@increment16_spec).
Proof. exact (jet_context _ _ increment16_spec_parametric increment16_local_spec ltac:(size_pos)). Qed.
Theorem increment32_context :
  jet_context_for f_simplicity_increment_32 (@increment32_spec).
Proof. exact (jet_context _ _ increment32_spec_parametric increment32_local_spec ltac:(size_pos)). Qed.
Theorem increment64_context :
  jet_context_for f_simplicity_increment_64 (@increment64_spec).
Proof. exact (jet_context _ _ increment64_spec_parametric increment64_local_spec ltac:(size_pos)). Qed.

Theorem add8_context :
  jet_context_for f_simplicity_add_8 (@add8_spec).
Proof. exact (jet_context _ _ add8_spec_parametric add8_local_spec ltac:(size_pos)). Qed.
Theorem add16_context :
  jet_context_for f_simplicity_add_16 (@add16_spec).
Proof. exact (jet_context _ _ add16_spec_parametric add16_local_spec ltac:(size_pos)). Qed.
Theorem add32_context :
  jet_context_for f_simplicity_add_32 (@add32_spec).
Proof. exact (jet_context _ _ add32_spec_parametric add32_local_spec ltac:(size_pos)). Qed.
Theorem add64_context :
  jet_context_for f_simplicity_add_64 (@add64_spec).
Proof. exact (jet_context _ _ add64_spec_parametric add64_local_spec ltac:(size_pos)). Qed.
