(** Original affine conversion followed by generator save/load and write.
    The finite branch retains the previously explicit CTZ boundary; the
    infinity branch has no CTZ premise. Neither is the whole public caller. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Translate.
Require Import C.extraMath C.jet_toZ C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_frame_inv C.jet_output_layout
  C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_curve_frame
  C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_rescale_literal
  C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_multiply_checkpoint_columns
  C.jet_secp_modinfo_fe_caller C.jet_secp_fe_inverse_state C.jet_secp_invert_literal C.jet_secp_fe_inv_prefix
  C.jet_secp_affine_inverse_complete C.jet_secp_affine_infinite
  C.jet_secp_generator_field_roundtrip C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode point_mul_words square_words rescale_field_output.

Theorem eval_generator_finite_affine_roundtrip m0 bd base bw edge cursor N bi (rc:Z) x y z m bp br bg :
  (forall mc w,Int64.unsigned w<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong w]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned w))))) ->
  write_frame_at m0 bd base bw edge cursor N -> 512<=N ->
  finv m0 bd base bw edge cursor N bi m false [] ->
  bp<>br -> bp<>bg -> br<>bg ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  Mem.load Mint32 m bp 120=Some (Vint Int.zero) -> modinfo_fe_state m ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable ->
  Mem.range_perm m bg 0 64 Cur Freeable -> xsep (extA m0 bd bw bi) [(bp,0);(br,0);(bg,0)] ->
  exists zi ma ms ml mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_gej_var)
    [Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero] E0 ma Vundef /\
  Clight2.eval_funcall secp_ge ma (Internal f_secp256k1_generator_save)
    [Vptr bg Ptrofs.zero;Vptr br Ptrofs.zero] E0 ms Vundef /\
  Clight2.eval_funcall secp_ge ms (Internal f_secp256k1_generator_load)
    [Vptr br Ptrofs.zero;Vptr bg Ptrofs.zero] E0 ml Vundef /\
  Clight2.eval_funcall secp_ge ml (Internal f_write_ge)
    [Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero] E0 mf Vundef /\
  finv m0 bd base bw edge cursor N bi mf true
    (@Simplicity.Translate.encode (Ty.Prod (Word 8) (Word 8))
      (rescale_field_output (point_mul_words x (square_words zi)),
       rescale_field_output (point_mul_words y (point_mul_words zi (square_words zi))))) /\
  radix_value zi=literal_invert_numeric (fe_inv_value z) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
  Mem.range_perm mf bg 0 64 Cur Freeable /\
  lframe (fun b _=>b<>bp /\ b<>br /\ b<>bg /\ ~extA m0 bd bw bi b) m mf /\ readonly_preserved m mf.
Proof.
  intros CountCall Output Cap Inv PR PG RG BX BY BZ X Y Z Flag Ready FP FR FG External.
  assert (OutP:~extA m0 bd bw bi bp) by exact (External 0%nat ltac:(clear;cbn;lia)).
  assert (OutR:~extA m0 bd bw bi br) by exact (External 1%nat ltac:(clear;cbn;lia)).
  assert (OutG:~extA m0 bd bw bi bg) by exact (External 2%nat ltac:(clear;cbn;lia)).
  assert (SerialSep:xsep (extA m0 bd bw bi) [(br,0);(bg,0)]).
  { intros [|[|i]] Index;[exact OutR|exact OutG|clear -Index;cbn in Index;lia]. }
  destruct (eval_affine_finite_initialized x y z m bp br CountCall PR BX BY BZ X Y Z Flag Ready FP FR)
    as (zi & ma & Affine & XA & YA & FlagA & FPA & FRA & BXA & BYA & Inverse & VX & VY & ReadyA & FrameA & ReadonlyA).
  assert (FGA:Mem.range_perm ma bg 0 64 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FG|exact FrameA|intros;split;congruence]. }
  assert (InvA:finv m0 bd base bw edge cursor N bi ma false []).
  { eapply finv_stable;[exact Output|exact Inv|].
    eapply lframe_implies;[exact FrameA|];intros b pos Ext Valid;split;intro Same;subst b;contradiction. }
  destruct (eval_generator_field_roundtrip m0 bd base bw edge cursor N bi rc
    (point_mul_words x (square_words zi)) (point_mul_words y (point_mul_words zi (square_words zi)))
    Int.zero ma br bg Output Cap InvA RG BXA BYA XA YA FlagA FRA FGA SerialSep)
    as (ms & ml & mf & Save & Load & Write & Final & FRF & FGF & FrameS & ReadonlyS).
  assert (FPF:Mem.range_perm mf bp 0 128 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FPA|exact FrameS|intros;repeat split;assumption]. }
  exists zi,ma,ms,ml,mf;split;[exact Affine|];split;[exact Save|];split;[exact Load|];split;[exact Write|];
    split;[exact Final|];split;[exact Inverse|];split;[exact FPF|];split;[exact FRF|];split;[exact FGF|];split.
  - eapply lframe_trans.
    + eapply lframe_implies;[exact FrameA|];intros b pos [NP [NR [NG NE]]] Valid;split;assumption.
    + eapply lframe_implies;[exact FrameS|];intros b pos [NP [NR [NG NE]]] Valid;repeat split;assumption.
  - eapply preserved_trans;[exact ReadonlyA|exact ReadonlyS].
Qed.

Definition generator_infinite_words (_:nat) : int64 := Int64.zero.
Lemma generator_infinite_bounds : square_input_bounds generator_infinite_words.
Proof.
  intros i Index;unfold generator_infinite_words;change (0<if Nat.eqb i 4 then 4503599627370496 else 72057594037927936).
  destruct (Nat.eqb i 4);lia.
Qed.
Lemma generator_infinite_output_zero :
  @toZ (WordToZ 8) (rescale_field_output generator_infinite_words)=0.
Proof.
  rewrite rescale_field_output_value,radix_value_as_fe_val.
  change (0 mod field_prime=0);apply Z.mod_0_l;rewrite field_prime_matches_normalizer;discriminate.
Qed.

Theorem eval_generator_infinite_affine_roundtrip m0 bd base bw edge cursor N bi (rc:Z) flag m bp br bg :
  write_frame_at m0 bd base bw edge cursor N -> 512<=N ->
  finv m0 bd base bw edge cursor N bi m false [] ->
  bp<>br -> bp<>bg -> br<>bg -> flag<>Int.zero ->
  Mem.load Mint32 m bp 120=Some (Vint flag) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable ->
  Mem.range_perm m bg 0 64 Cur Freeable -> xsep (extA m0 bd bw bi) [(bp,0);(br,0);(bg,0)] ->
  exists ma ms ml mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_gej_var)
    [Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero] E0 ma Vundef /\
  Clight2.eval_funcall secp_ge ma (Internal f_secp256k1_generator_save)
    [Vptr bg Ptrofs.zero;Vptr br Ptrofs.zero] E0 ms Vundef /\
  Clight2.eval_funcall secp_ge ms (Internal f_secp256k1_generator_load)
    [Vptr br Ptrofs.zero;Vptr bg Ptrofs.zero] E0 ml Vundef /\
  Clight2.eval_funcall secp_ge ml (Internal f_write_ge)
    [Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero] E0 mf Vundef /\
  finv m0 bd base bw edge cursor N bi mf true
    (@Simplicity.Translate.encode (Ty.Prod (Word 8) (Word 8))
      (rescale_field_output generator_infinite_words,rescale_field_output generator_infinite_words)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
  Mem.range_perm mf bg 0 64 Cur Freeable /\
  lframe (fun b _=>b<>br /\ b<>bg /\ ~extA m0 bd bw bi b) m mf /\ readonly_preserved m mf.
Proof.
  intros Output Cap Inv PR PG RG Nonzero Flag FP FR FG External.
  assert (OutP:~extA m0 bd bw bi bp) by exact (External 0%nat ltac:(clear;cbn;lia)).
  assert (OutR:~extA m0 bd bw bi br) by exact (External 1%nat ltac:(clear;cbn;lia)).
  assert (OutG:~extA m0 bd bw bi bg) by exact (External 2%nat ltac:(clear;cbn;lia)).
  assert (SerialSep:xsep (extA m0 bd bw bi) [(br,0);(bg,0)]).
  { intros [|[|i]] Index;[exact OutR|exact OutG|clear -Index;cbn in Index;lia]. }
  destruct (eval_affine_infinite_owned m bp br flag PR Nonzero Flag FP FR)
    as (ma & Affine & XA & YA & FlagA & FPA & FRA & FrameA & ReadonlyA).
  assert (FGA:Mem.range_perm ma bg 0 64 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FG|exact FrameA|intros;congruence]. }
  assert (InvA:finv m0 bd base bw edge cursor N bi ma false []).
  { eapply finv_stable;[exact Output|exact Inv|].
    eapply lframe_implies;[exact FrameA|];intros b pos Ext Valid;intro Same;subst b;contradiction. }
  change (fe_at ma br 0 (words5 generator_infinite_words)) in XA.
  change (fe_at ma br 40 (words5 generator_infinite_words)) in YA.
  destruct (eval_generator_field_roundtrip m0 bd base bw edge cursor N bi rc
    generator_infinite_words generator_infinite_words Int.one ma br bg Output Cap InvA RG
    generator_infinite_bounds generator_infinite_bounds XA YA FlagA FRA FGA SerialSep)
    as (ms & ml & mf & Save & Load & Write & Final & FRF & FGF & FrameS & ReadonlyS).
  assert (FPF:Mem.range_perm mf bp 0 128 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FPA|exact FrameS|intros;repeat split;assumption]. }
  exists ma,ms,ml,mf;split;[exact Affine|];split;[exact Save|];split;[exact Load|];split;[exact Write|];
    split;[exact Final|];split;[exact FPF|];split;[exact FRF|];split;[exact FGF|];split.
  - eapply lframe_trans.
    + eapply lframe_implies;[exact FrameA|];intros b pos [NR [NG NE]] Valid;exact NR.
    + exact FrameS.
  - eapply preserved_trans;[exact ReadonlyA|exact ReadonlyS].
Qed.
