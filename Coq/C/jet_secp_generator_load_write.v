(** Original generator loader followed by the original affine writer, as in
    hash_to_curve. This closes the final representation/serialization span. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_toZ C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_frame_inv C.jet_output_layout
  C.jet_secp_linkage C.jets_secp C.jet_secp_generator_load_storage C.jet_secp_generator_load_values
  C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_b32_exec C.jet_secp_square_columns
  C.jet_secp_square_spec_bridge C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_rescale_literal C.jet_secp_swu_public_rest C.jet_secp_gej_negate_literal
  C.jet_secp_write_fe_numeric C.jet_secp_multiply_input_input
  C.jet_secp_multiply_checkpoint_columns
  C.jet_secp_curve_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode rescale_field_output.

Definition generator_loaded_words bytes := limb_rho (be_val bytes).
Definition generator_loaded_output xs ys :=
  (rescale_field_output (generator_loaded_words xs),rescale_field_output (generator_loaded_words ys)).
Lemma generator_loaded_bounds bytes : length bytes=32%nat -> Forall (fun x=>0<=x<=255) bytes ->
  square_input_bounds (generator_loaded_words bytes).
Proof.
  intros Len Bytes i Index;pose proof (limb_rho_bound _ (be_32_bytes_bound bytes Len Bytes) i) as Bound.
  change (0<=Int64.unsigned (generator_loaded_words bytes i)<=4503599627370495) in Bound.
  destruct (Nat.eqb i 4);lia.
Qed.
Lemma generator_loaded_output_value bytes : length bytes=32%nat -> Forall (fun x=>0<=x<=255) bytes ->
  @toZ (WordToZ 8) (rescale_field_output (generator_loaded_words bytes))=be_val bytes mod field_prime.
Proof.
  intros Len Bytes;rewrite rescale_field_output_value;unfold generator_loaded_words.
  rewrite radix_limb_rho by (apply be_32_bytes_bound;assumption);reflexivity.
Qed.

Theorem eval_generator_load_write m0 bd base bw edge cursor N bi (rc:Z) xs ys m bp bg :
  write_frame_at m0 bd base bw edge cursor N -> 512<=N ->
  finv m0 bd base bw edge cursor N bi m false [] ->
  length xs=32%nat -> length ys=32%nat ->
  Forall (fun x=>0<=x<=255) xs -> Forall (fun y=>0<=y<=255) ys -> bp<>bg ->
  Mem.range_perm m bp 0 88 Cur Freeable -> Mem.range_perm m bg 0 64 Cur Freeable ->
  xsep (extA m0 bd bw bi) [(bp,0);(bg,0)] ->
  (forall i,(i<64)%nat -> Mem.load Mint8unsigned m bg (Z.of_nat i)=Some (Vint (Int.repr (nth i (xs++ys) 0)))) ->
  exists mr mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_generator_load)
    [Vptr bp Ptrofs.zero;Vptr bg Ptrofs.zero] E0 mr Vundef /\
  Clight2.eval_funcall secp_ge mr (Internal f_write_ge)
    [Vptr bd (Ptrofs.repr base);Vptr bp Ptrofs.zero] E0 mf Vundef /\
  finv m0 bd base bw edge cursor N bi mf true
    (@Simplicity.Translate.encode (Ty.Prod (Word 8) (Word 8)) (generator_loaded_output xs ys)) /\
  Mem.range_perm mf bp 0 88 Cur Freeable /\ Mem.range_perm mf bg 0 64 Cur Freeable /\
  lframe (fun b _=>b<>bp /\ b<>bg /\ ~extA m0 bd bw bi b) m mf /\ readonly_preserved m mf.
Proof.
  intros Output Cap Inv LX LY BX BY Sep FP FG External Source.
  assert (OutP:~extA m0 bd bw bi bp) by exact (External 0%nat ltac:(clear;cbn;lia)).
  assert (OutG:~extA m0 bd bw bi bg) by exact (External 1%nat ltac:(clear;cbn;lia)).
  destruct (eval_generator_load_from_storage xs ys m bp bg LX LY BX BY Sep FP FG Source)
    as (mr & Load & X & Y & Flag & FPR & FGR & InputR & FrameR & ReadOnlyR).
  rewrite swu_limb_list_words in X,Y.
  assert (InvR:finv m0 bd base bw edge cursor N bi mr false []).
  { eapply finv_stable;[exact Output|exact Inv|].
    eapply lframe_implies;[exact FrameR|];intros b pos Ext Valid;split;intro Same;subst b;contradiction. }
  assert (WriteSep:xsep (extA m0 bd bw bi) [(bp,0)]).
  { intros [|i] Bound;[exact OutP|clear -Bound;cbn in Bound;lia]. }
  destruct (swu_literal_writer m0 bd base bw edge cursor N bi rc mr bp
    (generator_loaded_words xs) (generator_loaded_words ys) (generator_loaded_output xs ys)
    Output Cap InvR (generator_loaded_bounds xs LX BX) (generator_loaded_bounds ys LY BY) X Y FPR WriteSep eq_refl)
    as (mf & Write & Final & FPF & FrameW).
  assert (FGF:Mem.range_perm mf bg 0 64 Cur Freeable) by
    (eapply curve_keep_free;[clear;lia|exact FGR|exact FrameW|intros;split;[congruence|exact OutG] ]).
  exists mr,mf;split;[exact Load|];split;[exact Write|];split;[exact Final|];
    split;[exact FPF|];split;[exact FGF|];split.
  - eapply lframe_trans.
    + eapply lframe_implies;[exact FrameR|];intros b pos [NP [NG NE]] Valid;split;assumption.
    + eapply lframe_implies;[exact FrameW|];intros b pos [NP [NG NE]] Valid;split;assumption.
  - eapply preserved_trans;[exact ReadOnlyR|eapply swu_writer_readonly;exact Write].
Qed.
