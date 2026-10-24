(** Discharge every original public SWU remainder call from arbitrary frame
    cursors and owned locals. The original CTZ contract remains explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.extraMath C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
  C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_swu_public_boundary C.jet_secp_swu_public_body C.jet_secp_swu_function C.jet_secp_swu_startup
  C.jet_secp_swu_literal C.jet_secp_multiply_input_reader C.jet_secp_rescale_public_reads
  C.jet_secp_curve_frame C.jet_secp_square_spec_bridge C.jet_secp_multiply_normalize_bridge
  C.jet_secp_point_three_reads C.jet_secp_write_ge_general C.jet_secp_rescale_writer
  C.jet_secp_rescale_literal C.jet_secp_gej_negate_literal C.jet_secp_field_io_preserve
  C.jet_secp_square_columns
  C.jet_secp_fe_math C.jet_secp_multiply_input_input
  C.jet_secp_b32_exec
  C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode square_reader_rho literal_swu.

Lemma swu_writer_closed : closed_stmtb field_io_helpers (fn_body f_write_ge)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma swu_writer_readonly m args mf :
  Clight2.eval_funcall secp_ge m (Internal f_write_ge) args E0 mf Vundef -> readonly_preserved m mf.
Proof.
  intro Run;inversion Run;subst.
  eapply preserved_trans;[eapply entry_preserved;eassumption|].
  eapply preserved_trans;[|eapply freelist_preserved;eassumption].
  eapply (proj1 (internal_exec_preserved _ _ field_io_helpers_ok));
    [eassumption|eapply entry_plain;[eassumption|reflexivity]|exact swu_writer_closed].
Qed.

Lemma swu_output_encoding x y (result:Ty.tySem (Ty.Prod (Word 8) (Word 8))) :
  (rescale_field_output x,rescale_field_output y)=result ->
  (Simplicity.Translate.encode (rescale_field_output x)++Simplicity.Translate.encode (rescale_field_output y))=
    Simplicity.Translate.encode result.
Proof.
  intro Match;pose proof (f_equal (@Simplicity.Translate.encode (Ty.Prod (Word 8) (Word 8))) Match) as Enc.
  rewrite point_encode_pair in Enc;exact Enc.
Qed.

Lemma swu_literal_writer m0 bd base bw edge cursor N bi (rc:Z) m bp x y
    (result:Ty.tySem (Ty.Prod (Word 8) (Word 8))) :
  write_frame_at m0 bd base bw edge cursor N -> 512<=N ->
  finv m0 bd base bw edge cursor N bi m false [] ->
  square_input_bounds x -> square_input_bounds y ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) ->
  Mem.range_perm m bp 0 88 Cur Freeable -> xsep (extA m0 bd bw bi) [(bp,0)] ->
  (rescale_field_output x,rescale_field_output y)=result -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_write_ge)
    [Vptr bd (Ptrofs.repr base);Vptr bp Ptrofs.zero] E0 mf Vundef /\
  finv m0 bd base bw edge cursor N bi mf true (Simplicity.Translate.encode result) /\
  Mem.range_perm mf bp 0 88 Cur Freeable /\
  lframe (fun b _=>b<>bp /\ ~extA m0 bd bw bi b) m mf.
Proof.
  intros Output Cap Inv BX BY X Y Free Sep Match;rewrite <-rescale_point_limbs in X,Y.
  destruct (eval_write_ge_general m0 bd base bw edge cursor N bi rc m bp
    (rescale_point_field x) (rescale_point_field y) Output Cap Inv
    (rescale_point_bounds _ BX) (rescale_point_bounds _ BY) X Y Free Sep)
    as (mf & Write & Final & FPF & Frame).
  rewrite !rescale_point_output,(swu_output_encoding x y result Match) in Final.
  exists mf;split;[exact Write|];split;[exact Final|];split;[exact FPF|exact Frame].
Qed.

Lemma eval_swu_map_write m0 bd base bw outedge cursor N bi (rc:Z)
    (t:Ty.tySem (Word 8)) m bt bp bl :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  swu_startup m -> write_frame_at m0 bd base bw outedge cursor N -> 512<=N ->
  fe_at m bt 0 (words5 (square_reader_rho t)) ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bp 0 88 Cur Freeable ->
  Mem.range_perm m bl 0 16 Cur Freeable -> bt<>bl -> bp<>bl -> bt<>bp ->
  xsep (extA m0 bd bw bi) [(bt,0);(bp,0);(bl,0)] ->
  finv m0 bd base bw outedge cursor N bi m false [] -> exists mn mf,
  Clight2.eval_funcall secp_ge m (Internal f_shallue_van_de_woestijne)
    [Vptr bp Ptrofs.zero;Vptr bt Ptrofs.zero] E0 mn Vundef /\
  Clight2.eval_funcall secp_ge mn (Internal f_write_ge)
    [Vptr bd (Ptrofs.repr base);Vptr bp Ptrofs.zero] E0 mf Vundef /\
  finv m0 bd base bw outedge cursor N bi mf true
    (Simplicity.Translate.encode (@literal_swu Simplicity.Alg.CoreFunSem t)) /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bp 0 88 Cur Freeable /\
  Mem.range_perm mf bl 0 16 Cur Freeable /\
  lframe (rescale_locals_outside m0 bd bw bi bt bp bl) m mf /\ swu_startup mf /\ readonly_preserved m mf.
Proof.
  intros Count Ready Output Cap Field FT FP FL TL PL TP Sep Inv.
  assert (OutT:~extA m0 bd bw bi bt) by exact (Sep 0%nat ltac:(abstract (cbn;lia))).
  assert (OutP:~extA m0 bd bw bi bp) by exact (Sep 1%nat ltac:(abstract (cbn;lia))).
  destruct (eval_swu_function t m bp bt Count ltac:(congruence) Ready Field FT FP)
    as (mn & x & y & Map & X & Y & Flag & FTN & FPN & BX & BY & Literal & ReadyN & FrameN & ReadOnlyN).
  assert (InvN:finv m0 bd base bw outedge cursor N bi mn false []).
  { eapply finv_stable;[exact Output|exact Inv|].
    eapply lframe_implies;[exact FrameN|];intros b pos Ext Valid;split;intro Same;subst b;contradiction. }
  assert (FLN:Mem.range_perm mn bl 0 16 Cur Freeable) by
    (eapply curve_keep_free;[abstract lia|exact FL|exact FrameN|intros;split;congruence]).
  assert (SepWrite:xsep (extA m0 bd bw bi) [(bp,0)]).
  { intros [|i] Bound;[exact OutP|clear -Bound;cbn in Bound;lia]. }
  destruct (swu_literal_writer m0 bd base bw outedge cursor N bi rc mn bp x y
    (@literal_swu Simplicity.Alg.CoreFunSem t) Output Cap InvN BX BY X Y FPN SepWrite Literal)
    as (mf & Write & Final & FPF & FrameW).
  assert (FTF:Mem.range_perm mf bt 0 40 Cur Freeable) by
    (eapply curve_keep_free;[abstract lia|exact FTN|exact FrameW|intros;split;[exact TP|exact OutT] ]).
  assert (FLF:Mem.range_perm mf bl 0 16 Cur Freeable).
  { eapply curve_keep_free;[abstract lia|exact FLN|exact FrameW|];intros;split;[congruence|].
    exact (Sep 2%nat ltac:(abstract (cbn;lia))). }
  pose proof (swu_writer_readonly _ _ _ Write) as ReadOnlyW.
  exists mn,mf;split;[exact Map|];split;[exact Write|];split;[exact Final|];
    split;[exact FTF|];split;[exact FPF|];split;[exact FLF|];split.
  - eapply lframe_trans.
    + eapply lframe_implies;[exact FrameN|];intros b pos (NT & NP & NL & NE) Valid;split;assumption.
    + eapply lframe_implies;[exact FrameW|];intros b pos (NT & NP & NL & NE) Valid;split;assumption.
  - split;[eapply swu_startup_preserved;[exact ReadyN|exact ReadOnlyW]|].
    eapply preserved_trans;[exact ReadOnlyN|exact ReadOnlyW].
Qed.

Lemma swu_limb_list_words (value:Z) : map Int64.repr (fe_limbs_of value)=words5 (limb_rho value).
Proof. reflexivity. Qed.
Lemma swu_reader_digits t : map Int64.repr (fe_limbs_of (normalized_value t))=
  words5 (square_reader_rho t).
Proof.
  Local Transparent square_reader_rho.
  unfold square_reader_rho;apply swu_limb_list_words.
Qed.
Local Opaque square_reader_rho.
Lemma swu_reader_field t m b :
  fe_at m b 0 (map Int64.repr (fe_limbs_of (normalized_value t))) ->
  fe_at m b 0 (words5 (square_reader_rho t)).
Proof. rewrite <-swu_reader_digits;exact (fun Field=>Field). Qed.

Theorem exec_swu_public_rest_owned le m0 bd base bw outedge cursor N bi edge rc
    (t:Ty.tySem (Word 8)) m bt bp bl :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  swu_startup m -> le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
  write_frame_at m0 bd base bw outedge cursor N -> 512<=N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits t)) ->
  0<=rc -> rc+256<=Int64.max_unsigned ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bp 0 88 Cur Freeable ->
  Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
  bt<>bl -> bp<>bl -> bt<>bp -> xsep (extA m0 bd bw bi) [(bt,0);(bp,0);(bl,0)] ->
  finv m0 bd base bw outedge cursor N bi m false [] -> exists mf,
  Clight2.exec_stmt secp_ge (swu_public_env bl bt bp) le m swu_public_rest E0 le mf
    (Out_return (Some (Vint Int.one,tint))) /\
  finv m0 bd base bw outedge cursor N bi mf true
    (Simplicity.Translate.encode (@literal_swu Simplicity.Alg.CoreFunSem t)) /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bp 0 88 Cur Freeable /\
  Mem.range_perm mf bl 0 16 Cur Freeable /\
  lframe (rescale_locals_outside m0 bd bw bi bt bp bl) m mf /\ swu_startup mf /\ readonly_preserved m mf.
Proof.
  intros Count Ready Dst Output Cap Input RC Max FT FP FL Source TL PL TP Sep Inv.
  assert (OutT:~extA m0 bd bw bi bt) by exact (Sep 0%nat ltac:(abstract (cbn;lia))).
  assert (OutP:~extA m0 bd bw bi bp) by exact (Sep 1%nat ltac:(abstract (cbn;lia))).
  assert (OutL:~extA m0 bd bw bi bl) by exact (Sep 2%nat ltac:(abstract (cbn;lia))).
  assert (SepRead:xsep (extA m0 bd bw bi) [(bt,0);(bl,0)]).
  { intros [|[|i]] Bound;[exact OutT|exact OutL|clear -Bound;cbn in Bound;lia]. }
  destruct (eval_read_fe_with_cursor m0 bd base bw outedge cursor N bi edge rc t m bt bl
    Output ltac:(clear -Cap;lia) Input RC Max FT FL Source TL SepRead Inv)
    as (mr & Read & Field & FTR & FLR & SourceR & InvR & FrameR).
  pose proof (swu_reader_field t mr bt Field) as NormalizedField.
  assert (VP:Mem.valid_block m bp) by (eapply Mem.perm_valid_block;apply (FP 0);abstract lia).
  pose proof (reader_preserves_other (extA m0 bd bw bi) bt bl bi (Ptrofs.repr edge) m mr bp
    ltac:(congruence) PL OutP VP FrameR) as KeepP.
  assert (FPR:Mem.range_perm mr bp 0 88 Cur Freeable) by
    (eapply curve_keep_free;[abstract lia|exact FP|exact KeepP|intros;reflexivity]).
  pose proof (field_reader_preserved _ _ _ _ _ Read) as ReadOnlyR.
  assert (ReadyR:swu_startup mr) by (eapply swu_startup_preserved;[exact Ready|exact ReadOnlyR]).
  destruct (eval_swu_map_write m0 bd base bw outedge cursor N bi rc t mr bt bp bl
    Count ReadyR Output Cap NormalizedField FTR FPR FLR TL PL TP Sep InvR)
    as (mn & mf & Map & Write & Final & FTF & FPF & FLF & FrameN & ReadyF & ReadOnlyN).
  assert (ReadOnly:readonly_preserved m mf) by
    (eapply preserved_trans;[exact ReadOnlyR|exact ReadOnlyN]).
  exists mf;split;[eapply exec_swu_public_from_calls;eassumption|].
  split;[exact Final|];split;[exact FTF|];split;[exact FPF|];split;[exact FLF|];split.
  - eapply lframe_trans.
    + eapply lframe_implies;[exact FrameR|];intros b pos (NT & NP & NL & NE) Valid.
      split;[exact Valid|];split;[|exact NE];intro Foot;apply two_read_foot_owner in Foot;destruct Foot;contradiction.
    + exact FrameN.
  - split;[exact ReadyF|exact ReadOnly].
Qed.
