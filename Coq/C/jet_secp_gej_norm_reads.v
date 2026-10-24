(** Actual XYZ reader and caller header, retaining the fields needed by the
    finite normalization branch. No inverse execution is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.BitMachine.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_exec C.jet_readBit_layout C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_curve_frame.
Require Import C.jet_secp_wrapper_run C.jet_secp_point_three_reads C.jet_secp_read_gej_fields.
Require Import C.jet_secp_square_spec_bridge C.jet_secp_multiply_normalize_bridge C.jet_secp_rescale_public_reads.
Require Import C.jet_secp_canonical_zero C.jet_secp_gej_predicate_body C.jet_secp_gej_norm_branch C.jet_secp_gej_norm_infinity.
Require Import C.jet_toZ C.jet_secp_fe_inv_prefix C.jet_secp_fe_math C.jet_secp_rescale_literal.
Require Import C.jet_secp_modinfo_fe_caller.
Require Import C.jet_secp_gej_affine_entry C.jet_secp_gej_affine_arithmetic.
Require Import C.jet_secp_fe_inv_statements C.jet_secp_modinv_var_entry C.jet_secp_signed62_numeric.
Require Import C.jet_sx_rep C.jet_secp_modinfo_fe_global C.jet_secp_square_columns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_is_zero square_reader_rho.

Lemma affine_inverse_reader_value (z:Ty.tySem Word256) :
  fe_inv_value(square_reader_rho z)=@toZ (WordToZ 8) z mod feP.
Proof.
  unfold fe_inv_value;rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue.
Qed.

Theorem exec_gej_norm_read_and_tag m0 bd base bw edge cursor N bi inedge rc le m bl bp br
    (x y z:Ty.tySem Word256) :
  le!_dst=Some(Vptr bd(Ptrofs.repr base)) -> write_frame_at m0 bd base bw edge cursor N -> 513<=N ->
  frame_input_cells_at m0 bi inedge rc (map Some(frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi inedge (rc+256)(map Some(frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi inedge (rc+512)(map Some(frame_input_word_bits z)) ->
  0<=rc -> rc+768<=Int64.max_unsigned ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  Mem.range_perm m br 0 88 Cur Freeable -> frame_fields_at m bl 0 bi inedge rc ->
  bp<>bl -> br<>bp -> br<>bl -> xsep (extA m0 bd bw bi) [(bp,0);(br,0);(bl,0)] ->
  finv m0 bd base bw edge cursor N bi m false [] -> exists mt,
  Clight2.exec_stmt secp_ge (gej_norm_env bl bp br) le m
    (Ssequence gej_predicate_read_stmt gej_norm_header) E0
    (gej_norm_tagged le (Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z))) mt Out_normal /\
  fe_at mt bp 0 (words5(square_reader_rho x)) /\
  fe_at mt bp 40 (words5(square_reader_rho y)) /\
  fe_at mt bp 80 (words5(square_reader_rho z)) /\
  Mem.load Mint32 mt bp 120=Some(Vint(bit_int(Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)))) /\
  frame_fields_at mt bl 0 bi inedge (rc+768) /\
  Mem.range_perm mt bp 0 128 Cur Freeable /\ Mem.range_perm mt bl 0 16 Cur Freeable /\
  Mem.range_perm mt br 0 88 Cur Freeable /\
  finv m0 bd base bw edge cursor N bi mt true [Some(negb(Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)))] /\
  lframe (fun b _=>b<>bp /\ b<>bl /\ ~extA m0 bd bw bi b) m mt /\
  (modinfo_fe_state m -> modinfo_fe_global_rep mt).
Proof.
  intros Dst Output Cap IX IY IZ RC Max FP FL FR Source PL RP RL Sep Inv.
  assert(SepRead:xsep (extA m0 bd bw bi) [(bp,0);(bl,0)]).
  { intros [|[|r]] Bound;[exact(Sep 0%nat ltac:(cbn;lia))|exact(Sep 2%nat ltac:(cbn;lia))|cbn in Bound;lia]. }
  assert(ReadInv:invA m0 bd base bw edge cursor N bi rc false [] 513
    (read_fe_rho(frame_input_word_bits x)rc) [] m).
  { split;[reflexivity|];split;[exact Inv|];split;[exact Cap|cbn;lia]. }
  destruct(eval_read_gej_canonical_fields m0 bd base bw edge cursor N 513 bi inedge rc
    x y z m bp bl Output IX IY IZ RC Max FP FL Source PL SepRead ReadInv)
    as (mr & Read & XR & YR & ZR & FlagR & SourceR & FPR & FLR & InvR & ReadFrame).
  rewrite !rescale_reader_limbs in XR,YR,ZR.
  destruct InvR as [_ [FinR _]].
  change(finv m0 bd base bw edge cursor N bi mr false []) in FinR.
  assert(NotR:~extA m0 bd bw bi br) by (exact(Sep 1%nat ltac:(cbn;lia))).
  assert(FRR:Mem.range_perm mr br 0 88 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FR|exact ReadFrame|];intros;split;[exact RP|];split;assumption. }
  destruct(exec_gej_norm_header m0 bd base bw edge cursor N bi le mr bl bp br
    (Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)) Dst Output ltac:(lia) FinR FlagR)
    as (mt & Header & Final & TagFrame & TagPerm).
  assert(ED:extA m0 bd bw bi bd) by (apply(fext_bd m0 bd base bw edge cursor N bi Output)).
  assert(EW:extA m0 bd bw bi bw).
  { split;[right;left;reflexivity|];eapply bw_valid;[exact Output|lia]. }
  assert(PD:bp<>bd) by (intro E;subst bp;exact(Sep 0%nat ltac:(cbn;lia) ED)).
  assert(PW:bp<>bw) by (intro E;subst bp;exact(Sep 0%nat ltac:(cbn;lia) EW)).
  assert(LD:bl<>bd) by (intro E;subst bl;exact(Sep 2%nat ltac:(cbn;lia) ED)).
  assert(LW:bl<>bw) by (intro E;subst bl;exact(Sep 2%nat ltac:(cbn;lia) EW)).
  assert(FlagT:Mem.load Mint32 mt bp 120=Some(Vint(bit_int(Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z))))).
  { rewrite(proj1 TagFrame);[exact FlagR|eapply load_valid;exact FlagR|intros;split;assumption]. }
  assert(SourceT:frame_fields_at mt bl 0 bi inedge (rc+768)).
  { destruct SourceR as [HE HO];assert(VL:Mem.valid_block mr bl) by (eapply load_valid;exact HE).
    split;rewrite(proj1 TagFrame) by (auto);assumption. }
  exists mt;split.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le);
      [apply exec_gej_norm_read;exact Read|exact Header].
  - split.
    + eapply curve_keep_field_range;[reflexivity|exact XR|exact TagFrame|];intros;split;assumption.
    + split.
      * eapply curve_keep_field_range;[reflexivity|exact YR|exact TagFrame|];intros;split;assumption.
      * split.
        -- eapply curve_keep_field_range;[reflexivity|exact ZR|exact TagFrame|];intros;split;assumption.
        -- split;[exact FlagT|];split;[exact SourceT|];split.
           ++ intros pos Hr;apply TagPerm,FPR;exact Hr.
           ++ split;[intros pos Hr;apply TagPerm,FLR;exact Hr|];split.
              ** intros pos Hr;apply TagPerm,FRR;exact Hr.
              ** split;[exact Final|];split.
                 --- eapply lframe_trans;[exact ReadFrame|].
                     eapply lframe_implies;[exact TagFrame|];intros b pos (NP & NL & NE) V;
                       split;intro E;subst b;contradiction.
                 --- intro Global.
                     pose proof(finv_wframe m0 bd base bw edge cursor N bi Output mr false [] FinR) as Current.
                     change(write_frame_at mr bd base bw edge (cursor-0) (N-0)) in Current.
                     rewrite !Z.sub_0_r in Current.
                     eapply frame_write_keeps_modinfo;[exact Current|lia|exact TagFrame|].
                     eapply read_gej_preserves_modinfo;[exact Read|exact Global].
Qed.

(** From the caller's input cells to the actual nested inverse entry. The
    modulus is required only before reading, not postulated afterwards.
    This is an execution prefix: the modular-inverse call is still open. *)
Theorem gej_norm_finite_enters_inverse m0 bd base bw edge cursor N bi inedge rc le m bl bp br
    (x y z:Ty.tySem Word256) :
  le!_dst=Some(Vptr bd(Ptrofs.repr base)) -> write_frame_at m0 bd base bw edge cursor N -> 513<=N ->
  frame_input_cells_at m0 bi inedge rc (map Some(frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi inedge (rc+256)(map Some(frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi inedge (rc+512)(map Some(frame_input_word_bits z)) ->
  0<=rc -> rc+768<=Int64.max_unsigned ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  Mem.range_perm m br 0 88 Cur Freeable -> frame_fields_at m bl 0 bi inedge rc ->
  bp<>bl -> br<>bp -> br<>bl -> xsep (extA m0 bd bw bi) [(bp,0);(br,0);(bl,0)] ->
  finv m0 bd base bw edge cursor N bi m false [] -> modinfo_fe_state m ->
  Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)=false ->
  exists mt b2 b3 ma bt bs mi mf,
  Clight2.exec_stmt secp_ge (gej_norm_env bl bp br) le m
    (Ssequence gej_predicate_read_stmt gej_norm_header) E0 (gej_norm_tagged le false) mt Out_normal /\
  function_entry2 secp_ge f_secp256k1_ge_set_gej_var [Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero]
    mt (affine_local_env b2 b3) (affine_entry_temps br bp) ma /\
  Clight2.exec_stmt secp_ge (affine_local_env b2 b3) (affine_entry_temps br bp) ma affine_flag_statement
    E0 (affine_finite_temps br bp) ma Out_normal /\
  eval_exprlist secp_ge (affine_local_env b2 b3) (affine_finite_temps br bp) ma
    [affine_point_address _z;affine_point_address _z] (type_of_params(fn_params f_secp256k1_fe_inv_var))
    [Vptr bp(Ptrofs.repr 80);Vptr bp(Ptrofs.repr 80)] /\
  function_entry2 secp_ge f_secp256k1_fe_inv_var [Vptr bp(Ptrofs.repr 80);Vptr bp(Ptrofs.repr 80)] ma
    (fe_inv_env bt bs) (fe_inv_slice_temps bp 80 bp 80) mi /\
  Clight2.exec_stmt secp_ge (fe_inv_env bt bs) (fe_inv_slice_temps bp 80 bp 80) mi fe_inv_prefix
    E0 (fe_inv_slice_temps bp 80 bp 80) mf Out_normal /\
  rep (fe_inv_packed_words(square_reader_rho z)) [(bs,0);(modinfo_fe_block,0)] inv_start_regs mf /\
  signed62_normalized(fe_inv_packed_words(square_reader_rho z)) /\
  signed62_unsigned_value(fe_inv_packed_words(square_reader_rho z))=@toZ (WordToZ 8) z mod feP /\
  fe_at mf bs 0 (words5(fe_inv_packed_words(square_reader_rho z))) /\
  fe_at mf bp 0 (words5(square_reader_rho x)) /\
  fe_at mf bp 40 (words5(square_reader_rho y)) /\
  fe_at mf bp 80 (words5(square_reader_rho z)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
  Mem.range_perm mf bl 0 16 Cur Freeable /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  modinfo_fe_global_rep mf /\ finv m0 bd base bw edge cursor N bi mf true [Some true] /\
  b2<>b3 /\ ~Mem.valid_block mt b2 /\ ~Mem.valid_block mt b3 /\
  bt<>bs /\ ~Mem.valid_block ma bt /\ ~Mem.valid_block ma bs /\
  lframe (fun b _=>b<>bp /\ b<>bl /\ ~extA m0 bd bw bi b) m mf.
Proof.
  intros Dst Output Cap IX IY IZ RC Max FP FL FR Source PL RP RL Sep Inv Global Nonzero.
  destruct(exec_gej_norm_read_and_tag m0 bd base bw edge cursor N bi inedge rc le m bl bp br
    x y z Dst Output Cap IX IY IZ RC Max FP FL FR Source PL RP RL Sep Inv)
    as (mt & ReadTag & X & Y & Z & Flag & Cursor & FPT & FLT & FRT & Tag & Frame & KeepGlobal).
  rewrite Nonzero in ReadTag,Flag,Tag;cbn [bit_int negb] in Flag,Tag.
  destruct(affine_entry_to_inverse_core (square_reader_rho z) mt bp br (square_reader_bounds z)
    Z Flag (KeepGlobal Global) FPT FRT)
    as (b2 & b3 & ma & bt & bs & mi & mf & AffineEntry & Finite & Args & InverseEntry & Prepare & Core & Packed & ZF & FPF & FRF & F2 & F3 & FT & FS & Normalized & Numeric & GlobalF & Separate & New2 & New3 & TS & NewT & NewS & InverseFrame).
  assert(XF:fe_at mf bp 0 (words5(square_reader_rho x))).
  { eapply curve_keep_field_range;[reflexivity|exact X|exact InverseFrame|];intros;exact I. }
  assert(YF:fe_at mf bp 40 (words5(square_reader_rho y))).
  { eapply curve_keep_field_range;[reflexivity|exact Y|exact InverseFrame|];intros;exact I. }
  assert(FLF:Mem.range_perm mf bl 0 16 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FLT|exact InverseFrame|];intros;exact I. }
  assert(TagF:finv m0 bd base bw edge cursor N bi mf true [Some true]).
  { eapply finv_stable;[exact Output|exact Tag|].
    eapply lframe_implies;[exact InverseFrame|];intros;exact I. }
  rewrite affine_inverse_reader_value in Numeric.
  assert(FrameF:lframe (fun b _=>b<>bp /\ b<>bl /\ ~extA m0 bd bw bi b) m mf).
  { eapply lframe_trans;[exact Frame|].
    eapply lframe_implies;[exact InverseFrame|];intros;exact I. }
  exists mt,b2,b3,ma,bt,bs,mi,mf;repeat first[assumption|split].
Qed.
