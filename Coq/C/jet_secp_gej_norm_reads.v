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
  lframe (fun b _=>b<>bp /\ b<>bl /\ ~extA m0 bd bw bi b) m mt.
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
              ** split;[exact Final|];eapply lframe_trans;[exact ReadFrame|].
                 eapply lframe_implies;[exact TagFrame|];intros b pos (NP & NL & NE) V;
                   split;intro E;subst b;contradiction.
Qed.
