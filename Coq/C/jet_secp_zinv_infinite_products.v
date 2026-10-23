(** Four actual arithmetic statements in the original infinity-input branch. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_curve_statements C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_point_mul_storage C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_field_mul_small
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_statement_prefix
 C.jet_secp_zinv_finite C.jet_secp_zinv_shared_preparation C.jet_secp_square_separate_caller
 C.jet_secp_field_product_owned C.jet_secp_point_affine_product C.jet_secp_double_coordinate_numeric
 C.jet_secp_curve_square C.jet_secp_double_statements C.jet_secp_mixed_finite_start.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words.
Definition zinv_infinite_branch := match zinv_a_head with
 | Ssequence _ (Sifthenelse _ branch _) => branch | _ => Sskip end.
Definition zinv_infinite_after_flag := match zinv_infinite_branch with
 | Ssequence _ rest => rest | _ => Sskip end.
Definition zinv_inverse_square_call := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
 [curve_local_address _bzinv2;Etempvar _bzinv (tptr curve_fe_type)].
Definition zinv_inverse_cube_call := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [curve_local_address _bzinv3;curve_local_address _bzinv2;Etempvar _bzinv (tptr curve_fe_type)].
Definition zinv_infinite_coordinate_call (y : bool) := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [double_point_address _r (if y then _y else _x);
  Eaddrof (mixed_b_field (if y then _y else _x) curve_fe_type) (tptr curve_fe_type);
  curve_local_address (if y then _bzinv3 else _bzinv2)].
Definition zinv_infinite_product_statements :=
 [zinv_inverse_square_call;zinv_inverse_cube_call;zinv_infinite_coordinate_call false;zinv_infinite_coordinate_call true].
Definition zinv_infinite_after_products := zinv_statement_drop 4 zinv_infinite_after_flag.
Lemma zinv_infinite_products_source : zinv_infinite_after_flag =
 statement_sequence zinv_infinite_product_statements zinv_infinite_after_products.
Proof. reflexivity. Qed.
Definition zinv_inverse_cube inv := point_mul_words (square_words inv) inv.
Definition zinv_infinite_products_frame (bp ba bb b2 b3 bx : block) pos :=
 (bx<>bp \/ pos<0 \/80<=pos) /\ (bx<>ba \/ pos<0 \/80<=pos) /\ bx<>bb /\ bx<>b2 /\ bx<>b3.
Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HC : _ /\ _ |- _ => destruct HC end;
 repeat match goal with HC : ~(?P \/ ?Q) |- _ =>
   let HP:=fresh "Different" in let HQ:=fresh "Different" in
   assert (HP:~P) by (intro;apply HC;left;assumption);
   assert (HQ:~Q) by (intro;apply HC;right;assumption);clear HC end.
Local Ltac keep_field H F := eapply field_at_lframe;[exact H|exact F|];intro pos;repeat split;try (left;congruence);congruence.
Local Ltac keep_free H F := eapply curve_keep_free;[lia|exact H|exact F|];intro pos;repeat split;try (left;congruence);congruence.
Local Ltac pure_call := unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).

Theorem exec_zinv_infinite_products u v inv e le m bp ba bb b2 b3 :
 le!_r=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) -> le!_bzinv=Some (Vptr bb Ptrofs.zero) ->
 e!_bzinv2=Some (b2,curve_fe_type) -> e!_bzinv3=Some (b3,curve_fe_type) ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> NoDup [bp;ba;bb;b2;b3] ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds inv ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) -> fe_at m bb 0 (words5 inv) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (statement_sequence zinv_infinite_product_statements Sskip) E0 le mf Out_normal /\
 fe_at mf bp 0 (words5 (point_mul_words u (square_words inv))) /\
 fe_at mf bp 40 (words5 (point_mul_words v (zinv_inverse_cube inv))) /\
 fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\ fe_at mf bb 0 (words5 inv) /\
 fe_at mf b2 0 (words5 (square_words inv)) /\ fe_at mf b3 0 (words5 (zinv_inverse_cube inv)) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bb 0 40 Cur Freeable /\ Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
 square_input_bounds (point_mul_words u (square_words inv)) /\
 square_input_bounds (point_mul_words v (zinv_inverse_cube inv)) /\
 lframe (zinv_infinite_products_frame bp ba bb b2 b3) m mf.
Proof.
 intros HR HB HI E2 E3 EQ EM Sep BU BV BI U V Inv PF AF InvF F2 F3;separate_blocks Sep.
 destruct (eval_square_separate_from_storage inv m b2 bb BI F2 Inv InvF ltac:(congruence))
   as (ms & Square & Q & F2S & InvS & InvFS & VQ & BQ & FS).
 assert (US : fe_at ms ba 0 (words5 u)) by (keep_field U FS).
 assert (VS : fe_at ms ba 40 (words5 v)) by (keep_field V FS).
 assert (PFS : Mem.range_perm ms bp 0 128 Cur Freeable) by (keep_free PF FS).
 assert (AFS : Mem.range_perm ms ba 0 88 Cur Freeable) by (keep_free AF FS).
 assert (F3S : Mem.range_perm ms b3 0 40 Cur Freeable) by (keep_free F3 FS).
 destruct (eval_field_product_owned (square_words inv) inv ms b3 b2 bb BQ BI
   ltac:(congruence) ltac:(congruence) ltac:(congruence) F3S Q F2S InvS InvFS)
   as (mc & Cube & C & QC & InvC & F3C & F2C & InvFC & VC & BC & FC).
 assert (UC : fe_at mc ba 0 (words5 u)) by (keep_field US FC).
 assert (VCField : fe_at mc ba 40 (words5 v)) by (keep_field VS FC).
 assert (PFC : Mem.range_perm mc bp 0 128 Cur Freeable) by (keep_free PFS FC).
 assert (AFC : Mem.range_perm mc ba 0 88 Cur Freeable) by (keep_free AFS FC).
 destruct (eval_point_affine_product false u (square_words inv) mc bp ba b2 BU BQ
   ltac:(congruence) ltac:(congruence) ltac:(congruence) PFC UC AFC QC F2C)
   as (mx & MulX & X & UX & QX & PFX & AFX & F2X & VX & BX & FX).
 assert (VXField : fe_at mx ba 40 (words5 v)).
 { eapply curve_keep_field_range;[reflexivity|exact VCField|exact FX|].
   intros pos Range;cbn [curve_square_offset];split;[left;congruence|];split;[congruence|right;right;clear - Range;lia]. }
 assert (CX : fe_at mx b3 0 (words5 (zinv_inverse_cube inv))) by (keep_field C FX).
 assert (InvX : fe_at mx bb 0 (words5 inv)) by (keep_field InvC FX).
 assert (F3X : Mem.range_perm mx b3 0 40 Cur Freeable) by (keep_free F3C FX).
 assert (InvFX : Mem.range_perm mx bb 0 40 Cur Freeable) by (keep_free InvFC FX).
 destruct (eval_point_affine_product true v (zinv_inverse_cube inv) mx bp ba b3 BV (double_tight_loose _ BC)
   ltac:(congruence) ltac:(congruence) ltac:(congruence) PFX VXField AFX CX F3X)
   as (mf & MulY & Y & VO & CO & PFO & AFO & F3O & VY & BY & FY).
 assert (XO : fe_at mf bp 0 (words5 (point_mul_words u (square_words inv)))).
 { eapply curve_keep_field_range;[reflexivity|exact X|exact FY|].
   intros pos Range;cbn [curve_square_offset];split;[right;left;clear - Range;lia|];split;[congruence|left;congruence]. }
 assert (UO : fe_at mf ba 0 (words5 u)).
 { eapply curve_keep_field_range;[reflexivity|exact UX|exact FY|].
   intros pos Range;cbn [curve_square_offset];split;[left;congruence|];split;[congruence|right;left;clear - Range;lia]. }
 assert (QO : fe_at mf b2 0 (words5 (square_words inv))) by (keep_field QX FY).
 assert (InvO : fe_at mf bb 0 (words5 inv)) by (keep_field InvX FY).
 assert (F2O : Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_free F2X FY).
 assert (InvFO : Mem.range_perm mf bb 0 40 Cur Freeable) by (keep_free InvFX FY).
 assert (Frame : lframe (zinv_infinite_products_frame bp ba bb b2 b3) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FS|];intros bx pos (NP & NA & NB & N2 & N3) Valid;split;assumption.
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FC|];intros bx pos (NP & NA & NB & N2 & N3) Valid;repeat split;assumption.
     + eapply lframe_trans.
       * eapply lframe_implies;[exact FX|];intros bx pos (NP & NA & NB & N2 & N3) Valid.
         cbn [curve_square_offset];split;[|split;[exact N2|]].
         -- destruct NP as [NP|[NP|NP]];[left;exact NP|right;left;exact NP|right;right;clear - NP;lia].
         -- destruct NA as [NA|[NA|NA]];[left;exact NA|right;left;exact NA|right;right;clear - NA;lia].
       * eapply lframe_implies;[exact FY|];intros bx pos (NP & NA & NB & N2 & N3) Valid.
         cbn [curve_square_offset];split;[|split;[exact N3|]].
         -- destruct NP as [NP|[NP|NP]];[left;exact NP|right;left;clear - NP;lia|right;right;exact NP].
         -- destruct NA as [NA|[NA|NA]];[left;exact NA|right;left;clear - NA;lia|right;right;exact NA]. }
 exists mf;split.
 - unfold zinv_infinite_product_statements;cbn [statement_sequence].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ms) (le1:=le).
   + unfold zinv_inverse_square_call;eapply exec_curve_call with (vargs:=[Vptr b2 Ptrofs.zero;Vptr bb Ptrofs.zero]) (v:=Vundef).
     * pure_call.
     * exact EQ.
     * eapply eval_Econs;[apply eval_curve_local;exact E2|reflexivity|].
       eapply eval_Econs;[apply eval_Etempvar;exact HI|reflexivity|constructor].
     * exact Square.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=le).
     * unfold zinv_inverse_cube_call;eapply exec_curve_call with
         (vargs:=[Vptr b3 Ptrofs.zero;Vptr b2 Ptrofs.zero;Vptr bb Ptrofs.zero]) (v:=Vundef).
       -- pure_call.
       -- exact EM.
       -- eapply eval_Econs;[apply eval_curve_local;exact E3|reflexivity|].
          eapply eval_Econs;[apply eval_curve_local;exact E2|reflexivity|].
          eapply eval_Econs;[apply eval_Etempvar;exact HI|reflexivity|constructor].
       -- exact Cube.
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mx) (le1:=le).
       -- unfold zinv_infinite_coordinate_call;eapply exec_curve_call with
           (vargs:=[Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr b2 Ptrofs.zero]) (v:=Vundef).
          ++ pure_call.
          ++ exact EM.
          ++ eapply eval_Econs;[apply eval_double_point_address;[cbn [In];tauto|exact HR]|reflexivity|].
             eapply eval_Econs;[apply eval_Eaddrof;apply eval_mixed_b_field;[cbn [In];tauto|exact HB]|reflexivity|].
             eapply eval_Econs;[apply eval_curve_local;exact E2|reflexivity|constructor].
          ++ exact MulX.
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
          ++ unfold zinv_infinite_coordinate_call;eapply exec_curve_call with
              (vargs:=[Vptr bp (Ptrofs.repr 40);Vptr ba (Ptrofs.repr 40);Vptr b3 Ptrofs.zero]) (v:=Vundef).
             ** pure_call.
             ** exact EM.
             ** eapply eval_Econs;[apply eval_double_point_address;[cbn [In];tauto|exact HR]|reflexivity|].
                eapply eval_Econs;[apply eval_Eaddrof;apply eval_mixed_b_field;[cbn [In];tauto|exact HB]|reflexivity|].
                eapply eval_Econs;[apply eval_curve_local;exact E3|reflexivity|constructor].
             ** exact MulY.
          ++ apply exec_Sskip.
 - repeat first [assumption|split].
Qed.
