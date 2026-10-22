(** Entire original nonzero-H tail from prepared fields: derive the H test,
    all arithmetic calls, final coordinates, ownership and precise framing. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
  C.jet_secp_square_columns C.jet_secp_field_sum_bounds C.jet_secp_curve_statements C.jet_secp_curve_frame
  C.jet_secp_field_read_preservation C.jet_secp_statement_prefix C.jet_secp_mixed_difference
  C.jet_secp_mixed_nonzero_start C.jet_secp_mixed_nonzero_products C.jet_secp_mixed_x_tail C.jet_secp_mixed_y_tail.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words.

Definition mixed_nonzero_x_words h i u := mixed_x_words i (mixed_h3_words h) (mixed_t_words u h).
Definition mixed_nonzero_y_words h i u s :=
  mixed_y_words (mixed_tx_words i (mixed_h3_words h) (mixed_t_words u h)) i (mixed_h3_words h) s.
Definition mixed_nonzero_tail_frame (bp bh b2 b3 bt bu bi bs bx : block) (pos : Z) :=
  bx<>bh /\ bx<>b2 /\ bx<>b3 /\ bx<>bt /\ bx<>bu /\ bx<>bi /\ bx<>bs /\ (bx<>bp \/ pos<0 \/ 124<=pos).

Local Ltac separate_tail_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by (intro;apply HS;left;assumption);
    assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac outside_products :=
  unfold mixed_nonzero_products_frame,mixed_nonzero_start_frame;
    repeat split;try (left;congruence);congruence.
Local Ltac keep_tail_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;try (left;congruence);congruence.

Theorem exec_mixed_nonzero_tail e le m bp bh b2 b3 bt bu bi bs x y z h u i s :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_h=Some (bh,curve_fe_type) -> e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) ->
  e!_t=Some (bt,curve_fe_type) -> e!_u1=Some (bu,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) -> e!_s1=Some (bs,curve_fe_type) ->
  e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
  e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None -> NoDup [bp;bh;b2;b3;bt;bu;bi;bs] ->
  square_input_bounds z -> square_input_bounds h -> square_input_bounds u -> square_input_bounds i -> square_input_bounds s ->
  radix_value h mod feP<>0 -> fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m bh 0 (words5 h) -> fe_at m bu 0 (words5 u) -> fe_at m bi 0 (words5 i) -> fe_at m bs 0 (words5 s) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bu 0 40 Cur Freeable ->
  Mem.range_perm m bi 0 40 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m mixed_after_difference E0 (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal /\
  fe_at mf bp 0 (words5 (mixed_nonzero_x_words h i u)) /\
  fe_at mf bp 40 (words5 (mixed_nonzero_y_words h i u s)) /\
  fe_at mf bp 80 (words5 (point_mul_words z h)) /\ Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bu 0 40 Cur Freeable /\
  Mem.range_perm mf bi 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  square_input_bounds (mixed_nonzero_x_words h i u) /\ square_input_bounds (mixed_nonzero_y_words h i u s) /\
  square_input_bounds (point_mul_words z h) /\ lframe (mixed_nonzero_tail_frame bp bh b2 b3 bt bu bi bs) m mf.
Proof.
  intros HA HR HN EH E2 E3 ET EU EI ES EZ EM EQ EN EA Sep BZ BH BU BI BS HNZ X Y Z H U I S PF FH F2 F3 FT FU IF SF.
  separate_tail_blocks Sep.
  assert (SepP : NoDup [bp;bh;b2;b3;bt;bu]) by
    (repeat rewrite NoDup_cons_iff;cbn [In];repeat split;intuition congruence).
  assert (SepXY : NoDup [bp;bt;bi;b3;bs]) by
    (repeat rewrite NoDup_cons_iff;cbn [In];repeat split;intuition congruence).
  destruct (exec_mixed_nonzero_products e le m bp bh b2 b3 bt bu x y z h u
    HA HR HN EH E2 E3 ET EU EZ EM EQ EN SepP BZ BH BU HNZ X Y Z H U PF FH F2 F3 FT FU)
    as (mp & CP & XP & YP & ZP & FlagP & HP & UP & H2P & H3P & TP & PFP & FHP & F2P & F3P & FTP & FUP &
      BoundZ & BoundH2 & BoundH3 & BoundT & ValH2 & ValH3 & ValT & FP).
  assert (IP : fe_at mp bi 0 (words5 i)).
  { eapply field_at_lframe;[exact I|exact FP|];intro pos;outside_products. }
  assert (SP : fe_at mp bs 0 (words5 s)).
  { eapply field_at_lframe;[exact S|exact FP|];intro pos;outside_products. }
  assert (IFP : Mem.range_perm mp bi 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact IF|exact FP|];intro pos;outside_products. }
  assert (SFP : Mem.range_perm mp bs 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact SF|exact FP|];intro pos;outside_products. }
  assert (HRP : (PTree.set _t'2 (Vint Int.zero) le)!_r=Some (Vptr bp Ptrofs.zero))
    by (rewrite PTree.gso by discriminate;exact HR).
  destruct (exec_mixed_xy_tail e (PTree.set _t'2 (Vint Int.zero) le) mp bp bi b3 bt bs
    i (mixed_h3_words h) (mixed_t_words u h) s HRP EI E3 ET ES EQ EM EA SepXY
    BI BoundH3 BoundT BS IP H3P TP SP PFP IFP F3P FTP SFP)
    as (mf & CXY & XO & YO & TO & GO & IO & SO & PFO & IFO & F3O & FTO & SFO & BoundX & BoundY & BoundTX & FX).
  assert (FHO : Mem.range_perm mf bh 0 40 Cur Freeable) by (keep_tail_free FHP FX).
  assert (F2O : Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_tail_free F2P FX).
  assert (FUO : Mem.range_perm mf bu 0 40 Cur Freeable) by (keep_tail_free FUP FX).
  assert (ZO : fe_at mf bp 80 (words5 (point_mul_words z h))).
  { eapply curve_keep_field_range;[reflexivity|exact ZP|exact FX|].
    intros pos HPos;unfold mixed_xy_frame;repeat split;try congruence;right;right;lia. }
  assert (FlagO : Mem.load Mint32 mf bp 120=Some (Vint Int.zero)).
  { rewrite (proj1 FX Mint32 bp 120);[exact FlagP| |].
    - eapply Mem.perm_valid_block;apply (PFP 0);lia.
    - intros pos HPos;unfold mixed_xy_frame;repeat split;try congruence;right;right;
        change (120<=pos<124) in HPos;lia. }
  assert (BX : square_input_bounds (mixed_nonzero_x_words h i u))
    by (exact (field_scaled_loose 4 _ ltac:(lia) BoundX)).
  assert (BY : square_input_bounds (mixed_nonzero_y_words h i u s))
    by (exact (field_scaled_loose 2 _ ltac:(lia) BoundY)).
  assert (Frame : lframe (mixed_nonzero_tail_frame bp bh b2 b3 bt bu bi bs) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FP|];intros bx pos (NH & N2 & N3 & NT & NU & NI & NS & NP) HV.
      unfold mixed_nonzero_products_frame,mixed_nonzero_start_frame;
        split;[exact N3|];split;[exact NT|];split;[exact NU|];split;[exact NH|];split;[exact N2|].
      destruct NP as [NP|[NP|NP]];[left;exact NP|right;left;lia|right;right;exact NP].
    - eapply lframe_implies;[exact FX|];intros bx pos (NH & N2 & N3 & NT & NU & NI & NS & NP) HV.
      unfold mixed_xy_frame;split;[exact NI|];split;[exact N3|];split;[exact NT|];split;[exact NS|].
      destruct NP as [NP|[NP|NP]];[left;exact NP|right;left;exact NP|right;right;lia]. }
  exists mf;split.
  - rewrite mixed_nonzero_products_source;eapply exec_statement_prefix_then_last;[exact CP|exact CXY].
  - repeat (first [assumption|split]).
Qed.
