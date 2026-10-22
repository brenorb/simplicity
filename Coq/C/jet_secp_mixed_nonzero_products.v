(** Connected original nonzero-H prefix through H2 negation and H3/T products.
    The private output fields are initially uninitialized, and their bounds
    and all intermediate call executions are derived inside this proof. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
  C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_field_mul_small
  C.jet_secp_field_negate_separate C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_curve_statements C.jet_secp_statement_prefix C.jet_secp_mixed_difference
  C.jet_secp_mixed_nonzero_start C.jet_secp_mixed_products C.jet_secp_double_coordinate_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words negate_sep_words.

Definition mixed_h2_words h := negate_sep_words (square_words h).
Definition mixed_h3_words h := point_mul_words (mixed_h2_words h) h.
Definition mixed_t_words u h := point_mul_words u (mixed_h2_words h).
Definition mixed_nonzero_products_statements := mixed_nonzero_prefix_statements++mixed_product_statements.
Definition mixed_nonzero_products_frame (bp bh b2 b3 bt bu bx : block) (pos : Z) :=
  bx<>b3 /\ bx<>bt /\ bx<>bu /\ mixed_nonzero_start_frame bp bh b2 bx pos.
Lemma mixed_nonzero_products_source : mixed_after_difference=
  statement_sequence mixed_nonzero_products_statements mixed_after_products.
Proof. reflexivity. Qed.

Local Ltac separate_nonzero_blocks Sep :=
  repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
  repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
  repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
    let HP := fresh "Sep" in let HQ := fresh "Sep" in
    assert (HP : ~P) by (intro;apply HS;left;assumption);
    assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_nonzero_field HF Frame :=
  eapply field_at_lframe;[exact HF|exact Frame|];intro pos;repeat split;congruence.
Local Ltac keep_nonzero_free HF Frame :=
  eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;repeat split;congruence.

Theorem exec_mixed_nonzero_products e le m bp bh b2 b3 bt bu x y z h u :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_h=Some (bh,curve_fe_type) -> e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) ->
  e!_t=Some (bt,curve_fe_type) -> e!_u1=Some (bu,curve_fe_type) ->
  e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_negate=None ->
  NoDup [bp;bh;b2;b3;bt;bu] -> square_input_bounds z -> square_input_bounds h -> square_input_bounds u ->
  radix_value h mod feP<>0 -> fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m bh 0 (words5 h) -> fe_at m bu 0 (words5 u) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bu 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m (statement_sequence mixed_nonzero_products_statements Sskip) E0
    (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 (point_mul_words z h)) /\
  Mem.load Mint32 mf bp 120=Some (Vint Int.zero) /\
  fe_at mf bh 0 (words5 h) /\ fe_at mf bu 0 (words5 u) /\ fe_at mf b2 0 (words5 (mixed_h2_words h)) /\
  fe_at mf b3 0 (words5 (mixed_h3_words h)) /\ fe_at mf bt 0 (words5 (mixed_t_words u h)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bu 0 40 Cur Freeable /\
  square_input_bounds (point_mul_words z h) /\ square_input_bounds (mixed_h2_words h) /\
  mul_small_input_bounds (mixed_h3_words h) /\ mul_small_input_bounds (mixed_t_words u h) /\
  radix_value (mixed_h2_words h)=4*feP-radix_value (square_words h) /\
  radix_value (mixed_h3_words h) mod feP=(radix_value (mixed_h2_words h)*radix_value h) mod feP /\
  radix_value (mixed_t_words u h) mod feP=(radix_value u*radix_value (mixed_h2_words h)) mod feP /\
  lframe (mixed_nonzero_products_frame bp bh b2 b3 bt bu) m mf.
Proof.
  intros HA HR HN EH E2 E3 ET EU EZ EM EQ EN Sep BZ BH BU HNZ X Y Z H U PF FH F2 F3 FT FU.
  separate_nonzero_blocks Sep.
  assert (SepP : NoDup [b2;b3;bt;bh;bu]).
  { repeat rewrite NoDup_cons_iff;cbn [In];repeat split;intuition congruence. }
  destruct (exec_mixed_nonzero_prefix e le m bp bh b2 x y z h HA HR HN EH E2 EZ EM EQ
    ltac:(congruence) ltac:(congruence) ltac:(congruence) BZ BH HNZ X Y Z H PF FH F2)
    as (mp & CP & XP & YP & ZP & FlagP & HP & H2P & PFP & FHP & F2P & BoundZ & BoundH2 & ValZ & ValH2 & FP).
  assert (UP : fe_at mp bu 0 (words5 u)).
  { eapply field_at_lframe;[exact U|exact FP|];intro pos;unfold mixed_nonzero_start_frame;
      repeat split;try (left;congruence);congruence. }
  assert (F3P : Mem.range_perm mp b3 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F3|exact FP|];intro pos;unfold mixed_nonzero_start_frame;
      repeat split;try (left;congruence);congruence. }
  assert (FTP : Mem.range_perm mp bt 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FT|exact FP|];intro pos;unfold mixed_nonzero_start_frame;
      repeat split;try (left;congruence);congruence. }
  assert (FUP : Mem.range_perm mp bu 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FU|exact FP|];intro pos;unfold mixed_nonzero_start_frame;
      repeat split;try (left;congruence);congruence. }
  destruct (exec_mixed_products e (PTree.set _t'2 (Vint Int.zero) le) mp b2 b3 bt bh bu (square_words h) h u
    E2 E3 ET EH EU EN EM SepP (double_square_tight h BH) BH BU H2P HP UP F2P F3P FTP FHP FUP)
    as (mf & CM & H2O & H3O & TO & HO & UO & F2O & F3O & FTO & FHO & FUO & ValN & BoundN & Val3 & ValT & Bound3 & BoundT & FM).
  assert (XO : fe_at mf bp 0 (words5 x)) by (keep_nonzero_field XP FM).
  assert (YO : fe_at mf bp 40 (words5 y)) by (keep_nonzero_field YP FM).
  assert (ZO : fe_at mf bp 80 (words5 (point_mul_words z h))) by (keep_nonzero_field ZP FM).
  assert (PFO : Mem.range_perm mf bp 0 128 Cur Freeable) by (keep_nonzero_free PFP FM).
  assert (FlagO : Mem.load Mint32 mf bp 120=Some (Vint Int.zero)).
  { rewrite (proj1 FM Mint32 bp 120);[exact FlagP| |intros pos PP;repeat split;congruence].
    eapply Mem.perm_valid_block;apply (PFP 0);lia. }
  assert (Frame : lframe (mixed_nonzero_products_frame bp bh b2 b3 bt bu) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact FP|];intros bx pos (N3 & NT & NU & NF) HV;exact NF.
    - eapply lframe_implies;[exact FM|];intros bx pos (N3 & NT & NU & NH & N2 & NP) HV.
      unfold mixed_product_frame;repeat split;assumption. }
  exists mf;split.
  - change (Clight2.exec_stmt secp_ge e le m
      (statement_sequence mixed_nonzero_prefix_statements (statement_sequence mixed_product_statements Sskip)) E0
      (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal).
    eapply exec_statement_prefix_then_last;[exact CP|exact CM].
  - repeat (first [assumption|split]).
Qed.
