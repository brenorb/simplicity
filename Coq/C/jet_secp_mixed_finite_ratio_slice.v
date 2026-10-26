(** Complete original finite mixed-addition body with loose coordinates and
    an indexed ratio output. Preparation and both H outcomes execute from
    initial storage; all caller/private owners are retained for the caller. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_statement_prefix
 C.jet_secp_field_read_preservation C.jet_secp_mixed_preparation C.jet_secp_mixed_finite_prefix
 C.jet_secp_mixed_difference C.jet_secp_mixed_zero_return C.jet_secp_mixed_finite_return C.jet_secp_mixed_finite_body
 C.jet_secp_mixed_preparation_loose C.jet_secp_mixed_finite_loose C.jet_secp_mixed_body_loose
 C.jet_secp_mixed_inverse_ratio_slice C.jet_secp_mixed_equal_ratio_slice C.jet_secp_mixed_nonzero_ratio_slice
 C.jet_secp_mixed_nonzero_tail C.jet_secp_field_weak_loose C.jet_secp_double_coordinate_numeric.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words weak_loose_words.

Definition mixed_mode_finite_ratio_words loose x y z u v :=
 if Z.eqb (radix_value (mixed_h_words (mixed_x_words loose x) z u) mod feP) 0
 then mixed_zero_words (mixed_i_words (weak_loose_words y) z v) (weak_loose_words y)
 else mixed_h_words (mixed_x_words loose x) z u.
Definition mixed_finite_slice_frame bp ba bu bv bs bt bz bh bi b2 b3 bk br base bx pos :=
 mixed_finite_body_frame bp ba bu bv bs bt bz bh bi b2 b3 bk bx pos /\
 (bx<>br \/ pos<base \/ base+40<=pos).

Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
 repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
   let HP:=fresh "Sep" in let HQ:=fresh "Sep" in
   assert (HP:~P) by (intro;apply HS;left;assumption);
   assert (HQ:~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac sep_goal := repeat rewrite NoDup_cons_iff;cbn [In];repeat split;
 try apply NoDup_nil;try (let Hx:=fresh "Hx" in intro Hx;repeat (destruct Hx as [Hx|Hx]);try contradiction;congruence).
Local Ltac outside := unfold mixed_finite_difference_frame,mixed_prepare_frame,
 mixed_zero_slice_frame,mixed_nonzero_tail_slice_frame,mixed_nonzero_tail_frame;
 repeat split;try (left;congruence);congruence.
Local Ltac keep_free HF Frame := eapply curve_keep_free;[lia|exact HF|exact Frame|];intros;outside.

Theorem exec_mixed_finite_ratio_slice (loose:bool) e le m bp ba bu bv bs bt bz bh bi b2 b3 bk br base size x y z u v :
 0<=base -> (8|base) -> base+40<=size -> size<=Ptrofs.max_unsigned ->
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
 le!_r=Some (Vptr bp Ptrofs.zero) -> le!_rzr=Some (Vptr br (Ptrofs.repr base)) ->
 e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
 e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
 e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
 e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) -> e!_t=Some (bk,curve_fe_type) ->
 e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
 e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
 e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None -> e!_secp256k1_fe_set_int=None ->
 NoDup [bp;ba;bu;bv;bs;bt;bz;bh;bi;b2;b3;bk;br] ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
 mixed_x_body_bound loose x -> square_input_bounds y ->
 square_input_bounds z -> square_input_bounds u -> square_input_bounds v ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bv 0 40 Cur Freeable ->
 Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
 Mem.range_perm m bz 0 40 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
 Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> Mem.range_perm m bk 0 40 Cur Freeable ->
 Mem.range_perm m br 0 size Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_ge_var) E0
  (mixed_mode_finite_body_temps loose le x y z u v) mf (mixed_finite_body_out (mixed_x_words loose x) z u) /\
 fe_at mf bp 0 (words5 (mixed_mode_finite_x_words loose x y z u v)) /\
 fe_at mf bp 40 (words5 (mixed_mode_finite_y_words loose x y z u v)) /\
 fe_at mf bp 80 (words5 (mixed_mode_finite_z_words loose x y z u v)) /\
 Mem.load Mint32 mf bp 120=Some (Vint (mixed_mode_finite_flag loose x y z u v)) /\
 fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\ Mem.load Mint32 mf ba 80=Some (Vint Int.zero) /\
 fe_at mf br base (words5 (mixed_mode_finite_ratio_words loose x y z u v)) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
 Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
 Mem.range_perm mf bz 0 40 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
 Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\ Mem.range_perm mf bk 0 40 Cur Freeable /\
 Mem.range_perm mf br 0 size Cur Freeable /\
 square_input_bounds (mixed_mode_finite_x_words loose x y z u v) /\
 square_input_bounds (mixed_mode_finite_y_words loose x y z u v) /\
 square_input_bounds (mixed_mode_finite_z_words loose x y z u v) /\
 square_input_bounds (mixed_mode_finite_ratio_words loose x y z u v) /\
 lframe (mixed_finite_slice_frame bp ba bu bv bs bt bz bh bi b2 b3 bk br base) m mf.
Proof.
 intros Base Align Fit Max HA HB HR HN EU EV ES ET EZ EH EI E2 E3 EK EW EM EQ EN EA E0N ED EF ESet Sep FlagA FlagB
  BX BY BZ BU BV X Y Z U V PF AF UF VF SF TF ZF HF IF F2 F3 FK RF.
 destruct (mixed_x_body_inputs loose x BX) as [PrepXBound RawXBound].
 separate_blocks Sep.
 assert (SepP:NoDup [bh;bi;bp;ba;bu;bv;bs;bt;bz]) by sep_goal.
 destruct (exec_mixed_finite_difference_mode loose e le m bp ba bu bv bs bt bz bh bi x y z u v
   HA HB EU EV ES ET EZ EH EI EW EM EQ EN EA SepP FlagA FlagB PrepXBound
   ltac:(intros j HJ;pose proof (square_input56 y BY j HJ);lia) BZ BU BV X Y Z U V PF AF UF VF SF TF ZF HF IF)
  as (mp & CP & XP & YP & ZP & UP & VP & U1 & U2 & S1 & S2 & Z12 & H & I & FlagAP & FlagBP &
    PFP & AFP & UFP & VFP & SFP & TFP & ZFP & HFP & IFP & TightX & TightY & TightU & TightS & ValH & ValI & BoundH & BoundI & FP).
 assert (F2P:Mem.range_perm mp b2 0 40 Cur Freeable) by (keep_free F2 FP).
 assert (F3P:Mem.range_perm mp b3 0 40 Cur Freeable) by (keep_free F3 FP).
 assert (FKP:Mem.range_perm mp bk 0 40 Cur Freeable) by (keep_free FK FP).
 assert (RFP:Mem.range_perm mp br 0 size Cur Freeable).
 { eapply curve_keep_free;[clear -Base Fit;lia|exact RF|exact FP|];intros;outside. }
 assert (HAP:(mixed_preparation_temps le)!_a=Some (Vptr bp Ptrofs.zero)) by
  (unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HA).
 assert (HRP:(mixed_preparation_temps le)!_r=Some (Vptr bp Ptrofs.zero)) by
  (unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HR).
 assert (HNP:(mixed_preparation_temps le)!_rzr=Some (Vptr br (Ptrofs.repr base))) by
  (unfold mixed_preparation_temps;rewrite !PTree.gso by discriminate;exact HN).
 unfold mixed_mode_finite_body_temps,mixed_finite_body_out,mixed_mode_finite_x_words,mixed_mode_finite_y_words,
  mixed_mode_finite_z_words,mixed_mode_finite_flag,mixed_mode_finite_ratio_words.
 destruct (Z.eqb (radix_value (mixed_h_words (mixed_x_words loose x) z u) mod feP) 0) eqn:HC.
 - apply Z.eqb_eq in HC.
   assert (SepZ:NoDup [bp;bh;bi;br]) by sep_goal.
   destruct (exec_mixed_zero_head_ratio_slice e (mixed_preparation_temps le) mp bp bh bi br base size x y z
     (mixed_h_words (mixed_x_words loose x) z u) (mixed_i_words (weak_loose_words y) z v)
     HAP HRP HNP EH EI E0N ED EF ESet SepZ Base Align Fit Max RawXBound BY BZ BoundH BoundI HC
     FlagAP XP YP ZP H I PFP HFP IFP RFP)
    as (mf & CZ & XO & YO & ZO & FlagO & HO & IO & RO & PFO & HFO & IFO & RFO & BXO & BYO & BZO & BRO & FZ).
   assert (FB:lframe (mixed_finite_slice_frame bp ba bu bv bs bt bz bh bi b2 b3 bk br base) mp mf).
   { eapply lframe_implies;[exact FZ|];intros b pos [((NP & NA & NU & NV & NS & NT & NZ & NH & NI) & N2 & N3 & NK) Outside] Valid;
      split;[exact NP|];split;[exact NH|];split;assumption. }
   assert (UO:fe_at mf ba 0 (words5 u)) by (eapply field_at_lframe;[exact UP|exact FZ|];intros;outside).
   assert (VO:fe_at mf ba 40 (words5 v)) by (eapply field_at_lframe;[exact VP|exact FZ|];intros;outside).
   assert (FlagBO:Mem.load Mint32 mf ba 80=Some (Vint Int.zero)).
   { rewrite (proj1 FZ Mint32 ba 80);[exact FlagBP| |intros;outside];eapply Mem.perm_valid_block;apply (AFP 0);lia. }
   assert (AFO:Mem.range_perm mf ba 0 88 Cur Freeable) by (keep_free AFP FZ).
   assert (UFO:Mem.range_perm mf bu 0 40 Cur Freeable) by (keep_free UFP FZ).
   assert (VFO:Mem.range_perm mf bv 0 40 Cur Freeable) by (keep_free VFP FZ).
   assert (SFO:Mem.range_perm mf bs 0 40 Cur Freeable) by (keep_free SFP FZ).
   assert (TFO:Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_free TFP FZ).
   assert (ZFO:Mem.range_perm mf bz 0 40 Cur Freeable) by (keep_free ZFP FZ).
   assert (F2O:Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_free F2P FZ).
   assert (F3O:Mem.range_perm mf b3 0 40 Cur Freeable) by (keep_free F3P FZ).
   assert (FKO:Mem.range_perm mf bk 0 40 Cur Freeable) by (keep_free FKP FZ).
   exists mf;split.
   + rewrite mixed_finite_difference_source;eapply exec_statement_prefix_then_last;[exact CP|].
     eapply exec_Sseq_2;[exact CZ|discriminate].
   + do 25 (split;[assumption|]).
     eapply lframe_trans;[|exact FB];eapply lframe_implies;[exact FP|];
      intros b pos [((NP & NA & NU & NV & NS & NT & NZ & NH & NI) & N2 & N3 & NK) Outside] Valid;
      unfold mixed_finite_difference_frame,mixed_prepare_frame;repeat split;try assumption;left;assumption.
 - apply Z.eqb_neq in HC.
   assert (SepN:NoDup [bp;bh;b2;b3;bk;bu;bi;bs;br]) by sep_goal.
   destruct (exec_mixed_nonzero_tail_slice e (mixed_preparation_temps le) mp bp bh b2 b3 bk bu bi bs br base size x y z
     (mixed_h_words (mixed_x_words loose x) z u) (mixed_x_words loose x)
     (mixed_i_words (weak_loose_words y) z v) (weak_loose_words y)
     Base Align Fit Max HAP HRP HNP EH E2 E3 EK EU EI ES E0N EM EQ EN EA SepN
     BZ BoundH (double_tight_loose _ TightX) BoundI (double_tight_loose _ TightY) HC XP YP ZP H U1 I S1
     PFP HFP F2P F3P FKP UFP IFP SFP RFP)
    as (mf & CN & XO & YO & ZO & FlagO & PFO & HFO & F2O & F3O & FKO & UFO & IFO & SFO & BXO & BYO & BZO & RO & RFO & FN).
   assert (UO:fe_at mf ba 0 (words5 u)) by (eapply field_at_lframe;[exact UP|exact FN|];intros;outside).
   assert (VO:fe_at mf ba 40 (words5 v)) by (eapply field_at_lframe;[exact VP|exact FN|];intros;outside).
   assert (FlagBO:Mem.load Mint32 mf ba 80=Some (Vint Int.zero)).
   { rewrite (proj1 FN Mint32 ba 80);[exact FlagBP| |intros;outside];eapply Mem.perm_valid_block;apply (AFP 0);lia. }
   assert (AFO:Mem.range_perm mf ba 0 88 Cur Freeable) by (keep_free AFP FN).
   assert (VFO:Mem.range_perm mf bv 0 40 Cur Freeable) by (keep_free VFP FN).
   assert (TFO:Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_free TFP FN).
   assert (ZFO:Mem.range_perm mf bz 0 40 Cur Freeable) by (keep_free ZFP FN).
   exists mf;split.
   + rewrite mixed_finite_difference_source;eapply exec_statement_prefix_then_last;[exact CP|exact CN].
   + do 25 (split;[assumption|]).
     eapply lframe_trans.
     * eapply lframe_implies;[exact FP|];intros b pos [((NP & NA & NU & NV & NS & NT & NZ & NH & NI) & N2 & N3 & NK) Outside] Valid;
        unfold mixed_finite_difference_frame,mixed_prepare_frame;repeat split;try assumption;left;assumption.
     * eapply lframe_implies;[exact FN|];intros b pos [((NP & NA & NU & NV & NS & NT &NZ & NH & NI) & N2 & N3 & NK) Outside] Valid;
        split;[unfold mixed_nonzero_tail_frame;repeat split;try assumption;left;exact NP|exact Outside].
Qed.
