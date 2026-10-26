(** Complete original mixed-addition body for any accumulator flag, with
    loose coordinates and a ratio output in its real caller-owned array. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_mixed_finite_body
 C.jet_secp_mixed_body C.jet_secp_mixed_body_loose C.jet_secp_mixed_finite_return
 C.jet_secp_mixed_finite_loose C.jet_secp_mixed_preparation_loose C.jet_secp_mixed_preparation
 C.jet_secp_mixed_finite_ratio_slice C.jet_secp_mixed_infinite_ratio_slice
 C.jet_secp_mixed_infinite_literal C.jet_secp_double_var_owned C.jet_secp_point_set_bit.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition mixed_mode_slice_ratio_words loose flag x y z u v :=
 if Int.eq flag Int.zero then mixed_mode_finite_ratio_words loose x y z u v else point_set_bit_words false.
Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HS : _ /\ _ |- _=>destruct HS end;
 repeat match goal with HS : ~(?P \/ ?Q) |- _=>
   let HP:=fresh "Sep" in let HQ:=fresh "Sep" in
   assert (HP:~P) by (intro;apply HS;left;assumption);
   assert (HQ:~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_owner HF Frame := eapply curve_keep_free;[lia|exact HF|exact Frame|];intros;split;[congruence|left;congruence].

Theorem exec_mixed_body_ratio_slice (loose:bool) e le m bp ba bu bv bs bt bz bh bi b2 b3 bk br base size x y z u v flag :
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
 e!_secp256k1_gej_set_ge=None -> e!_secp256k1_fe_clear=None ->
 NoDup [bp;ba;bu;bv;bs;bt;bz;bh;bi;b2;b3;bk;br] ->
 Mem.load Mint32 m bp 120=Some (Vint flag) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
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
  (mixed_mode_body_temps loose le flag x y z u v) mf (mixed_body_out flag (mixed_x_words loose x) z u) /\
 fe_at mf bp 0 (words5 (mixed_mode_body_x_words loose flag x y z u v)) /\
 fe_at mf bp 40 (words5 (mixed_mode_body_y_words loose flag x y z u v)) /\
 fe_at mf bp 80 (words5 (mixed_mode_body_z_words loose flag x y z u v)) /\
 Mem.load Mint32 mf bp 120=Some (Vint (mixed_mode_body_flag loose flag x y z u v)) /\
 fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\ Mem.load Mint32 mf ba 80=Some (Vint Int.zero) /\
 fe_at mf br base (words5 (mixed_mode_slice_ratio_words loose flag x y z u v)) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
 Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\
 Mem.range_perm mf bz 0 40 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
 Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\ Mem.range_perm mf bk 0 40 Cur Freeable /\
 Mem.range_perm mf br 0 size Cur Freeable /\
 square_input_bounds (mixed_mode_body_x_words loose flag x y z u v) /\
 square_input_bounds (mixed_mode_body_y_words loose flag x y z u v) /\
 square_input_bounds (mixed_mode_body_z_words loose flag x y z u v) /\
 square_input_bounds (mixed_mode_slice_ratio_words loose flag x y z u v) /\
 lframe (mixed_finite_slice_frame bp ba bu bv bs bt bz bh bi b2 b3 bk br base) m mf.
Proof.
 intros Base Align Fit Max HA HB HR HN EU EV ES ET EZ EH EI E2 E3 EK EW EM EQ EN EA E0N ED EF ESet ESetGE EClear
  Sep FlagA FlagB BX BY BZ BU BV X Y Z U V PF AF UF VF SF TF ZF HF IF F2 F3 FK RF.
 unfold mixed_mode_body_temps,mixed_body_out,mixed_mode_body_x_words,mixed_mode_body_y_words,
  mixed_mode_body_z_words,mixed_mode_body_flag,mixed_mode_slice_ratio_words.
 destruct (Int.eq_dec flag Int.zero) as [->|Nonzero].
 - rewrite Int.eq_true.
   exact (exec_mixed_finite_ratio_slice loose e le m bp ba bu bv bs bt bz bh bi b2 b3 bk br base size x y z u v
    Base Align Fit Max HA HB HR HN EU EV ES ET EZ EH EI E2 E3 EK EW EM EQ EN EA E0N ED EF ESet Sep
    FlagA FlagB BX BY BZ BU BV X Y Z U V PF AF UF VF SF TF ZF HF IF F2 F3 FK RF).
 - rewrite Int.eq_false by exact Nonzero;separate_blocks Sep.
   destruct (exec_mixed_infinite_ratio_slice e le m bp ba br base size u v flag Base Align Fit Max
     HA HR HB HN ESetGE EClear ltac:(congruence) ltac:(congruence) ltac:(congruence)
     PF AF RF FlagA Nonzero U V FlagB)
    as (mf & Run & XO & YO & ZO & FlagO & UO & VO & FlagBO & RO & PFO & AFO & RFO & FB).
   assert (UFO:Mem.range_perm mf bu 0 40 Cur Freeable) by (keep_owner UF FB).
   assert (VFO:Mem.range_perm mf bv 0 40 Cur Freeable) by (keep_owner VF FB).
   assert (SFO:Mem.range_perm mf bs 0 40 Cur Freeable) by (keep_owner SF FB).
   assert (TFO:Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_owner TF FB).
   assert (ZFO:Mem.range_perm mf bz 0 40 Cur Freeable) by (keep_owner ZF FB).
   assert (HFO:Mem.range_perm mf bh 0 40 Cur Freeable) by (keep_owner HF FB).
   assert (IFO:Mem.range_perm mf bi 0 40 Cur Freeable) by (keep_owner IF FB).
   assert (F2O:Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_owner F2 FB).
   assert (F3O:Mem.range_perm mf b3 0 40 Cur Freeable) by (keep_owner F3 FB).
   assert (FKO:Mem.range_perm mf bk 0 40 Cur Freeable) by (keep_owner FK FB).
   assert (Frame:lframe (mixed_finite_slice_frame bp ba bu bv bs bt bz bh bi b2 b3 bk br base) m mf).
   { eapply lframe_implies;[exact FB|];intros b pos [((NP & NA & NU & NV & NS & NT & NZ & NH & NI) & N2 & N3 & NK) Outside] Valid;
      split;[exact NP|exact Outside]. }
   exists mf;repeat (first [assumption|exact mixed_one_bounds|exact square_zero_bounds|split]).
   intros j Bound;unfold point_set_bit_words;destruct (Nat.eqb j 0);
    change (0<if Nat.eqb j 4 then 4503599627370496 else 72057594037927936);
    destruct (Nat.eqb j 4);lia.
Qed.
