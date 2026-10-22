(** All original projective-addition body branches on actual reader fields,
    with the complete fixed literal result and every owner needed for freeing. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_square_spec_bridge
 C.jet_secp_square_columns C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_gej_add_finite_body C.jet_secp_gej_add_finite_nonzero C.jet_secp_gej_add_finite_body_literal
 C.jet_secp_gej_add_infinite_literal C.jet_secp_rescale_literal C.jet_secp_canonical_zero C.jet_secp_add_literal.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output literal_gej_add canonical_fe_is_zero.

Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
 repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
   let HP := fresh "Sep" in let HQ := fresh "Sep" in
   assert (HP : ~P) by (intro;apply HS;left;assumption);
   assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_free HF Frame :=
 eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;first [exact Logic.I|congruence].

Theorem exec_gej_add_body_literal e le m pa pb pu pv ps pt p12 p22 bh bi b2 b3 bt (ax ay az bx byword bz : Ty.tySem (Word 8)) :
 le!_a=Some (Vptr pa Ptrofs.zero) -> le!_b=Some (Vptr pb Ptrofs.zero) ->
 le!_r=Some (Vptr pa Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
 e!_u1=Some (pu,curve_fe_type) -> e!_u2=Some (pv,curve_fe_type) ->
 e!_s1=Some (ps,curve_fe_type) -> e!_s2=Some (pt,curve_fe_type) ->
 e!_z12=Some (p12,curve_fe_type) -> e!_z22=Some (p22,curve_fe_type) ->
 e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
 e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) -> e!_t=Some (bt,curve_fe_type) ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None ->
 e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None ->
 e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None ->
 NoDup [pa;pb;pu;pv;ps;pt;p12;p22;bh;bi;b2;b3;bt] ->
 Mem.load Mint32 m pa 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) -> Mem.load Mint32 m pb 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem bz)))) ->
 fe_at m pa 0 (words5 (square_reader_rho ax)) -> fe_at m pa 40 (words5 (square_reader_rho ay)) -> fe_at m pa 80 (words5 (square_reader_rho az)) ->
 fe_at m pb 0 (words5 (square_reader_rho bx)) -> fe_at m pb 40 (words5 (square_reader_rho byword)) -> fe_at m pb 80 (words5 (square_reader_rho bz)) ->
 Mem.range_perm m pa 0 128 Cur Freeable -> Mem.range_perm m pb 0 128 Cur Freeable ->
 Mem.range_perm m pu 0 40 Cur Freeable -> Mem.range_perm m pv 0 40 Cur Freeable ->
 Mem.range_perm m ps 0 40 Cur Freeable -> Mem.range_perm m pt 0 40 Cur Freeable ->
 Mem.range_perm m p12 0 40 Cur Freeable -> Mem.range_perm m p22 0 40 Cur Freeable ->
 Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
 Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable ->
 Mem.range_perm m bt 0 40 Cur Freeable -> exists mf le2 out x y z,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_var) E0 le2 mf out /\
 outcome_result_value out (fn_return f_secp256k1_gej_add_var) Vundef mf /\
 fe_at mf pa 0 (words5 x) /\ fe_at mf pa 40 (words5 y) /\ fe_at mf pa 80 (words5 z) /\
 Mem.range_perm mf pa 0 128 Cur Freeable /\
 Mem.range_perm mf pb 0 128 Cur Freeable /\
 Mem.range_perm mf pu 0 40 Cur Freeable /\
 Mem.range_perm mf pv 0 40 Cur Freeable /\
 Mem.range_perm mf ps 0 40 Cur Freeable /\
 Mem.range_perm mf pt 0 40 Cur Freeable /\
 Mem.range_perm mf p12 0 40 Cur Freeable /\
 Mem.range_perm mf p22 0 40 Cur Freeable /\
 Mem.range_perm mf bh 0 40 Cur Freeable /\
 Mem.range_perm mf bi 0 40 Cur Freeable /\
 Mem.range_perm mf b2 0 40 Cur Freeable /\
 Mem.range_perm mf b3 0 40 Cur Freeable /\
 Mem.range_perm mf bt 0 40 Cur Freeable /\
 square_input_bounds x /\ square_input_bounds y /\ square_input_bounds z /\
 ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=
 @literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)) /\
 lframe (gej_add_finite_nonzero_frame pa pb pu pv ps pt p12 p22 bh bi b2 b3 bt) m mf.
Proof.
 intros PA PB PR PN EU EV ES ET E12 E22 EH EI E2 E3 ETemp EQ EM EN EA E0N ED EF
   Sep FlagA FlagB AX AY AZ BXf BYf BZf FA FB FU FV FS FT F12 F22 FH FI F2 F3 FTemp.
 pose proof Sep as Sep0;separate_blocks Sep0.
 destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)) eqn:InfA.
 - destruct (exec_gej_add_a_infinite_literal e le m pa pb ax ay az bx byword bz
     (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem bz)))
     PA PR PB ltac:(congruence) ltac:(rewrite InfA;exact FlagA) InfA FA FB BXf BYf BZf FlagB)
     as (mf & Body & XO & YO & ZO & Literal & FlagO & FAO & FBO & FrameA).
 assert (FUO : Mem.range_perm mf pu 0 40 Cur Freeable) by (keep_free FU FrameA).
 assert (FVO : Mem.range_perm mf pv 0 40 Cur Freeable) by (keep_free FV FrameA).
 assert (FSO : Mem.range_perm mf ps 0 40 Cur Freeable) by (keep_free FS FrameA).
 assert (FTO : Mem.range_perm mf pt 0 40 Cur Freeable) by (keep_free FT FrameA).
 assert (F12O : Mem.range_perm mf p12 0 40 Cur Freeable) by (keep_free F12 FrameA).
 assert (F22O : Mem.range_perm mf p22 0 40 Cur Freeable) by (keep_free F22 FrameA).
 assert (FHO : Mem.range_perm mf bh 0 40 Cur Freeable) by (keep_free FH FrameA).
 assert (FIO : Mem.range_perm mf bi 0 40 Cur Freeable) by (keep_free FI FrameA).
 assert (F2O : Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_free F2 FrameA).
 assert (F3O : Mem.range_perm mf b3 0 40 Cur Freeable) by (keep_free F3 FrameA).
 assert (FTempO : Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_free FTemp FrameA).
 assert (Frame : lframe (gej_add_finite_nonzero_frame pa pb pu pv ps pt p12 p22 bh bi b2 b3 bt) m mf).
 { eapply lframe_implies;[exact FrameA|].
   intros b pos (NA & NB & NU & NV & NS & NT & N12 & N22 & NH & NI & N2 & N3 & NTemp) VB;exact NA. }
 exists mf,(PTree.set _t'4 (Vint Int.one) le),(Out_return None),
   (square_reader_rho bx),(square_reader_rho byword),(square_reader_rho bz).
 split;[exact Body|];split;[reflexivity|].
 repeat (first [assumption|apply square_reader_bounds|split]).
 - destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem bz)) eqn:InfB.
   + destruct (exec_gej_add_b_infinite_literal e le m pa pb ax ay az bx byword bz
       PA PR PB PN ltac:(rewrite InfA;exact FlagA) ltac:(rewrite InfB;exact FlagB) InfA InfB FA AX AY AZ)
       as (mf & Body & XO & YO & ZO & Literal & FAO & FrameB).
   assert (FBO : Mem.range_perm mf pb 0 128 Cur Freeable) by (keep_free FB FrameB).
   assert (FUO : Mem.range_perm mf pu 0 40 Cur Freeable) by (keep_free FU FrameB).
   assert (FVO : Mem.range_perm mf pv 0 40 Cur Freeable) by (keep_free FV FrameB).
   assert (FSO : Mem.range_perm mf ps 0 40 Cur Freeable) by (keep_free FS FrameB).
   assert (FTO : Mem.range_perm mf pt 0 40 Cur Freeable) by (keep_free FT FrameB).
   assert (F12O : Mem.range_perm mf p12 0 40 Cur Freeable) by (keep_free F12 FrameB).
   assert (F22O : Mem.range_perm mf p22 0 40 Cur Freeable) by (keep_free F22 FrameB).
   assert (FHO : Mem.range_perm mf bh 0 40 Cur Freeable) by (keep_free FH FrameB).
   assert (FIO : Mem.range_perm mf bi 0 40 Cur Freeable) by (keep_free FI FrameB).
   assert (F2O : Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_free F2 FrameB).
   assert (F3O : Mem.range_perm mf b3 0 40 Cur Freeable) by (keep_free F3 FrameB).
   assert (FTempO : Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_free FTemp FrameB).
   assert (Frame : lframe (gej_add_finite_nonzero_frame pa pb pu pv ps pt p12 p22 bh bi b2 b3 bt) m mf).
   { eapply lframe_implies;[exact FrameB|];intros;exact Logic.I. }
   exists mf,(PTree.set _t'3 (Vint Int.one) (PTree.set _t'4 (Vint Int.zero) le)),(Out_return None),
     (square_reader_rho ax),(square_reader_rho ay),(square_reader_rho az).
   split;[exact Body|];split;[reflexivity|].
   repeat (first [assumption|apply square_reader_bounds|split]).
   + destruct (exec_gej_add_finite_body_literal e le m pa pb pu pv ps pt p12 p22 bh bi b2 b3 bt
       ax ay az bx byword bz PA PB PR PN EU EV ES ET E12 E22 EH EI E2 E3 ETemp EQ EM EN EA E0N ED EF
       Sep ltac:(rewrite InfA;exact FlagA) ltac:(rewrite InfB;exact FlagB) InfA InfB
       AX AY AZ BXf BYf BZf FA FB FU FV FS FT F12 F22 FH FI F2 F3 FTemp)
       as (mf & Body & XO & YO & ZO & FlagO & FAO & FBO & FUO & FVO & FSO & FTO &
         F12O & F22O & FHO & FIO & F2O & F3O & FTempO & BoundX & BoundY & BoundZ & Literal & Frame).
     exists mf;do 2 eexists.
     exists (gej_add_finite_x_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
       (square_reader_rho bx) (square_reader_rho byword) (square_reader_rho bz)),
       (gej_add_finite_y_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
       (square_reader_rho bx) (square_reader_rho byword) (square_reader_rho bz)),
       (gej_add_finite_z_words (square_reader_rho ax) (square_reader_rho ay) (square_reader_rho az)
       (square_reader_rho bx) (square_reader_rho byword) (square_reader_rho bz)).
     split;[exact Body|];split.
     * unfold gej_add_finite_out;destruct (Z.eqb _ 0);reflexivity.
     * repeat (first [assumption|split]).
Qed.
