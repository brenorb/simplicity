(** All original projective-addition branches from arbitrary bounded field
    representations, including the flag observed by subsequent C callers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_gej_add_finite_body C.jet_secp_gej_add_finite_nonzero C.jet_secp_gej_add_finite_generic_body
 C.jet_secp_gej_add_infinite C.jet_secp_gej_add_infinite_literal C.jet_secp_rescale_literal
 C.jet_secp_canonical_zero C.jet_secp_canonical_normalize C.jet_secp_curve_literal C.jet_secp_add_literal
 C.jet_secp_literal_gej_predicate C.jet_secp_gej_ge_equiv_flag C.jet_secp_double_literal_bridge.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output literal_gej_add canonical_fe_is_zero canonical_fe_normalize literal_gej_is_infinity.

Lemma gej_add_output_normalize w (a : Ty.tySem (Word 8)) :
 radix_value w mod feP=@toZ (WordToZ 8) a mod feP ->
 rescale_field_output w=@canonical_fe_normalize Alg.CoreFunSem a.
Proof.
 intro R;apply double_field_output_matches.
 rewrite canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model;exact R.
Qed.

Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
 repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
   let HP := fresh "Sep" in let HQ := fresh "Sep" in
   assert (HP : ~P) by (intro;apply HS;left;assumption);
   assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_free HF Frame :=
 eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;first [exact Logic.I|congruence].

Theorem exec_gej_add_body_generic e le m pa pb pu pv ps pt p12 p22 bh bi b2 b3 bt mx my mz mu mv mw (ax ay az bx byword bz : Ty.tySem (Word 8)) :
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
 square_input_bounds mx ->
 square_input_bounds my ->
 square_input_bounds mz ->
 square_input_bounds mu ->
 square_input_bounds mv ->
 square_input_bounds mw ->
 radix_value mx mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value my mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value mz mod feP=@toZ (WordToZ 8) az mod feP ->
 radix_value mu mod feP=@toZ (WordToZ 8) bx mod feP ->
 radix_value mv mod feP=@toZ (WordToZ 8) byword mod feP ->
 radix_value mw mod feP=@toZ (WordToZ 8) bz mod feP ->
 fe_at m pa 0 (words5 mx) -> fe_at m pa 40 (words5 my) -> fe_at m pa 80 (words5 mz) ->
 fe_at m pb 0 (words5 mu) -> fe_at m pb 40 (words5 mv) -> fe_at m pb 80 (words5 mw) ->
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
 Mem.load Mint32 mf pa 120=Some (Vint (bit_int (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem (@literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz))))))) /\
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
   Sep FlagA FlagB BMX BMY BMZ BMU BMV BMW RMX RMY RMZ RMU RMV RMW
   AX AY AZ BXf BYf BZf FA FB FU FV FS FT F12 F22 FH FI F2 F3 FTemp.
 pose proof Sep as Sep0;separate_blocks Sep0.
 destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)) eqn:InfA.
 - destruct (exec_gej_add_a_infinite e le m pa pb mu mv mw Int.one
     (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem bz)))
     PA PR PB ltac:(congruence) FlagA ltac:(discriminate) FA FB BXf BYf BZf FlagB)
     as (mf & Body & XO & YO & ZO & FlagO & FAO & FBO & FrameA).
   assert (HA : @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inr tt).
   { rewrite literal_gej_is_infinity_value.
     destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [[] | []];[discriminate InfA|reflexivity]. }
   assert (Literal : ((rescale_field_output mu,rescale_field_output mv),rescale_field_output mw)=
     @literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz))).
   { rewrite gej_add_left_infinite_value by exact HA.
     rewrite (gej_add_output_normalize mu bx RMU),(gej_add_output_normalize mv byword RMV),
       (gej_add_output_normalize mw bz RMW);reflexivity. }
   assert (SpecFlag : Mem.load Mint32 mf pa 120=Some (Vint (bit_int (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem (@literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)))))))).
   { rewrite gej_add_left_infinite_value by exact HA.
     rewrite literal_gej_is_infinity_value,equiv_normalized_zero_test;exact FlagO. }
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
   exists mf,(PTree.set _t'4 (Vint Int.one) le),(Out_return None),mu,mv,mw.
   split;[exact Body|];split;[reflexivity|];repeat (first [assumption|split]).
 - destruct (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem bz)) eqn:InfB.
   + destruct (exec_gej_add_b_infinite e le m pa pb Int.one
       PA PR PB PN FlagA FlagB ltac:(discriminate) FA) as (mf & Body & FrameB).
     assert (XO : fe_at mf pa 0 (words5 mx)).
     { eapply field_at_lframe;[exact AX|exact FrameB|];intros;exact Logic.I. }
     assert (YO : fe_at mf pa 40 (words5 my)).
     { eapply field_at_lframe;[exact AY|exact FrameB|];intros;exact Logic.I. }
     assert (ZO : fe_at mf pa 80 (words5 mz)).
     { eapply field_at_lframe;[exact AZ|exact FrameB|];intros;exact Logic.I. }
     assert (HA : @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt).
     { rewrite literal_gej_is_infinity_value.
       destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [[] | []];[reflexivity|discriminate InfA]. }
     assert (HB : @literal_gej_is_infinity Alg.CoreFunSem ((bx,byword),bz)=inr tt).
     { rewrite literal_gej_is_infinity_value.
       destruct (@canonical_fe_is_zero Alg.CoreFunSem bz) as [[] | []];[discriminate InfB|reflexivity]. }
     assert (Literal : ((rescale_field_output mx,rescale_field_output my),rescale_field_output mz)=
       @literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz))).
     { rewrite gej_add_right_infinite_value by assumption.
       rewrite (gej_add_output_normalize mx ax RMX),(gej_add_output_normalize my ay RMY),
         (gej_add_output_normalize mz az RMZ);reflexivity. }
     assert (FlagO : Mem.load Mint32 mf pa 120=Some (Vint Int.zero)).
     { rewrite (proj1 FrameB Mint32 pa 120);[exact FlagA| |intros;exact Logic.I].
       eapply Mem.perm_valid_block;apply (FA 0);lia. }
     assert (SpecFlag : Mem.load Mint32 mf pa 120=Some (Vint (bit_int (Bit.toBool (@literal_gej_is_infinity Alg.CoreFunSem (@literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)))))))).
     { rewrite gej_add_right_infinite_value by assumption.
       rewrite literal_gej_is_infinity_value,equiv_normalized_zero_test,InfA;exact FlagO. }
     assert (FAO : Mem.range_perm mf pa 0 128 Cur Freeable) by (keep_free FA FrameB).
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
     exists mf,(PTree.set _t'3 (Vint Int.one) (PTree.set _t'4 (Vint Int.zero) le)),(Out_return None),mx,my,mz.
     split;[exact Body|];split;[reflexivity|];repeat (first [assumption|split]).
   + destruct (exec_gej_add_finite_body_generic e le m pa pb pu pv ps pt p12 p22 bh bi b2 b3 bt
       mx my mz mu mv mw ax ay az bx byword bz
       PA PB PR PN EU EV ES ET E12 E22 EH EI E2 E3 ETemp EQ EM EN EA E0N ED EF
       Sep ltac:(rewrite InfA;exact FlagA) ltac:(rewrite InfB;exact FlagB)
       BMX BMY BMZ BMU BMV BMW RMX RMY RMZ RMU RMV RMW InfA InfB
       AX AY AZ BXf BYf BZf FA FB FU FV FS FT F12 F22 FH FI F2 F3 FTemp)
       as (mf & Body & XO & YO & ZO & FlagO & SpecFlag & FAO & FBO & FUO & FVO & FSO & FTO &
         F12O & F22O & FHO & FIO & F2O & F3O & FTempO & BoundX & BoundY & BoundZ & Literal & Frame).
     exists mf;do 2 eexists.
     exists (gej_add_finite_x_words mx my mz mu mv mw),(gej_add_finite_y_words mx my mz mu mv mw),
       (gej_add_finite_z_words mx my mz mu mv mw).
     split;[exact Body|];split.
     * unfold gej_add_finite_out;destruct (Z.eqb _ 0);reflexivity.
     * repeat (first [assumption|split]).
Qed.
