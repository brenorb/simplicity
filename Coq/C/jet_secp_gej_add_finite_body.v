(** Both finite branches of the entire original projective-addition helper.
    The H dispatch is discharged, not a restriction on the represented inputs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_field_read_preservation C.jet_secp_gej_add_finite_difference C.jet_secp_gej_add_finite_prepare
 C.jet_secp_gej_add_finite_return C.jet_secp_gej_add_finite_nonzero
 C.jet_secp_mixed_zero_return C.jet_secp_mixed_nonzero_tail C.jet_secp_double_all_calls.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words.

Definition gej_add_finite_x_words x y z u v w :=
 if Z.eqb (radix_value (gej_add_h_words x z u w) mod feP) 0
 then mixed_zero_words (gej_add_i_words y z v w) (double_output_x_words x y)
 else mixed_nonzero_x_words (gej_add_h_words x z u w) (gej_add_i_words y z v w) (gej_add_u1_words x w).
Definition gej_add_finite_y_words x y z u v w :=
 if Z.eqb (radix_value (gej_add_h_words x z u w) mod feP) 0
 then mixed_zero_words (gej_add_i_words y z v w) (double_output_y_words x y)
 else mixed_nonzero_y_words (gej_add_h_words x z u w) (gej_add_i_words y z v w) (gej_add_u1_words x w) (gej_add_s1_words y w).
Definition gej_add_finite_z_words x y z u v w :=
 if Z.eqb (radix_value (gej_add_h_words x z u w) mod feP) 0
 then mixed_zero_words (gej_add_i_words y z v w) (double_output_z_words y z)
 else point_mul_words z (point_mul_words (gej_add_h_words x z u w) w).
Definition gej_add_finite_flag x y z u v w :=
 if Z.eqb (radix_value (gej_add_h_words x z u w) mod feP) 0
 then mixed_zero_flag (gej_add_i_words y z v w) y z else Int.zero.
Definition gej_add_finite_temps le x y z u v w :=
 if Z.eqb (radix_value (gej_add_h_words x z u w) mod feP) 0
 then mixed_zero_return_temps (gej_add_finite_prepare_temps le) (gej_add_i_words y z v w)
 else PTree.set _t'2 (Vint Int.zero) (gej_add_finite_prepare_temps le).
Definition gej_add_finite_out x z u w :=
 if Z.eqb (radix_value (gej_add_h_words x z u w) mod feP) 0 then Out_return None else Out_normal.

Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
 repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
   let HP := fresh "Sep" in let HQ := fresh "Sep" in
   assert (HP : ~P) by (intro;apply HS;left;assumption);
   assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.
Local Ltac keep_free HF Frame :=
 eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;
 unfold gej_add_finite_return_frame;repeat split;congruence.

Theorem exec_gej_add_finite_body e le m pa pb pu pv ps pt p12 p22 bh bi b2 b3 bt x y z u v w :
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
 Mem.load Mint32 m pa 120=Some (Vint Int.zero) -> Mem.load Mint32 m pb 120=Some (Vint Int.zero) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds w ->
 fe_at m pa 0 (words5 x) -> fe_at m pa 40 (words5 y) -> fe_at m pa 80 (words5 z) ->
 fe_at m pb 0 (words5 u) -> fe_at m pb 40 (words5 v) -> fe_at m pb 80 (words5 w) ->
 Mem.range_perm m pa 0 128 Cur Freeable -> Mem.range_perm m pb 0 128 Cur Freeable ->
 Mem.range_perm m pu 0 40 Cur Freeable -> Mem.range_perm m pv 0 40 Cur Freeable ->
 Mem.range_perm m ps 0 40 Cur Freeable -> Mem.range_perm m pt 0 40 Cur Freeable ->
 Mem.range_perm m p12 0 40 Cur Freeable -> Mem.range_perm m p22 0 40 Cur Freeable ->
 Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
 Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable ->
 Mem.range_perm m bt 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_var) E0
   (gej_add_finite_temps le x y z u v w) mf (gej_add_finite_out x z u w) /\
 fe_at mf pa 0 (words5 (gej_add_finite_x_words x y z u v w)) /\
 fe_at mf pa 40 (words5 (gej_add_finite_y_words x y z u v w)) /\
 fe_at mf pa 80 (words5 (gej_add_finite_z_words x y z u v w)) /\
 Mem.load Mint32 mf pa 120=Some (Vint (gej_add_finite_flag x y z u v w)) /\
 Mem.range_perm mf pa 0 128 Cur Freeable /\ Mem.range_perm mf pb 0 128 Cur Freeable /\
 Mem.range_perm mf pu 0 40 Cur Freeable /\ Mem.range_perm mf pv 0 40 Cur Freeable /\
 Mem.range_perm mf ps 0 40 Cur Freeable /\ Mem.range_perm mf pt 0 40 Cur Freeable /\
 Mem.range_perm mf p12 0 40 Cur Freeable /\ Mem.range_perm mf p22 0 40 Cur Freeable /\
 Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
 Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
 Mem.range_perm mf bt 0 40 Cur Freeable /\
 square_input_bounds (gej_add_finite_x_words x y z u v w) /\
 square_input_bounds (gej_add_finite_y_words x y z u v w) /\
 square_input_bounds (gej_add_finite_z_words x y z u v w) /\
 lframe (gej_add_finite_nonzero_frame pa pb pu pv ps pt p12 p22 bh bi b2 b3 bt) m mf.
Proof.
 intros PA PB PR PN EU EV ES ET E12 E22 EH EI E2 E3 ETemp EQ EM EN EA E0N ED EF
   Sep FlagA FlagB BX BY BZ BU BV BW AX AY AZ BXf BYf BZf FA FB FU FV FS FT F12 F22 FH FI F2 F3 FTemp.
 unfold gej_add_finite_temps,gej_add_finite_out,gej_add_finite_x_words,
   gej_add_finite_y_words,gej_add_finite_z_words,gej_add_finite_flag.
 destruct (Z.eqb (radix_value (gej_add_h_words x z u w) mod feP) 0) eqn:HZ.
 - apply Z.eqb_eq in HZ.
   pose proof Sep as Sep0;separate_blocks Sep0.
   assert (SepZ : NoDup [pa;pb;pu;pv;ps;pt;p12;p22;bh;bi]).
   { exact (@NoDup_app_remove_r block [pa;pb;pu;pv;ps;pt;p12;p22;bh;bi]
       [b2;b3;bt] Sep). }
   destruct (exec_gej_add_finite_zero_body e le m pa pb pu pv ps pt p12 p22 bh bi x y z u v w
     PA PB PR PN EU EV ES ET E12 E22 EH EI EQ EM EN EA E0N ED EF SepZ FlagA FlagB
     BX BY BZ BU BV BW HZ AX AY AZ BXf BYf BZf FA FB FU FV FS FT F12 F22 FH FI)
     as (mf & Body & XO & YO & ZO & FlagO & FAO & FBO & FUO & FVO & FSO & FTO &
       F12O & F22O & FHO & FIO & BoundX & BoundY & BoundZ & FrameZ).
   assert (F2O : Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_free F2 FrameZ).
   assert (F3O : Mem.range_perm mf b3 0 40 Cur Freeable) by (keep_free F3 FrameZ).
   assert (FTempO : Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_free FTemp FrameZ).
   assert (Frame : lframe (gej_add_finite_nonzero_frame pa pb pu pv ps pt p12 p22 bh bi b2 b3 bt) m mf).
   { eapply lframe_implies;[exact FrameZ|].
     intros bx pos (NA & NB & NU & NV & NS & NT & N12 & N22 & NH & NI & N2 & N3 & NTemp) VB;
       unfold gej_add_finite_return_frame;repeat split;assumption. }
   exists mf;repeat (first [assumption|split]).
 - apply Z.eqb_neq in HZ.
   exact (exec_gej_add_finite_nonzero_body e le m pa pb pu pv ps pt p12 p22 bh bi b2 b3 bt x y z u v w
     PA PB PR PN EU EV ES ET E12 E22 EH EI E2 E3 ETemp EQ EM EN EA E0N ED EF Sep FlagA FlagB
     BX BY BZ BU BV BW HZ AX AY AZ BXf BYf BZf FA FB FU FV FS FT F12 F22 FH FI F2 F3 FTemp).
Qed.
