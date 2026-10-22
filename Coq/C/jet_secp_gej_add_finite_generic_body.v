(** Actual whole finite projective C helper body against the fixed literal
    Simplicity result, from six bounded field representations and their residues. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_square_spec_bridge C.jet_secp_curve_statements
 C.jet_secp_gej_add_finite_body C.jet_secp_gej_add_finite_nonzero C.jet_secp_gej_add_finite_generic C.jet_secp_gej_add_flag
 C.jet_secp_rescale_literal C.jet_secp_canonical_zero C.jet_secp_add_literal.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output literal_gej_add canonical_fe_is_zero.

Theorem exec_gej_add_finite_body_generic e le m pa pb pu pv ps pt p12 p22 bh bi b2 b3 bt mx my mz mu mv mw (ax ay az bx byword bz : Ty.tySem (Word 8)) :
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
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=Datatypes.false ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem bz)=Datatypes.false ->
 fe_at m pa 0 (words5 mx) -> fe_at m pa 40 (words5 my) -> fe_at m pa 80 (words5 mz) ->
 fe_at m pb 0 (words5 mu) -> fe_at m pb 40 (words5 mv) -> fe_at m pb 80 (words5 mw) ->
 Mem.range_perm m pa 0 128 Cur Freeable -> Mem.range_perm m pb 0 128 Cur Freeable ->
 Mem.range_perm m pu 0 40 Cur Freeable -> Mem.range_perm m pv 0 40 Cur Freeable ->
 Mem.range_perm m ps 0 40 Cur Freeable -> Mem.range_perm m pt 0 40 Cur Freeable ->
 Mem.range_perm m p12 0 40 Cur Freeable -> Mem.range_perm m p22 0 40 Cur Freeable ->
 Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable ->
 Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable ->
 Mem.range_perm m bt 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_var) E0
   (gej_add_finite_temps le mx my mz mu mv mw) mf (gej_add_finite_out mx mz mu mw) /\
 fe_at mf pa 0 (words5 (gej_add_finite_x_words mx my mz mu mv mw)) /\
 fe_at mf pa 40 (words5 (gej_add_finite_y_words mx my mz mu mv mw)) /\
 fe_at mf pa 80 (words5 (gej_add_finite_z_words mx my mz mu mv mw)) /\
 Mem.load Mint32 mf pa 120=Some (Vint (gej_add_finite_flag mx my mz mu mv mw)) /\
 Mem.load Mint32 mf pa 120=Some (Vint (bit_int (Bit.toBool
   (@jet_secp_literal_gej_predicate.literal_gej_is_infinity Alg.CoreFunSem
     (@literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz))))))) /\
 Mem.range_perm mf pa 0 128 Cur Freeable /\ Mem.range_perm mf pb 0 128 Cur Freeable /\
 Mem.range_perm mf pu 0 40 Cur Freeable /\ Mem.range_perm mf pv 0 40 Cur Freeable /\
 Mem.range_perm mf ps 0 40 Cur Freeable /\ Mem.range_perm mf pt 0 40 Cur Freeable /\
 Mem.range_perm mf p12 0 40 Cur Freeable /\ Mem.range_perm mf p22 0 40 Cur Freeable /\
 Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
 Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
 Mem.range_perm mf bt 0 40 Cur Freeable /\
 square_input_bounds (gej_add_finite_x_words mx my mz mu mv mw) /\
 square_input_bounds (gej_add_finite_y_words mx my mz mu mv mw) /\
 square_input_bounds (gej_add_finite_z_words mx my mz mu mv mw) /\
 ((rescale_field_output (gej_add_finite_x_words mx my mz mu mv mw),
   rescale_field_output (gej_add_finite_y_words mx my mz mu mv mw)),
   rescale_field_output (gej_add_finite_z_words mx my mz mu mv mw))=
 @literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)) /\
 lframe (gej_add_finite_nonzero_frame pa pb pu pv ps pt p12 p22 bh bi b2 b3 bt) m mf.
Proof.
 intros PA PB PR PN EU EV ES ET E12 E22 EH EI E2 E3 ETemp EQ EM EN EA E0N ED EF
   Sep FlagA FlagB BMX BMY BMZ BMU BMV BMW RMX RMY RMZ RMU RMV RMW FinA FinB AX AY AZ BXf BYf BZf FA FB FU FV FS FT F12 F22 FH FI F2 F3 FTemp.
 rewrite FinA in FlagA;rewrite FinB in FlagB.
 change (Mem.load Mint32 m pa 120=Some (Vint Int.zero)) in FlagA.
 change (Mem.load Mint32 m pb 120=Some (Vint Int.zero)) in FlagB.
 destruct (exec_gej_add_finite_body e le m pa pb pu pv ps pt p12 p22 bh bi b2 b3 bt
   mx my mz
   mu mv mw
   PA PB PR PN EU EV ES ET E12 E22 EH EI E2 E3 ETemp EQ EM EN EA E0N ED EF Sep FlagA FlagB
   BMX BMY BMZ BMU BMV BMW
   AX AY AZ BXf BYf BZf FA FB FU FV FS FT F12 F22 FH FI F2 F3 FTemp)
   as (mf & Body & XO & YO & ZO & FlagO & FAO & FBO & FUO & FVO & FSO & FTO &
     F12O & F22O & FHO & FIO & F2O & F3O & FTempO & BoundX & BoundY & BoundZ & Frame).
 pose proof (gej_add_finite_outputs_literal mx my mz mu mv mw ax ay az bx byword bz
   BMX BMY BMZ BMU BMV BMW RMX RMY RMZ RMU RMV RMW FinA FinB) as Literal.
 assert (SpecFlag : Mem.load Mint32 mf pa 120=Some (Vint (bit_int (Bit.toBool
   (@jet_secp_literal_gej_predicate.literal_gej_is_infinity Alg.CoreFunSem
     (@literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)))))))).
 { rewrite (gej_add_finite_flag_bit mx my mz mu mv mw) in FlagO.
   rewrite (gej_add_finite_flag_matches_literal mx my mz mu mv mw ax ay az bx byword bz
     BMX BMY BMZ BMU BMV BMW RMX RMY RMZ RMU RMV RMW FinA FinB) in FlagO;exact FlagO. }
 exists mf;repeat (first [assumption|split]).
Qed.
