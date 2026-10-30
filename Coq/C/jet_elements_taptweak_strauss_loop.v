(** The complete original descending loop with all four digit streams. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_strauss_point_loop C.jet_secp_strauss_digit_guard
 C.jet_secp_generator_digit_control C.jet_secp_generator_loop_control
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge
 C.jet_secp_square_columns C.jet_secp_field_mul_small
 C.jet_secp_globalz_loop C.jet_secp_globalz_pass2 C.jet_secp_globalz_word_walk
 C.jet_secp_scalar_table_literal C.jet_secp_wnaf5_literal C.jet_secp_strauss_wnaf_calls
 C.jet_secp_rescale_literal C.jet_secp_canonical_zero C.jet_secp_double_loose_literal
 C.jet_secp_double_literal C.jet_secp_mixed_xy_literal C.jet_secp_strauss_program
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_secp_slice_permissions
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Opaque secp_ge rescale_field_output literal_gej_double literal_strauss_step.
Set Default Timeout 10.

Require Import C.jet_secp_strauss_general_iteration C.jet_secp_generator_globals C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_values C.jet_secp_wnaf_literal_array.

Require Import C.jet_secp_strauss_general_loop C.jet_transport C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_generator_globals.
Require Import C.jet_elements_taptweak_strauss_iteration.
Local Opaque elements_taptweak_ge.
Lemma eval_elements_taptweak_generator_loop_guard e le m i : -1<=i<129 -> le!_i=Some (Vint (Int.repr i)) ->
 eval_expr elements_taptweak_ge e le m
   (Ebinop Oge (Etempvar _i tint) (Econst_int Int.zero tint) tint)
   (Vint (if 0<=?i then Int.one else Int.zero)).
Proof.
 intros Index PI;eapply eval_Ebinop;[apply eval_Etempvar;exact PI|constructor|].
 change (Some (Val.of_bool (negb (Int.lt (Int.repr i) Int.zero)))=
   Some (Vint (if 0<=?i then Int.one else Int.zero))).
 unfold Int.lt;rewrite Int.signed_repr by
   (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
 change (Some (Val.of_bool (negb (if Coqlib.zlt i 0 then true else false)))=
   Some (Vint (if 0<=?i then Int.one else Int.zero))).
 destruct (Coqlib.zlt i 0),(Z.leb_spec 0 i);try lia;reflexivity.
Qed.

Theorem exec_elements_taptweak_generator_loop_done e le m : le!_i=Some (Vint (Int.repr (-1))) ->
 Clight2.exec_stmt elements_taptweak_ge e le m generator_descending_loop E0 le m Out_normal.
Proof.
 intro PI;rewrite generator_descending_loop_source.
 eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
 eapply exec_Sseq_2;[|discriminate].
 eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
 exact (eval_elements_taptweak_generator_loop_guard e le m (-1) ltac:(lia) PI).
Qed.

Lemma exec_elements_taptweak_generator_loop_join e le m i lei mi lef mf :
 0<=i<129 -> le!_i=Some (Vint (Int.repr i)) -> lei!_i=Some (Vint (Int.repr i)) ->
 Clight2.exec_stmt elements_taptweak_ge e le m generator_loop_arithmetic E0 lei mi Out_normal ->
 Clight2.exec_stmt elements_taptweak_ge e (PTree.set _i (Vint (Int.repr (i-1))) lei) mi
   generator_descending_loop E0 lef mf Out_normal ->
 Clight2.exec_stmt elements_taptweak_ge e le m generator_descending_loop E0 lef mf Out_normal.
Proof.
 intros Index PI PII Body Rest;rewrite generator_descending_loop_source in Rest|-*.
 eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0) (le1:=lei) (m1:=mi)
   (out1:=Out_normal) (le2:=PTree.set _i (Vint (Int.repr (i-1))) lei) (m2:=mi).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m).
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|constructor].
     pose proof (eval_elements_taptweak_generator_loop_guard e le m i ltac:(lia) PI) as Guard.
     rewrite (proj2 (Z.leb_le 0 i) ltac:(lia)) in Guard;exact Guard.
   + exact Body.
 - constructor.
 - apply exec_Sset;eapply eval_Ebinop;[apply eval_Etempvar;exact PII|constructor|].
   change (Some (Vint (Int.sub (Int.repr i) Int.one))=Some (Vint (Int.repr (i-1)))).
   change Int.one with (Int.repr 1);rewrite Int.sub_signed,!Int.signed_repr by
     (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia);reflexivity.
 - exact Rest.
Qed.
Section Descending.
Variable e:env.
Variables br bs bp bd bt bx bb bg1 bg128:block.
Variable inv:nat->int64.
Variables xs ys aux:nat->nat->int64.
Variable zctx:Ty.tySem (Word 8).
Variables bits1 bitslam bitsg1 bitsg128:Z.
Variables digits1 digitslam:Z->Ty.tySem literal_wnaf5_digit.
Variables digitsg1 digitsg128:Z->Ty.tySem literal_wnaf_digit.
Hypothesis Len1:0<=bits1<=129.
Hypothesis LenLam:0<=bitslam<=129.
Hypothesis LenG1:0<=bitsg1<=129.
Hypothesis LenG128:0<=bitsg128<=129.
Hypothesis ValidG1:forall j,0<=j<129 -> wnaf_literal_valid (digitsg1 j).
Hypothesis ValidG128:forall j,0<=j<129 -> wnaf_literal_valid (digitsg128 j).
Hypothesis Separate:NoDup [br;bd;bs;bp;bt;bx;bb;bg1;bg128].
Hypothesis Plain:plain_env e.
Hypothesis Domain:edom e(fn_vars f_secp256k1_ecmult_strauss_wnaf).
Hypothesis BoundLocals:forall id,In id(map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)) ->exists b ty,e!id=Some(b,ty).
Hypothesis ArrayG1:e!_wnaf_ng_1=Some (bg1,tarray tint 129).
Hypothesis ArrayG128:e!_wnaf_ng_128=Some (bg128,tarray tint 129).
Hypothesis LocalZ:e!_Z=Some (bb,curve_fe_type).
Hypothesis GetStorage:e!_secp256k1_ecmult_table_get_ge_storage=None.
Hypothesis AddZinv:e!_secp256k1_gej_add_zinv_var=None.
Hypothesis TableG1:e!(generator_table_id false)=None.
Hypothesis TableG128:e!(generator_table_id true)=None.
Hypothesis BI:square_input_bounds inv.
Hypothesis Scale:radix_value inv mod feP=@toZ (WordToZ 8) zctx mod feP.
Hypothesis AbsentG1:forall j,0<=j<129 -> bitsg1<=j -> digitsg1 j=inl tt.
Hypothesis AbsentG128:forall j,0<=j<129 -> bitsg128<=j -> digitsg128 j=inl tt.
Hypothesis Local:e!_tmpa=Some (bd,Tstruct __6121 noattr).
Hypothesis Get:e!_secp256k1_ecmult_table_get_ge=None.
Hypothesis GetLam:e!_secp256k1_ecmult_table_get_ge_lambda=None.
Hypothesis Add:e!_secp256k1_gej_add_ge_var=None.
Hypothesis DoubleSymbol:e!_secp256k1_gej_double_var=None.
Hypothesis Bounds:globalz_table_bounds xs ys.
Hypothesis Tight:forall k,(k<8)%nat -> mul_small_input_bounds (ys k).
Hypothesis AuxBounds:forall k,(k<8)%nat -> square_input_bounds (aux k).
Hypothesis AuxLiteral:forall k,(k<8)%nat -> rescale_field_output (aux k)=
 @C.jet_secp_beta_spec.literal_fe_multiply_beta Alg.CoreFunSem (rescale_field_output (xs k)).
Hypothesis Absent1:forall j,0<=j<129 -> bits1<=j -> digits1 j=inl tt.
Hypothesis AbsentLam:forall j,0<=j<129 -> bitslam<=j -> digitslam j=inl tt.

Theorem exec_elements_taptweak_strauss_loop count : (count<=129)%nat ->
 forall le m x y z (ax ay az:Ty.tySem (Word 8)),
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_i=Some (Vint (Int.repr (Z.of_nat count-1))) -> le!_no=Some (Vlong Int64.one) ->
 le!_bits_ng_1=Some (Vint (Int.repr bitsg1)) -> le!_bits_ng_128=Some (Vint (Int.repr bitsg128)) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 Mem.load Mint32 m bp 1032=Some (Vint (Int.repr bits1)) ->
 Mem.load Mint32 m bp 1036=Some (Vint (Int.repr bitslam)) ->
 (forall j,0<=j<bits1 -> Mem.load Mint32 m bp (4*j)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value (digits1 j))))) ->
 (forall j,0<=j<bitslam -> Mem.load Mint32 m bp (516+4*j)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value (digitslam j))))) ->
 (forall j,0<=j<bitsg1 -> Mem.load Mint32 m bg1 (4*j)=Some (Vint (Int.repr (wnaf_literal_value (digitsg1 j))))) ->
 (forall j,0<=j<bitsg128 -> Mem.load Mint32 m bg128 (4*j)=Some (Vint (Int.repr (wnaf_literal_value (digitsg128 j))))) ->
 (forall h,elements_taptweak_generator_table_state h m) -> fe_at m bb 0 (words5 inv) -> Mem.range_perm m bb 0 40 Cur Freeable ->
 globalz_table_rep m bt xs ys ->
 (forall k,(k<8)%nat -> fe_at m bx (40*Z.of_nat k) (words5 (aux k))) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=((ax,ay),az) ->
 fe_at m br 0 (words5 x) -> fe_at m br 40 (words5 y) -> fe_at m br 80 (words5 z) ->
 Mem.load Mint32 m br 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m bd 0 88 Cur Freeable ->
 Mem.range_perm m bt 0 704 Cur Freeable -> Mem.range_perm m bx 0 320 Cur Freeable ->
 exists lef mf ox oy oz,
 Clight2.exec_stmt elements_taptweak_ge e le m generator_descending_loop E0 lef mf Out_normal /\
 lef!_i=Some (Vint (Int.repr (-1))) /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  strauss_general_loop_result count digits1 digitslam digitsg1 digitsg128 (zctx,globalz_word_vector (globalz_decoded_points xs ys)) ((ax,ay),az) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
 Mem.range_perm mf bt 0 704 Cur Freeable /\ Mem.range_perm mf bx 0 320 Cur Freeable /\
 fe_at mf bb 0 (words5 inv) /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
 (forall h,elements_taptweak_generator_table_state h mf) /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (fun b _=>b<>br /\ b<>bd /\ b<>bb) m mf /\
 (forall id,~In id [_i;_np;_n;_t'8;_t'9;_t'10;_t'11;_t'12;_t'13;_t'14;_t'15;_t'17;_t'18;_t'19;_t'20;_t'21;_t'22;_t'23;_t'24;_t'25;_t'26;_t'27;_t'28;_t'29] -> lef!id=le!id).
Proof.
 induction count as [|count IH];intros Count le m x y z ax ay az R State I No G1 G128
  PS PT PX Count1 CountLam Load1 LoadLam LoadG1 LoadG128 Tables Inv FreeZ Table Aux BX BY BZ Repr X Y Z Flag FreeR FreeD FreeT FreeX.
 - exists le,m,x,y,z;split;[apply exec_elements_taptweak_generator_loop_done;exact I|];split;[exact I|].
   assert (FlagO:Mem.load Mint32 m br 120=Some (Vint (bit_int (Bit.toBool
     (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output z)))))).
   { assert (Eq:rescale_field_output z=az) by congruence;rewrite Eq;exact Flag. }
   split;[exact X|];split;[exact Y|];split;[exact Z|];split;[exact FlagO|];
   split;[exact BX|];split;[exact BY|];split;[exact BZ|];split;[exact Repr|];
   split;[exact FreeR|];split;[exact FreeD|];split;[exact FreeT|];split;[exact FreeX|];
   split;[exact Inv|];split;[exact FreeZ|];split;[exact Tables|];
   split;[apply keeps_permissions_refl|];split;[apply preserved_refl|];split;[apply lframe_refl|intros;reflexivity].
 - assert (Index:0<=Z.of_nat count<129) by (pose proof (Nat2Z.is_nonneg count);lia).
   assert (IC:le!_i=Some (Vint (Int.repr (Z.of_nat count)))).
   { replace (Z.of_nat count) with (Z.of_nat (S count)-1) by (rewrite Nat2Z.inj_succ;lia);exact I. }
   destruct (exec_elements_taptweak_strauss_iteration (digits1 (Z.of_nat count)) (digitslam (Z.of_nat count))
    (digitsg1 (Z.of_nat count)) (digitsg128 (Z.of_nat count))
    xs ys aux x y z inv ax ay az zctx e le m br bs bp bd bt bx bb bg1 bg128
    (Z.of_nat count) bits1 bitslam bitsg1 bitsg128
    Index Len1 LenLam LenG1 LenG128 (ValidG1 _ Index) (ValidG128 _ Index) Separate Plain Domain BoundLocals Tables
    ArrayG1 ArrayG128 LocalZ GetStorage AddZinv TableG1 TableG128
    Local Get GetLam Add DoubleSymbol R State IC No G1 G128
    ltac:(intro H;apply LoadG1;lia) ltac:(intro H;apply LoadG128;lia)
    (AbsentG1 _ Index) (AbsentG128 _ Index) PS PT PX Count1 CountLam
    ltac:(intro H;apply Load1;lia) ltac:(intro H;apply LoadLam;lia)
    (Absent1 _ Index) (AbsentLam _ Index) Table Bounds Tight Aux AuxBounds AuxLiteral
    BX BY BZ BI Scale Inv FreeZ Repr X Y Z Flag FreeR FreeD FreeT FreeX)
    as (mi & ix & iy & iz & Body & XI & YI & ZI & FlagI & BXI & BYI & BZI & LiteralI &
     FRI & FDI & FTI & FXI & InvI & FZI & TablesI & KeepI & ReadonlyI & FrameI).
   pose (li:=strauss_general_iteration_temps le bp bt bx (Z.of_nat count) bits1 bitslam bitsg1 bitsg128
    (digits1 (Z.of_nat count)) (digitslam (Z.of_nat count)) (digitsg1 (Z.of_nat count)) (digitsg128 (Z.of_nat count))).
   pose (ln:=PTree.set _i (Vint (Int.repr (Z.of_nat count-1))) li).
   assert (ICi:li!_i=Some (Vint (Int.repr (Z.of_nat count)))).
   { unfold li;rewrite strauss_general_iteration_other by (clear;cbn [In];intuition discriminate);exact IC. }
   assert (Protected:forall b,In b [bs;bp;bt;bx;bg1;bg128] -> b<>br /\ b<>bd /\ b<>bb).
   { pose proof Separate as Sep;inversion Sep as [|? ? NotR Tail];subst.
     inversion Tail as [|? ? NotD Tail2];subst.
     pose proof (NoDup_remove_2 [br;bd;bs;bp;bt;bx] [bg1;bg128] bb Separate) as NotZ.
     intros b Member;split.
     - intro Eq;subst b;apply NotR;clear -Member;cbn [In] in Member|-*;tauto.
     - split.
       + intro Eq;subst b;apply NotD;clear -Member;cbn [In] in Member|-*;tauto.
       + intro Eq;subst b;apply NotZ;clear -Member;cbn [app In] in Member|-*;tauto. }
   assert (Saved:forall chunk b ofs value,b<>br /\ b<>bd /\ b<>bb ->
    Mem.load chunk m b ofs=Some value -> Mem.load chunk mi b ofs=Some value).
   { intros chunk b ofs value Outside Load;rewrite (proj1 FrameI chunk b ofs);[exact Load| |intros;exact Outside].
     eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
      [eapply Mem.load_valid_access;exact Load|apply perm_any_N]. }
   assert (PSI:Mem.load Mptr mi bs 16=Some (Vptr bp Ptrofs.zero)).
   { apply Saved;[apply Protected;clear;cbn [In];tauto|exact PS]. }
   assert (PTI:Mem.load Mptr mi bs 8=Some (Vptr bt Ptrofs.zero)).
   { apply Saved;[apply Protected;clear;cbn [In];tauto|exact PT]. }
   assert (PXI:Mem.load Mptr mi bs 0=Some (Vptr bx Ptrofs.zero)).
   { apply Saved;[apply Protected;clear;cbn [In];tauto|exact PX]. }
   assert (C1I:Mem.load Mint32 mi bp 1032=Some (Vint (Int.repr bits1))).
   { apply Saved;[apply Protected;clear;cbn [In];tauto|exact Count1]. }
   assert (CLI:Mem.load Mint32 mi bp 1036=Some (Vint (Int.repr bitslam))).
   { apply Saved;[apply Protected;clear;cbn [In];tauto|exact CountLam]. }
   assert (L1I:forall j,0<=j<bits1 -> Mem.load Mint32 mi bp (4*j)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value (digits1 j))))).
   { intros j H;apply Saved;[apply Protected;clear;cbn [In];tauto|apply Load1;exact H]. }
   assert (LLI:forall j,0<=j<bitslam -> Mem.load Mint32 mi bp (516+4*j)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value (digitslam j))))).
   { intros j H;apply Saved;[apply Protected;clear;cbn [In];tauto|apply LoadLam;exact H]. }
   assert (LG1I:forall j,0<=j<bitsg1 -> Mem.load Mint32 mi bg1 (4*j)=Some (Vint (Int.repr (wnaf_literal_value (digitsg1 j))))).
   { intros j H;apply Saved;[apply Protected;clear;cbn [In];tauto|apply LoadG1;exact H]. }
   assert (LG128I:forall j,0<=j<bitsg128 -> Mem.load Mint32 mi bg128 (4*j)=Some (Vint (Int.repr (wnaf_literal_value (digitsg128 j))))).
   { intros j H;apply Saved;[apply Protected;clear;cbn [In];tauto|apply LoadG128;exact H]. }
   assert (TableI:globalz_table_rep mi bt xs ys).
   { intros k K;destruct (Table k K) as (TX & TY & TF);split.
     - eapply field_at_lframe;[exact TX|exact FrameI|intros;apply Protected;clear;cbn [In];tauto].
     - split.
       + eapply field_at_lframe;[exact TY|exact FrameI|intros;apply Protected;clear;cbn [In];tauto].
       + apply Saved;[apply Protected;clear;cbn [In];tauto|exact TF]. }
   assert (AuxI:forall k,(k<8)%nat -> fe_at mi bx (40*Z.of_nat k) (words5 (aux k))).
   { intros k K;eapply field_at_lframe;[apply Aux;exact K|exact FrameI|intros;apply Protected;clear;cbn [In];tauto]. }
   assert (RN:ln!_r=Some (Vptr br Ptrofs.zero)).
   { unfold ln;rewrite PTree.gso by discriminate;unfold li;
     rewrite strauss_general_iteration_other by (clear;cbn [In];intuition discriminate);exact R. }
   assert (SN:ln!_state=Some (Vptr bs Ptrofs.zero)).
   { unfold ln;rewrite PTree.gso by discriminate;unfold li;
     rewrite strauss_general_iteration_other by (clear;cbn [In];intuition discriminate);exact State. }
   assert (NN:ln!_no=Some (Vlong Int64.one)).
   { unfold ln;rewrite PTree.gso by discriminate;unfold li;
     rewrite strauss_general_iteration_other by (clear;cbn [In];intuition discriminate);exact No. }
   assert (G1N:ln!_bits_ng_1=Some (Vint (Int.repr bitsg1))).
   { unfold ln;rewrite PTree.gso by discriminate;unfold li;
     rewrite strauss_general_iteration_other by (clear;cbn [In];intuition discriminate);exact G1. }
   assert (G128N:ln!_bits_ng_128=Some (Vint (Int.repr bitsg128))).
   { unfold ln;rewrite PTree.gso by discriminate;unfold li;
     rewrite strauss_general_iteration_other by (clear;cbn [In];intuition discriminate);exact G128. }
   destruct (IH ltac:(lia) ln mi ix iy iz
    (rescale_field_output ix) (rescale_field_output iy) (rescale_field_output iz)
    RN SN (PTree.gss _ _ _) NN G1N G128N PSI PTI PXI C1I CLI L1I LLI LG1I LG128I TablesI InvI FZI TableI AuxI
    BXI BYI BZI eq_refl XI YI ZI FlagI FRI FDI FTI FXI)
    as (lef & mf & ox & oy & oz & Rest & FinalI & XO & YO & ZO & FlagO & BXO & BYO & BZO &
     LiteralF & FRF & FDF & FTF & FXF & InvF & FZF & TablesF & KeepF & ReadonlyF & FrameF & OtherF).
   exists lef,mf,ox,oy,oz;split.
   + exact (exec_elements_taptweak_generator_loop_join e le m (Z.of_nat count) li mi lef mf Index IC ICi Body Rest).
   + split;[exact FinalI|];split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];
     split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];split.
     * rewrite LiteralI in LiteralF;exact LiteralF.
     * split;[exact FRF|];split;[exact FDF|];split;[exact FTF|];split;[exact FXF|];split;[exact InvF|];split;[exact FZF|];split;[exact TablesF|];split.
       -- eapply keeps_permissions_trans;[exact KeepI|exact KeepF].
       -- split;[eapply preserved_trans;[exact ReadonlyI|exact ReadonlyF]|];split.
          ++ eapply lframe_trans;[exact FrameI|exact FrameF].
          ++ intros id Outside;rewrite OtherF by exact Outside.
             unfold ln;rewrite PTree.gso by (intro Eq;apply Outside;subst id;cbn [In];tauto).
             unfold li;apply strauss_general_iteration_other;clear -Outside;cbn [In] in Outside|-*;tauto.
Qed.
End Descending.

