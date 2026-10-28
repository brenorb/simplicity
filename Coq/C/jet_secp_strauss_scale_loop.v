(** The complete original descending loop for zero generator counts. *)
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

Require Import C.jet_secp_strauss_scale_iteration.

(** Bounded induction for the original descending loop, with no curve premise. *)
Fixpoint strauss_scale_loop_result (count:nat) (digits1 digitslam:Z->Ty.tySem literal_wnaf5_digit)
 (context:Ty.tySem literal_strauss_context) (point:Ty.tySem literal_table_gej) :=
 match count with
 | O=>point
 | S count=>strauss_scale_loop_result count digits1 digitslam context
   (@literal_strauss_step Alg.CoreFunSem (point,(context,((digits1 (Z.of_nat count),digitslam (Z.of_nat count)),(inl tt,inl tt)))))
 end.
Section Descending.
Variable e:env.
Variables br bs bp bd bt bx:block.
Variables xs ys aux:nat->nat->int64.
Variable zctx:Ty.tySem (Word 8).
Variables bits1 bitslam:Z.
Variables digits1 digitslam:Z->Ty.tySem literal_wnaf5_digit.
Hypothesis Len1:0<=bits1<=129.
Hypothesis LenLam:0<=bitslam<=129.
Hypothesis Separate:NoDup [br;bd;bs;bp;bt;bx].
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

Theorem exec_strauss_scale_loop count : (count<=129)%nat ->
 forall le m x y z (ax ay az:Ty.tySem (Word 8)),
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_i=Some (Vint (Int.repr (Z.of_nat count-1))) -> le!_no=Some (Vlong Int64.one) ->
 le!_bits_ng_1=Some (Vint Int.zero) -> le!_bits_ng_128=Some (Vint Int.zero) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 Mem.load Mint32 m bp 1032=Some (Vint (Int.repr bits1)) ->
 Mem.load Mint32 m bp 1036=Some (Vint (Int.repr bitslam)) ->
 (forall j,0<=j<bits1 -> Mem.load Mint32 m bp (4*j)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value (digits1 j))))) ->
 (forall j,0<=j<bitslam -> Mem.load Mint32 m bp (516+4*j)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value (digitslam j))))) ->
 globalz_table_rep m bt xs ys ->
 (forall k,(k<8)%nat -> fe_at m bx (40*Z.of_nat k) (words5 (aux k))) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=((ax,ay),az) ->
 fe_at m br 0 (words5 x) -> fe_at m br 40 (words5 y) -> fe_at m br 80 (words5 z) ->
 Mem.load Mint32 m br 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m bd 0 88 Cur Freeable ->
 Mem.range_perm m bt 0 704 Cur Freeable -> Mem.range_perm m bx 0 320 Cur Freeable ->
 exists lef mf ox oy oz,
 Clight2.exec_stmt secp_ge e le m generator_descending_loop E0 lef mf Out_normal /\
 lef!_i=Some (Vint (Int.repr (-1))) /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  strauss_scale_loop_result count digits1 digitslam (zctx,globalz_word_vector (globalz_decoded_points xs ys)) ((ax,ay),az) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
 Mem.range_perm mf bt 0 704 Cur Freeable /\ Mem.range_perm mf bx 0 320 Cur Freeable /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (fun b _=>b<>br /\ b<>bd) m mf /\
 (forall id,~In id [_i;_np;_n;_t'8;_t'9;_t'10;_t'11;_t'12;_t'14;_t'19;_t'20;_t'21;_t'22;_t'23;_t'24;_t'25;_t'26;_t'27;_t'28;_t'29] -> lef!id=le!id).
Proof.
 induction count as [|count IH];intros Count le m x y z ax ay az R State I No G1 G128
  PS PT PX Count1 CountLam Load1 LoadLam Table Aux BX BY BZ Repr X Y Z Flag FreeR FreeD FreeT FreeX.
 - exists le,m,x,y,z;split;[apply exec_generator_loop_done;exact I|];split;[exact I|].
   assert (FlagO:Mem.load Mint32 m br 120=Some (Vint (bit_int (Bit.toBool
     (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output z)))))).
   { assert (Eq:rescale_field_output z=az) by congruence;rewrite Eq;exact Flag. }
   split;[exact X|];split;[exact Y|];split;[exact Z|];split;[exact FlagO|];
   split;[exact BX|];split;[exact BY|];split;[exact BZ|];split;[exact Repr|];
   split;[exact FreeR|];split;[exact FreeD|];split;[exact FreeT|];split;[exact FreeX|];
   split;[apply keeps_permissions_refl|];split;[apply preserved_refl|];split;[apply lframe_refl|intros;reflexivity].
 - assert (Index:0<=Z.of_nat count<129) by (pose proof (Nat2Z.is_nonneg count);lia).
   assert (IC:le!_i=Some (Vint (Int.repr (Z.of_nat count)))).
   { replace (Z.of_nat count) with (Z.of_nat (S count)-1) by (rewrite Nat2Z.inj_succ;lia);exact I. }
   destruct (exec_strauss_scale_iteration (digits1 (Z.of_nat count)) (digitslam (Z.of_nat count))
    xs ys aux x y z ax ay az zctx e le m br bs bp bd bt bx (Z.of_nat count) bits1 bitslam
    Index Len1 LenLam Separate Local Get GetLam Add DoubleSymbol R State IC No G1 G128 PS PT PX Count1 CountLam
    ltac:(intro H;apply Load1;lia) ltac:(intro H;apply LoadLam;lia)
    (Absent1 _ Index) (AbsentLam _ Index) Table Bounds Tight Aux AuxBounds AuxLiteral
    BX BY BZ Repr X Y Z Flag FreeR FreeD FreeT FreeX)
    as (mi & ix & iy & iz & Body & XI & YI & ZI & FlagI & BXI & BYI & BZI & LiteralI &
     FRI & FDI & FTI & FXI & KeepI & ReadonlyI & FrameI).
   pose (li:=strauss_scale_iteration_temps le bp bt bx (Z.of_nat count) bits1 bitslam
    (digits1 (Z.of_nat count)) (digitslam (Z.of_nat count))).
   pose (ln:=PTree.set _i (Vint (Int.repr (Z.of_nat count-1))) li).
   assert (ICi:li!_i=Some (Vint (Int.repr (Z.of_nat count)))).
   { unfold li;rewrite strauss_scale_iteration_other by (clear;cbn [In];intuition discriminate);exact IC. }
   assert (Protected:forall b,In b [bs;bp;bt;bx] -> b<>br /\ b<>bd).
   { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;
     intros b Member;cbn [In] in Member;intuition congruence. }
   assert (Saved:forall chunk b ofs value,b<>br /\ b<>bd ->
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
     rewrite strauss_scale_iteration_other by (clear;cbn [In];intuition discriminate);exact R. }
   assert (SN:ln!_state=Some (Vptr bs Ptrofs.zero)).
   { unfold ln;rewrite PTree.gso by discriminate;unfold li;
     rewrite strauss_scale_iteration_other by (clear;cbn [In];intuition discriminate);exact State. }
   assert (NN:ln!_no=Some (Vlong Int64.one)).
   { unfold ln;rewrite PTree.gso by discriminate;unfold li;
     rewrite strauss_scale_iteration_other by (clear;cbn [In];intuition discriminate);exact No. }
   assert (G1N:ln!_bits_ng_1=Some (Vint Int.zero)).
   { unfold ln;rewrite PTree.gso by discriminate;unfold li;
     rewrite strauss_scale_iteration_other by (clear;cbn [In];intuition discriminate);exact G1. }
   assert (G128N:ln!_bits_ng_128=Some (Vint Int.zero)).
   { unfold ln;rewrite PTree.gso by discriminate;unfold li;
     rewrite strauss_scale_iteration_other by (clear;cbn [In];intuition discriminate);exact G128. }
   destruct (IH ltac:(lia) ln mi ix iy iz
    (rescale_field_output ix) (rescale_field_output iy) (rescale_field_output iz)
    RN SN (PTree.gss _ _ _) NN G1N G128N PSI PTI PXI C1I CLI L1I LLI TableI AuxI
    BXI BYI BZI eq_refl XI YI ZI FlagI FRI FDI FTI FXI)
    as (lef & mf & ox & oy & oz & Rest & FinalI & XO & YO & ZO & FlagO & BXO & BYO & BZO &
     LiteralF & FRF & FDF & FTF & FXF & KeepF & ReadonlyF & FrameF & OtherF).
   exists lef,mf,ox,oy,oz;split.
   + exact (exec_generator_loop_join e le m (Z.of_nat count) li mi lef mf Index IC ICi Body Rest).
   + split;[exact FinalI|];split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];
     split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];split.
     * rewrite LiteralI in LiteralF;exact LiteralF.
     * split;[exact FRF|];split;[exact FDF|];split;[exact FTF|];split;[exact FXF|];split.
       -- eapply keeps_permissions_trans;[exact KeepI|exact KeepF].
       -- split;[eapply preserved_trans;[exact ReadonlyI|exact ReadonlyF]|];split.
          ++ eapply lframe_trans;[exact FrameI|exact FrameF].
          ++ intros id Outside;rewrite OtherF by exact Outside.
             unfold ln;rewrite PTree.gso by (intro Eq;apply Outside;subst id;cbn [In];tauto).
             unfold li;apply strauss_scale_iteration_other;cbn [In] in Outside|-*;tauto.
Qed.
End Descending.

Require Import C.jet_secp_generator_loop_literal C.jet_secp_literal_infinity.
Local Opaque literal_gej_infinity.

Lemma strauss_scale_loop_result_fold count digits1 digitslam context point :
 strauss_scale_loop_result count digits1 digitslam context point=
 fold_left (fun point pair=>@literal_strauss_step Alg.CoreFunSem
  (point,(context,(pair,(inl tt,inl tt)))))
  (map (fun j=>(digits1 (Z.of_nat j),digitslam (Z.of_nat j))) (rev (seq 0 count))) point.
Proof.
 revert point;induction count as [|count IH];intro point;[reflexivity|].
 cbn [strauss_scale_loop_result];rewrite IH,seq_S,rev_app_distr,map_app.
 cbn [rev app map fold_left Nat.add];reflexivity.
Qed.

Lemma strauss_scale_step_absent (point:Ty.tySem literal_table_gej) (context:Ty.tySem literal_strauss_context) :
 @literal_strauss_step Alg.CoreFunSem (point,(context,((inl tt,inl tt),(inl tt,inl tt))))=
 @literal_gej_double Alg.CoreFunSem point.
Proof. destruct context as [z table];rewrite literal_strauss_step_value;reflexivity. Qed.

Theorem strauss_scale_remove_leading_zeros count keep digits1 digitslam context :
 (keep<=count)%nat ->
 (forall j,(keep<=j<count)%nat -> digits1 (Z.of_nat j)=inl tt /\ digitslam (Z.of_nat j)=inl tt) ->
 strauss_scale_loop_result count digits1 digitslam context (@literal_gej_infinity Alg.CoreFunSem tt)=
 strauss_scale_loop_result keep digits1 digitslam context (@literal_gej_infinity Alg.CoreFunSem tt).
Proof.
 induction count as [|count IH];intros Bound Zeros.
 - assert (Eq:keep=0%nat) by lia;subst keep;reflexivity.
 - destruct (Nat.eq_dec keep (S count)) as [Eq|Different];[rewrite Eq;reflexivity|].
   destruct (Zeros count ltac:(lia)) as [Low High].
   change (strauss_scale_loop_result count digits1 digitslam context
     (@literal_strauss_step Alg.CoreFunSem
      (@literal_gej_infinity Alg.CoreFunSem tt,(context,
       ((digits1 (Z.of_nat count),digitslam (Z.of_nat count)),(inl tt,inl tt)))))=
    strauss_scale_loop_result keep digits1 digitslam context (@literal_gej_infinity Alg.CoreFunSem tt)).
   rewrite Low,High,strauss_scale_step_absent,generator_double_infinity.
   apply IH;[lia|intros j Range;apply Zeros;lia].
Qed.

Lemma strauss_combine_repeats {A B:Type} (a:A) (b:B) n :
 combine (repeat a n) (repeat b n)=repeat (a,b) n.
Proof. induction n as [|n IH];[reflexivity|cbn [repeat combine];f_equal;exact IH]. Qed.

Lemma strauss_scale_fold_absent_generators
 (point:Ty.tySem literal_table_gej) (context:Ty.tySem literal_strauss_context)
 (pairs:list (Ty.tySem (Ty.Prod literal_wnaf5_digit literal_wnaf5_digit))) :
 fold_left (fun point ds=>@literal_strauss_step Alg.CoreFunSem (point,(context,ds)))
  (combine pairs (repeat (inl tt,inl tt) (length pairs))) point=
 fold_left (fun point pair=>@literal_strauss_step Alg.CoreFunSem
  (point,(context,(pair,(inl tt,inl tt))))) pairs point.
Proof.
 revert point;induction pairs as [|pair pairs IH];intro point;[reflexivity|].
 change (fold_left (fun point ds=>@literal_strauss_step Alg.CoreFunSem (point,(context,ds)))
  (combine pairs (repeat (inl tt,inl tt) (length pairs)))
  (@literal_strauss_step Alg.CoreFunSem (point,(context,(pair,(inl tt,inl tt)))))=
 fold_left (fun point pair=>@literal_strauss_step Alg.CoreFunSem
  (point,(context,(pair,(inl tt,inl tt))))) pairs
  (@literal_strauss_step Alg.CoreFunSem (point,(context,(pair,(inl tt,inl tt)))))).
 apply IH.
Qed.

Theorem strauss_scale_loop_literal129 digits1 digitslam
 (point:Ty.tySem literal_table_gej) (context:Ty.tySem literal_strauss_context)
 (h1:Ty.tySem literal_wnaf5_digit) (t1:Ty.tySem (Vector literal_wnaf5_digit 7))
 (hlam:Ty.tySem literal_wnaf5_digit) (tlam:Ty.tySem (Vector literal_wnaf5_digit 7))
 (tg1 tg128:Ty.tySem (Vector C.jet_secp_wnaf_literal.literal_wnaf_digit 7)) :
 map (fun j=>(digits1 (Z.of_nat j),digitslam (Z.of_nat j))) (rev (seq 0 129))=
  (h1,hlam)::combine (literal_wnaf5_flatten 7 t1) (literal_wnaf5_flatten 7 tlam) ->
 C.jet_secp_wnaf_literal.literal_wnaf_flatten 7 tg1=repeat (inl tt) 128 ->
 C.jet_secp_wnaf_literal.literal_wnaf_flatten 7 tg128=repeat (inl tt) 128 ->
 strauss_scale_loop_result 129 digits1 digitslam context point=
 @literal_strauss_digits129 Alg.CoreFunSem
  (point,(context,(((h1,t1),(hlam,tlam)),((inl tt,tg1),(inl tt,tg128))))).
Proof.
 intros Digits G1 G128.
 pose (tail:=combine (literal_wnaf5_flatten 7 t1) (literal_wnaf5_flatten 7 tlam)).
 assert (Length:length tail=128%nat).
 { unfold tail;rewrite combine_length,!strauss_wnaf5_flatten_length;reflexivity. }
 rewrite strauss_scale_loop_result_fold,Digits,literal_strauss_digits129_list,G1,G128,strauss_combine_repeats.
 change (fold_left (fun point pair=>@literal_strauss_step Alg.CoreFunSem
  (point,(context,(pair,(inl tt,inl tt))))) tail
  (@literal_strauss_step Alg.CoreFunSem (point,(context,((h1,hlam),(inl tt,inl tt)))))=
 fold_left (fun point ds=>@literal_strauss_step Alg.CoreFunSem (point,(context,ds)))
  (combine tail (repeat (inl tt,inl tt) 128))
  (@literal_strauss_step Alg.CoreFunSem (point,(context,((h1,hlam),(inl tt,inl tt)))))).
 symmetry;rewrite <-Length;apply strauss_scale_fold_absent_generators.
Qed.

Theorem strauss_scale_short_loop_literal129 keep digits1 digitslam
 (context:Ty.tySem literal_strauss_context)
 (h1:Ty.tySem literal_wnaf5_digit) (t1:Ty.tySem (Vector literal_wnaf5_digit 7))
 (hlam:Ty.tySem literal_wnaf5_digit) (tlam:Ty.tySem (Vector literal_wnaf5_digit 7))
 (tg1 tg128:Ty.tySem (Vector C.jet_secp_wnaf_literal.literal_wnaf_digit 7)) :
 (keep<=129)%nat ->
 (forall j,(keep<=j<129)%nat -> digits1 (Z.of_nat j)=inl tt /\ digitslam (Z.of_nat j)=inl tt) ->
 map (fun j=>(digits1 (Z.of_nat j),digitslam (Z.of_nat j))) (rev (seq 0 129))=
  (h1,hlam)::combine (literal_wnaf5_flatten 7 t1) (literal_wnaf5_flatten 7 tlam) ->
 C.jet_secp_wnaf_literal.literal_wnaf_flatten 7 tg1=repeat (inl tt) 128 ->
 C.jet_secp_wnaf_literal.literal_wnaf_flatten 7 tg128=repeat (inl tt) 128 ->
 strauss_scale_loop_result keep digits1 digitslam context (@literal_gej_infinity Alg.CoreFunSem tt)=
 @literal_strauss_digits129 Alg.CoreFunSem
  (@literal_gej_infinity Alg.CoreFunSem tt,(context,(((h1,t1),(hlam,tlam)),((inl tt,tg1),(inl tt,tg128))))).
Proof.
 intros Bound Zeros Digits G1 G128.
 rewrite <-(strauss_scale_remove_leading_zeros 129 keep digits1 digitslam context Bound Zeros).
 apply strauss_scale_loop_literal129;assumption.
Qed.


