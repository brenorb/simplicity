(** One complete original global-Z loop iteration, deriving temporary storage
    and helper premises from the actual factor branch, decrement and copies. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_globalz_factor_call C.jet_secp_globalz_prepare C.jet_secp_globalz_indexed_call
 C.jet_secp_curve_statements C.jet_secp_ge_zinv_arithmetic C.jet_secp_ge_zinv_indexed_function
 C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_rescale_literal
 C.jet_secp_field_read_preservation C.jet_secp_statement_prefix C.jet_secp_slice_permissions
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output globalz_factor_words ge_zinv_x_words ge_zinv_y_words.

Definition globalz_iteration_temps le i := PTree.set _i (Vlong (Int64.repr (i-1))) le.
Definition globalz_iteration_frame (br bt bf bz:block) i (bx:block) pos :=
 bx<>bt /\ bx<>bf /\ (bx<>br \/ pos<88*(i-1) \/ 88*(i-1)+84<=pos) /\
 (bx<>bz \/ pos<40*i \/ 40*i+40<=pos).

Lemma exec_globalz_decrement e le m i : 1<=i<8 -> le!_i=Some (Vlong (Int64.repr i)) ->
 Clight2.exec_stmt secp_ge e le m globalz_decrement E0 (globalz_iteration_temps le i) m Out_normal.
Proof.
 intros Index IndexTemp;unfold globalz_decrement,globalz_iteration_temps;apply exec_Sset.
 eapply eval_Ebinop;[apply eval_Etempvar;exact IndexTemp|constructor|].
 change (Some (Vlong (Int64.sub (Int64.repr i) Int64.one))=
  Some (Vlong (Int64.repr (i-1)))).
 unfold Int64.sub;rewrite Int64.unsigned_repr by
  (change Int64.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.

Theorem exec_globalz_iteration e le x y zs ratio m br bt bf bz i :
 1<=i<8 -> NoDup [br;bt;bf;bz] ->
 e!_tmpa=Some (bt,Tstruct __6123 noattr) -> e!_zs=Some (bf,curve_fe_type) ->
 e!_secp256k1_fe_mul=None -> e!_secp256k1_ge_set_gej_zinv=None ->
 le!_a=Some (Vptr br Ptrofs.zero) -> le!_zr=Some (Vptr bz Ptrofs.zero) ->
 le!_i=Some (Vlong (Int64.repr i)) -> le!_len=Some (Vlong (Int64.repr 8)) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds zs -> square_input_bounds ratio ->
 fe_at m br (88*(i-1)+0) (words5 x) -> fe_at m br (88*(i-1)+40) (words5 y) ->
 fe_at m bf 0 (words5 zs) -> fe_at m bz (40*i) (words5 ratio) ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m bt 0 128 Cur Freeable ->
 Mem.range_perm m bf 0 40 Cur Freeable -> Mem.range_perm m bz 0 320 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m globalz_indexed_loop_body E0 (globalz_iteration_temps le i) mf Out_normal /\
 fe_at mf br (88*(i-1)+0) (words5 (ge_zinv_x_words x (globalz_factor_words i zs ratio))) /\
 fe_at mf br (88*(i-1)+40) (words5 (ge_zinv_y_words y (globalz_factor_words i zs ratio))) /\
 Mem.load Mint32 mf br (88*(i-1)+80)=Some (Vint Int.zero) /\
 (rescale_field_output (ge_zinv_x_words x (globalz_factor_words i zs ratio)),
  rescale_field_output (ge_zinv_y_words y (globalz_factor_words i zs ratio)))=
  @literal_gej_zinv Alg.CoreFunSem ((rescale_field_output x,rescale_field_output y),
    rescale_field_output (globalz_factor_words i zs ratio)) /\
 fe_at mf bt 0 (words5 x) /\ fe_at mf bt 40 (words5 y) /\
 Mem.load Mint32 mf bt 120=Some (Vint Int.zero) /\
 fe_at mf bf 0 (words5 (globalz_factor_words i zs ratio)) /\ fe_at mf bz (40*i) (words5 ratio) /\
 square_input_bounds (ge_zinv_x_words x (globalz_factor_words i zs ratio)) /\
 square_input_bounds (ge_zinv_y_words y (globalz_factor_words i zs ratio)) /\
 square_input_bounds (globalz_factor_words i zs ratio) /\
 Mem.range_perm mf br 0 704 Cur Freeable /\ Mem.range_perm mf bt 0 128 Cur Freeable /\
 Mem.range_perm mf bf 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 320 Cur Freeable /\
 keeps_permissions m mf /\ lframe (globalz_iteration_frame br bt bf bz i) m mf /\ readonly_preserved m mf.
Proof.
 intros Index Distinct Tmp Factor MulGlobal ScaleGlobal A Ratios IndexTemp Length BX BY BZ BR X Y Z R
  FreeA FreeT FreeZ FreeR.
 inversion Distinct as [|? ? NR Rest];subst;inversion Rest as [|? ? NT Rest2];subst;
  inversion Rest2 as [|? ? NF Rest3];subst.
 cbn [In] in NR,NT,NF.
 assert (AT:br<>bt) by (intuition congruence).
 assert (AF:br<>bf) by (intuition congruence).
 assert (AR:br<>bz) by (intuition congruence).
 assert (TF:bt<>bf) by (intuition congruence).
 assert (TR:bt<>bz) by (intuition congruence).
 assert (FR:bf<>bz) by (intuition congruence).
 destruct (exec_globalz_factor_call e le zs ratio m bf bz i Index FR Factor MulGlobal Ratios IndexTemp Length
   BZ BR Z R FreeZ FreeR)
  as (m1 & FactorRun & Z1 & R1 & BZ1 & FactorLiteral & FreeZ1 & FreeR1 & Keep1 & Frame1 & Readonly1).
 assert (X1:fe_at m1 br (88*(i-1)+0) (words5 x)).
 { eapply field_at_lframe;[exact X|exact Frame1|];intros;split;left;assumption. }
 assert (Y1:fe_at m1 br (88*(i-1)+40) (words5 y)).
 { eapply field_at_lframe;[exact Y|exact Frame1|];intros;split;left;assumption. }
 set (le1:=globalz_iteration_temps le i).
 assert (A1:le1!_a=Some (Vptr br Ptrofs.zero)) by
  (unfold le1,globalz_iteration_temps;rewrite PTree.gso by discriminate;exact A).
 assert (Index1:le1!_i=Some (Vlong (Int64.repr (i-1)))) by
  (unfold le1,globalz_iteration_temps;apply PTree.gss).
 assert (FreeT1:Mem.range_perm m1 bt 0 128 Cur Freeable) by
  (eapply keeps_range_permissions;[exact Keep1|exact FreeT]).
 destruct (exec_globalz_prepare e le1 x y m1 br bt (i-1) ltac:(lia) AT Tmp A1 Index1 X1 Y1 FreeT1)
  as (m2 & Prepare & X2 & Y2 & Flag2 & Perm2 & Frame2 & Readonly2).
 assert (Z2:fe_at m2 bf 0 (words5 (globalz_factor_words i zs ratio))).
 { eapply field_at_lframe;[exact Z1|exact Frame2|];intros;left;congruence. }
 assert (R2:fe_at m2 bz (40*i) (words5 ratio)).
 { eapply field_at_lframe;[exact R1|exact Frame2|];intros;left;congruence. }
 assert (FreeA2:Mem.range_perm m2 br 0 704 Cur Freeable).
 { intros pos Range;apply (proj2 (Perm2 br pos Cur Freeable));apply Keep1;apply FreeA;exact Range. }
 assert (FreeT2:Mem.range_perm m2 bt 0 128 Cur Freeable).
 { intros pos Range;apply (proj2 (Perm2 bt pos Cur Freeable));apply FreeT1;exact Range. }
 assert (FreeZ2:Mem.range_perm m2 bf 0 40 Cur Freeable).
 { intros pos Range;apply (proj2 (Perm2 bf pos Cur Freeable));apply FreeZ1;exact Range. }
 destruct (exec_globalz_indexed_scale e le1 x y (globalz_factor_words i zs ratio) m2 br bt bf (i-1)
  ltac:(lia) AT AF TF Tmp Factor ScaleGlobal A1 Index1 BX BY BZ1 Flag2 X2 Y2 Z2 FreeA2 FreeT2 FreeZ2)
  as (mf & Scale & XO & YO & Flag & Literal & FlagT & XT & YT & ZF & FreeAF & FreeTF & FreeZF & BXO & BYO
      & Keep3 & Frame3 & Readonly3).
 assert (Keep:keeps_permissions m mf).
 { intros b pos k p Perm;apply Keep3;apply (proj2 (Perm2 b pos k p));apply Keep1;exact Perm. }
 assert (RF:fe_at mf bz (40*i) (words5 ratio)).
 { eapply field_at_lframe;[exact R2|exact Frame3|];intros;unfold ge_zinv_indexed_frame;
    split;[congruence|];split;left;congruence. }
 exists mf;split.
 - rewrite globalz_prepare_source;change (Clight2.exec_stmt secp_ge e le m
    (Ssequence globalz_factor_branch (Ssequence globalz_decrement
      (statement_sequence globalz_prepare_statements globalz_indexed_scale_statement))) E0 le1 mf Out_normal).
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m1);[exact FactorRun|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le1) (m1:=m1).
   + apply exec_globalz_decrement;assumption.
   + eapply exec_statement_prefix_then_last;[exact Prepare|exact Scale].
 - split;[exact XO|];split;[exact YO|];split;[exact Flag|];split;[exact Literal|];
   split;[exact XT|];split;[exact YT|];split;[exact FlagT|];split;[exact ZF|];split;[exact RF|];
   split;[exact BXO|];split;[exact BYO|];split;[exact BZ1|];split;[exact FreeAF|];
   split;[exact FreeTF|];split;[exact FreeZF|];split.
   + eapply keeps_range_permissions;[exact Keep|exact FreeR].
   + split;[exact Keep|];split.
     * eapply lframe_trans.
       -- eapply lframe_implies;[exact Frame1|];intros b pos (NotT & NotF & Entry & Ratio) Valid;
           split;[left;exact NotF|exact Ratio].
       -- eapply lframe_trans.
          ++ eapply lframe_implies;[exact Frame2|];intros b pos (NotT & NotF & Entry & Ratio) Valid;
              left;exact NotT.
          ++ eapply lframe_implies;[exact Frame3|];intros b pos (NotT & NotF & Entry & Ratio) Valid;
              split;[exact NotF|];split;[exact Entry|left;exact NotT].
     * eapply preserved_trans;[exact Readonly1|];eapply preserved_trans;[exact Readonly2|exact Readonly3].
Qed.
