(** Original Strauss point stage with all four digit streams. *)
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

Require Import C.jet_secp_strauss_general_iteration C.jet_secp_strauss_general_loop C.jet_secp_generator_pair_general C.jet_secp_generator_globals C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_values C.jet_secp_wnaf_literal_array.


Require Import C.jet_secp_strauss_scale_loop C.jet_secp_negate_literal_contract C.jet_secp_globalz_word_walk C.jet_secp_generator_point_stage C.jet_secp_generator_entry C.jet_secp_generator_final C.jet_secp_strauss_final_literal C.jet_secp_strauss_final_flag
 C.jet_secp_double_var_owned C.jet_secp_gej_infinity_owned C.jet_secp_literal_infinity C.jet_secp_curve_literal C.jet_secp_generator_loop_literal.
Local Opaque literal_fe_multiply literal_gej_infinity.
Lemma strauss_point_stage_closed : closed_stmtb secp_closed_helpers generator_point_stage=true.
Proof. vm_compute;reflexivity. Qed.

Theorem exec_strauss_general_point_stage_flag count e le m br bs bp bd bt bx bz xs ys aux inv bits1 bitslam digits1 digitslam bg1 bg128 bitsg1 bitsg128 digitsg1 digitsg128 :
 (count<=129)%nat -> plain_env e -> NoDup [br;bd;bs;bp;bt;bx;bz;bg1;bg128] ->
 (forall h,generator_table_state h m) ->
 e!_wnaf_ng_1=Some (bg1,tarray tint 129) -> e!_wnaf_ng_128=Some (bg128,tarray tint 129) ->
 e!_secp256k1_ecmult_table_get_ge_storage=None -> e!_secp256k1_gej_add_zinv_var=None ->
 e!(generator_table_id false)=None -> e!(generator_table_id true)=None ->
 0<=bitsg1<=129 -> 0<=bitsg128<=129 ->
 (forall j,0<=j<129 -> wnaf_literal_valid (digitsg1 j)) ->
 (forall j,0<=j<129 -> wnaf_literal_valid (digitsg128 j)) ->
 (forall j,0<=j<bitsg1 -> Mem.load Mint32 m bg1 (4*j)=Some (Vint (Int.repr (wnaf_literal_value (digitsg1 j))))) ->
 (forall j,0<=j<bitsg128 -> Mem.load Mint32 m bg128 (4*j)=Some (Vint (Int.repr (wnaf_literal_value (digitsg128 j))))) ->
 (forall j,0<=j<129 -> bitsg1<=j -> digitsg1 j=inl tt) ->
 (forall j,0<=j<129 -> bitsg128<=j -> digitsg128 j=inl tt) ->
 e!_tmpa=Some (bd,Tstruct __6121 noattr) -> e!_Z=Some (bz,curve_fe_type) ->
 e!_secp256k1_ecmult_table_get_ge=None -> e!_secp256k1_ecmult_table_get_ge_lambda=None ->
 e!_secp256k1_gej_add_ge_var=None -> e!_secp256k1_gej_double_var=None ->
 e!_secp256k1_gej_set_infinity=None -> e!_secp256k1_fe_mul=None ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_no=Some (Vlong Int64.one) -> le!_bits=Some (Vint (Int.repr (Z.of_nat count))) ->
 le!_bits_ng_1=Some (Vint (Int.repr bitsg1)) -> le!_bits_ng_128=Some (Vint (Int.repr bitsg128)) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 0<=bits1<=129 -> 0<=bitslam<=129 ->
 Mem.load Mint32 m bp 1032=Some (Vint (Int.repr bits1)) ->
 Mem.load Mint32 m bp 1036=Some (Vint (Int.repr bitslam)) ->
 (forall j,0<=j<bits1 -> Mem.load Mint32 m bp (4*j)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value (digits1 j))))) ->
 (forall j,0<=j<bitslam -> Mem.load Mint32 m bp (516+4*j)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value (digitslam j))))) ->
 (forall j,0<=j<129 -> bits1<=j -> digits1 j=inl tt) ->
 (forall j,0<=j<129 -> bitslam<=j -> digitslam j=inl tt) ->
 globalz_table_rep m bt xs ys -> globalz_table_bounds xs ys ->
 (forall k,(k<8)%nat -> mul_small_input_bounds (ys k)) ->
 (forall k,(k<8)%nat -> fe_at m bx (40*Z.of_nat k) (words5 (aux k))) ->
 (forall k,(k<8)%nat -> square_input_bounds (aux k)) ->
 (forall k,(k<8)%nat -> rescale_field_output (aux k)=
  @C.jet_secp_beta_spec.literal_fe_multiply_beta Alg.CoreFunSem (rescale_field_output (xs k))) ->
 square_input_bounds inv -> fe_at m bz 0 (words5 inv) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m bd 0 88 Cur Freeable ->
 Mem.range_perm m bt 0 704 Cur Freeable -> Mem.range_perm m bx 0 320 Cur Freeable ->
 Mem.range_perm m bz 0 40 Cur Freeable ->
 exists lef mf ox oy oz,
 Clight2.exec_stmt secp_ge e le m generator_point_stage E0 lef mf Out_normal /\
 lef!_r=Some (Vptr br Ptrofs.zero) /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  (let result:=strauss_general_loop_result count digits1 digitslam digitsg1 digitsg128
    (rescale_field_output inv,globalz_word_vector (globalz_decoded_points xs ys))
    (@literal_gej_infinity Alg.CoreFunSem tt) in
   (fst result,@literal_fe_multiply Alg.CoreFunSem (rescale_field_output inv,snd result))) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
 Mem.range_perm mf bt 0 704 Cur Freeable /\ Mem.range_perm mf bx 0 320 Cur Freeable /\
 Mem.range_perm mf bz 0 40 Cur Freeable /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun b _=>b<>br /\ b<>bd /\ b<>bz) m mf /\
 (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output inv))=false ->
  Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz)))))).
Proof.
 intros Count Plain Separate Tables ArrayG1 ArrayG128 GetStorage AddZinv TableG1 TableG128
  LenG1 LenG128 ValidG1 ValidG128 LoadG1 LoadG128 AbsentG1 AbsentG128 Local ZLocal Get GetLam Add DoubleSymbol InfinitySymbol MulSymbol
  R State No Bits G1 G128 PS PT PX Len1 LenLam Count1 CountLam Load1 LoadLam Absent1 AbsentLam
  Table Bounds Tight Aux AuxBounds AuxLiteral InvBounds Inv FreeR FreeD FreeT FreeX FreeZ.
 pose proof Separate as LoopSeparate.
 assert (Protected:forall b,In b [bd;bs;bp;bt;bx;bz;bg1;bg128] -> b<>br).
 { inversion Separate as [|? ? NotR Tail];subst.
   intros b Member Eq;subst b;apply NotR;exact Member. }
 assert (ZR:bz<>br) by (apply Protected;clear;cbn [In];tauto).
 assert (ZD:bz<>bd).
 { inversion Separate as [|? ? NotR Tail];subst;inversion Tail as [|? ? NotD Tail2];subst.
   intro Eq;subst bz;apply NotD;clear;cbn [In];tauto. }
 destruct (eval_gej_infinity_initializer_owned m br 0 ltac:(clear;lia) ltac:(exists 0;reflexivity)
  ltac:(change (128<=18446744073709551615);clear;lia)
  ltac:(intros pos Range;eapply Mem.perm_implies;[apply FreeR;exact Range|constructor]))
  as (mi & Initialize & XI & YI & ZI & FlagI & LoadsI & PermI & ValidI).
 assert (FrameI:lframe (fun b _=>b<>br) m mi).
 { split.
   - intros chunk b ofs Valid Outside;apply LoadsI;left;apply (Outside ofs);pose proof (size_chunk_pos chunk);lia.
   - split;[intros b pos k p Valid Outside Perm;apply (proj2 (PermI _ _ _ _));exact Perm|exact ValidI]. }
 assert (Saved:forall chunk b ofs value,b<>br -> Mem.load chunk m b ofs=Some value ->
  Mem.load chunk mi b ofs=Some value).
 { intros chunk b ofs value Other Load;rewrite (proj1 FrameI chunk b ofs);[exact Load| |intros;exact Other].
   eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
    [eapply Mem.load_valid_access;exact Load|apply perm_any_N]. }
 assert (PSI:Mem.load Mptr mi bs 16=Some (Vptr bp Ptrofs.zero)).
 { eapply Saved;[apply Protected;clear;cbn [In];tauto|exact PS]. }
 assert (PTI:Mem.load Mptr mi bs 8=Some (Vptr bt Ptrofs.zero)).
 { eapply Saved;[apply Protected;clear;cbn [In];tauto|exact PT]. }
 assert (PXI:Mem.load Mptr mi bs 0=Some (Vptr bx Ptrofs.zero)).
 { eapply Saved;[apply Protected;clear;cbn [In];tauto|exact PX]. }
 assert (C1I:Mem.load Mint32 mi bp 1032=Some (Vint (Int.repr bits1))).
 { eapply Saved;[apply Protected;clear;cbn [In];tauto|exact Count1]. }
 assert (CLI:Mem.load Mint32 mi bp 1036=Some (Vint (Int.repr bitslam))).
 { eapply Saved;[apply Protected;clear;cbn [In];tauto|exact CountLam]. }
 assert (L1I:forall j,0<=j<bits1 -> Mem.load Mint32 mi bp (4*j)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value (digits1 j))))).
 { intros j J;eapply Saved;[apply Protected;clear;cbn [In];tauto|apply Load1;exact J]. }
 assert (LLI:forall j,0<=j<bitslam -> Mem.load Mint32 mi bp (516+4*j)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value (digitslam j))))).
 { intros j J;eapply Saved;[apply Protected;clear;cbn [In];tauto|apply LoadLam;exact J]. }
 assert (LG1I:forall j,0<=j<bitsg1 -> Mem.load Mint32 mi bg1 (4*j)=Some (Vint (Int.repr (wnaf_literal_value (digitsg1 j))))).
 { intros j J;eapply Saved;[apply Protected;clear;cbn [In];tauto|apply LoadG1;exact J]. }
 assert (LG128I:forall j,0<=j<bitsg128 -> Mem.load Mint32 mi bg128 (4*j)=Some (Vint (Int.repr (wnaf_literal_value (digitsg128 j))))).
 { intros j J;eapply Saved;[apply Protected;clear;cbn [In];tauto|apply LoadG128;exact J]. }
 assert (InitializeClosed:closed_stmtb secp_closed_helpers (fn_body f_secp256k1_gej_set_infinity)=true)
  by (vm_compute;reflexivity).
 assert (ReadI:readonly_preserved m mi) by
  (eapply secp_closed_function_preserved;[exact InitializeClosed|reflexivity|exact Initialize]).
 assert (TablesI:forall h,generator_table_state h mi) by
  (eapply generator_tables_readonly;[exact Tables|exact ReadI]).
 assert (TableI:globalz_table_rep mi bt xs ys).
 { intros k K;destruct (Table k K) as (TX & TY & TF);split.
   - eapply field_at_lframe;[exact TX|exact FrameI|intros;apply Protected;clear;cbn [In];tauto].
   - split.
     + eapply field_at_lframe;[exact TY|exact FrameI|intros;apply Protected;clear;cbn [In];tauto].
     + eapply Saved;[apply Protected;clear;cbn [In];tauto|exact TF]. }
 assert (AuxI:forall k,(k<8)%nat -> fe_at mi bx (40*Z.of_nat k) (words5 (aux k))).
 { intros k K;eapply field_at_lframe;[apply Aux;exact K|exact FrameI|intros;apply Protected;clear;cbn [In];tauto]. }
 assert (InvI:fe_at mi bz 0 (words5 inv)) by (eapply field_at_lframe;[exact Inv|exact FrameI|intros;exact ZR]).
 pose (li:=PTree.set _i (Vint (Int.repr (Z.of_nat count-1))) le).
 assert (RL:li!_r=Some (Vptr br Ptrofs.zero)) by (unfold li;rewrite PTree.gso by discriminate;exact R).
 assert (SL:li!_state=Some (Vptr bs Ptrofs.zero)) by (unfold li;rewrite PTree.gso by discriminate;exact State).
 assert (NL:li!_no=Some (Vlong Int64.one)) by (unfold li;rewrite PTree.gso by discriminate;exact No).
 assert (G1L:li!_bits_ng_1=Some (Vint (Int.repr bitsg1))) by (unfold li;rewrite PTree.gso by discriminate;exact G1).
 assert (G128L:li!_bits_ng_128=Some (Vint (Int.repr bitsg128))) by (unfold li;rewrite PTree.gso by discriminate;exact G128).
 assert (Index:li!_i=Some (Vint (Int.repr (Z.of_nat count-1)))) by (unfold li;apply PTree.gss).
 assert (ZeroOut:rescale_field_output (fun _ : nat=>Int64.zero)=@literal_fe_zero256 Alg.CoreFunSem tt)
  by exact zero_field_writer_literal_output.
 assert (ZeroTest:Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (@literal_fe_zero256 Alg.CoreFunSem tt))=true).
 { rewrite literal_curve_zero_numeric;unfold literal_fe_zero256;rewrite Word.zero_correct;reflexivity. }
 assert (FlagReady:Mem.load Mint32 mi br 120=Some (Vint
  (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (@literal_fe_zero256 Alg.CoreFunSem tt)))))).
 { rewrite ZeroTest;exact FlagI. }
 assert (Repr:((rescale_field_output (fun _ : nat=>Int64.zero),rescale_field_output (fun _ : nat=>Int64.zero)),
  rescale_field_output (fun _ : nat=>Int64.zero))=
  ((@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt),@literal_fe_zero256 Alg.CoreFunSem tt)).
 { rewrite ZeroOut;reflexivity. }
 assert (Scale:radix_value inv mod feP=@toZ (WordToZ 8) (rescale_field_output inv) mod feP).
 { rewrite rescale_field_output_value,field_prime_matches_normalizer,Z.mod_mod by (unfold feP,feR;lia);reflexivity. }
 destruct (exec_strauss_general_loop e br bs bp bd bt bx bz bg1 bg128 inv xs ys aux (rescale_field_output inv)
  bits1 bitslam bitsg1 bitsg128 digits1 digitslam digitsg1 digitsg128
  Len1 LenLam LenG1 LenG128 ValidG1 ValidG128 LoopSeparate Plain
  ArrayG1 ArrayG128 ZLocal GetStorage AddZinv TableG1 TableG128 InvBounds Scale AbsentG1 AbsentG128
  Local Get GetLam Add DoubleSymbol Bounds Tight AuxBounds AuxLiteral Absent1 AbsentLam count Count li mi
  (fun _ : nat=>Int64.zero) (fun _ : nat=>Int64.zero) (fun _ : nat=>Int64.zero)
  (@literal_fe_zero256 Alg.CoreFunSem tt) (@literal_fe_zero256 Alg.CoreFunSem tt) (@literal_fe_zero256 Alg.CoreFunSem tt)
  RL SL Index NL G1L G128L PSI PTI PXI C1I CLI L1I LLI LG1I LG128I TablesI InvI
  ltac:(intros pos P;apply (proj2 (PermI _ _ _ _)),FreeZ;exact P) TableI AuxI
  square_zero_bounds square_zero_bounds square_zero_bounds Repr XI YI ZI FlagReady
  ltac:(intros pos P;apply (proj2 (PermI _ _ _ _)),FreeR;exact P)
  ltac:(intros pos P;apply (proj2 (PermI _ _ _ _)),FreeD;exact P)
  ltac:(intros pos P;apply (proj2 (PermI _ _ _ _)),FreeT;exact P)
  ltac:(intros pos P;apply (proj2 (PermI _ _ _ _)),FreeX;exact P))
  as (ll & ml & ox & oy & lz & Loop & End & XL & YL & ZL & FlagL & BXL & BYL & BZL & LiteralL &
   FreeRL & FreeDL & FreeTL & FreeXL & InvL & FreeZL & TablesL & KeepL & ReadL & FrameL & OtherL).
 assert (RLL:ll!_r=Some (Vptr br Ptrofs.zero)).
 { rewrite OtherL by (clear;cbn [In];intuition discriminate);exact RL. }
 destruct (exec_strauss_final_literal ox oy lz inv e ll ml br bz RLL ZLocal MulSymbol
  ltac:(congruence) BXL BYL BZL InvBounds FlagL XL YL ZL InvL FreeRL FreeZL)
  as (mf & oz & Final & XF & YF & ZF & FlagF & InvF & FreeRF & FreeZF & BZF & Product & FrameF).
 pose (lf:=PTree.set _t'16 (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output lz))))) ll).
 assert (Exec:Clight2.exec_stmt secp_ge e le m generator_point_stage E0 lf mf Out_normal).
 { rewrite generator_point_stage_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mi).
   - unfold generator_infinity_statement;eapply exec_curve_call with (vargs:=[Vptr br Ptrofs.zero]) (v:=Vundef).
     + unfold secp_pure;repeat first [left;reflexivity|right].
     + exact InfinitySymbol.
     + eapply eval_Econs;[apply eval_Etempvar;exact R|reflexivity|constructor].
     + exact Initialize.
   - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=ll) (m1:=ml);[|exact Final].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=li) (m1:=mi);[|exact Loop].
     unfold generator_start_index_statement;apply exec_Sset;eapply eval_Ebinop;
      [apply eval_Etempvar;exact Bits|constructor|].
     change (Some (Vint (Int.sub (Int.repr (Z.of_nat count)) Int.one))=
      Some (Vint (Int.repr (Z.of_nat count-1)))).
     change Int.one with (Int.repr 1);rewrite Int.sub_signed,!Int.signed_repr by
      (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia);reflexivity. }
 assert (Keep:keeps_permissions m mf).
 { eapply (proj1 (internal_exec_keeps_permissions _ _ secp_closed_helpers_ok));[exact Exec|exact Plain|exact strauss_point_stage_closed]. }
 assert (Read:readonly_preserved m mf).
 { eapply secp_closed_stmt_preserved;[exact Exec|exact Plain|exact strauss_point_stage_closed]. }
 assert (Literal:((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  (let result:=strauss_general_loop_result count digits1 digitslam digitsg1 digitsg128
    (rescale_field_output inv,globalz_word_vector (globalz_decoded_points xs ys))
    (@literal_gej_infinity Alg.CoreFunSem tt) in
   (fst result,@literal_fe_multiply Alg.CoreFunSem (rescale_field_output inv,snd result)))).
 { apply (f_equal (fun p:Ty.tySem literal_table_gej=>
    (fst p,@literal_fe_multiply Alg.CoreFunSem (rescale_field_output inv,snd p)))) in LiteralL.
   rewrite Product,globalz_multiply_commutes.
   exact LiteralL. }
 assert (Frame:lframe (fun b _=>b<>br /\ b<>bd /\ b<>bz) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameI|intros b pos (Rr & Dd & Zz) _;exact Rr].
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FrameL|intros b pos (Rr & Dd & Zz) _;repeat split;assumption].
     + eapply lframe_implies;[exact FrameF|intros b pos (Rr & Dd & Zz) _;split;assumption]. }
 exists lf,mf,ox,oy,oz;split;[exact Exec|];split.
 - unfold lf;rewrite PTree.gso by discriminate;exact RLL.
 - split;[exact XF|];split;[exact YF|];split;[exact ZF|];
   split;[exact BXL|];split;[exact BYL|];split;[exact BZF|];split;[exact Literal|];
   split;[exact FreeRF|];split;[intros pos P;apply Keep,FreeD;exact P|];
   split;[intros pos P;apply Keep,FreeT;exact P|];split;[intros pos P;apply Keep,FreeX;exact P|];
   split;[exact FreeZF|];split;[exact Keep|];split;[exact Read|];split;[exact Frame|].
   intro Nonzero;rewrite Product,literal_zero_product_nonzero_factor by exact Nonzero;exact FlagF.
Qed.


Theorem exec_strauss_general_point_stage count e le m br bs bp bd bt bx bz xs ys aux inv bits1 bitslam digits1 digitslam bg1 bg128 bitsg1 bitsg128 digitsg1 digitsg128 :
 (count<=129)%nat -> plain_env e -> NoDup [br;bd;bs;bp;bt;bx;bz;bg1;bg128] ->
 (forall h,generator_table_state h m) ->
 e!_wnaf_ng_1=Some (bg1,tarray tint 129) -> e!_wnaf_ng_128=Some (bg128,tarray tint 129) ->
 e!_secp256k1_ecmult_table_get_ge_storage=None -> e!_secp256k1_gej_add_zinv_var=None ->
 e!(generator_table_id false)=None -> e!(generator_table_id true)=None ->
 0<=bitsg1<=129 -> 0<=bitsg128<=129 ->
 (forall j,0<=j<129 -> wnaf_literal_valid (digitsg1 j)) ->
 (forall j,0<=j<129 -> wnaf_literal_valid (digitsg128 j)) ->
 (forall j,0<=j<bitsg1 -> Mem.load Mint32 m bg1 (4*j)=Some (Vint (Int.repr (wnaf_literal_value (digitsg1 j))))) ->
 (forall j,0<=j<bitsg128 -> Mem.load Mint32 m bg128 (4*j)=Some (Vint (Int.repr (wnaf_literal_value (digitsg128 j))))) ->
 (forall j,0<=j<129 -> bitsg1<=j -> digitsg1 j=inl tt) ->
 (forall j,0<=j<129 -> bitsg128<=j -> digitsg128 j=inl tt) ->
 e!_tmpa=Some (bd,Tstruct __6121 noattr) -> e!_Z=Some (bz,curve_fe_type) ->
 e!_secp256k1_ecmult_table_get_ge=None -> e!_secp256k1_ecmult_table_get_ge_lambda=None ->
 e!_secp256k1_gej_add_ge_var=None -> e!_secp256k1_gej_double_var=None ->
 e!_secp256k1_gej_set_infinity=None -> e!_secp256k1_fe_mul=None ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_no=Some (Vlong Int64.one) -> le!_bits=Some (Vint (Int.repr (Z.of_nat count))) ->
 le!_bits_ng_1=Some (Vint (Int.repr bitsg1)) -> le!_bits_ng_128=Some (Vint (Int.repr bitsg128)) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 0<=bits1<=129 -> 0<=bitslam<=129 ->
 Mem.load Mint32 m bp 1032=Some (Vint (Int.repr bits1)) ->
 Mem.load Mint32 m bp 1036=Some (Vint (Int.repr bitslam)) ->
 (forall j,0<=j<bits1 -> Mem.load Mint32 m bp (4*j)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value (digits1 j))))) ->
 (forall j,0<=j<bitslam -> Mem.load Mint32 m bp (516+4*j)=Some (Vint (Int.repr (C.jet_secp_wnaf5_signed_array.wnaf5_literal_value (digitslam j))))) ->
 (forall j,0<=j<129 -> bits1<=j -> digits1 j=inl tt) ->
 (forall j,0<=j<129 -> bitslam<=j -> digitslam j=inl tt) ->
 globalz_table_rep m bt xs ys -> globalz_table_bounds xs ys ->
 (forall k,(k<8)%nat -> mul_small_input_bounds (ys k)) ->
 (forall k,(k<8)%nat -> fe_at m bx (40*Z.of_nat k) (words5 (aux k))) ->
 (forall k,(k<8)%nat -> square_input_bounds (aux k)) ->
 (forall k,(k<8)%nat -> rescale_field_output (aux k)=
  @C.jet_secp_beta_spec.literal_fe_multiply_beta Alg.CoreFunSem (rescale_field_output (xs k))) ->
 square_input_bounds inv -> fe_at m bz 0 (words5 inv) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m bd 0 88 Cur Freeable ->
 Mem.range_perm m bt 0 704 Cur Freeable -> Mem.range_perm m bx 0 320 Cur Freeable ->
 Mem.range_perm m bz 0 40 Cur Freeable ->
 exists lef mf ox oy oz,
 Clight2.exec_stmt secp_ge e le m generator_point_stage E0 lef mf Out_normal /\
 lef!_r=Some (Vptr br Ptrofs.zero) /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  (let result:=strauss_general_loop_result count digits1 digitslam digitsg1 digitsg128
    (rescale_field_output inv,globalz_word_vector (globalz_decoded_points xs ys))
    (@literal_gej_infinity Alg.CoreFunSem tt) in
   (fst result,@literal_fe_multiply Alg.CoreFunSem (rescale_field_output inv,snd result))) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
 Mem.range_perm mf bt 0 704 Cur Freeable /\ Mem.range_perm mf bx 0 320 Cur Freeable /\
 Mem.range_perm mf bz 0 40 Cur Freeable /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun b _=>b<>br /\ b<>bd /\ b<>bz) m mf.
Proof.
 intros Count Plain Separate Tables ArrayG1 ArrayG128 GetStorage AddZinv TableG1 TableG128
  LenG1 LenG128 ValidG1 ValidG128 LoadG1 LoadG128 AbsentG1 AbsentG128 Local ZLocal Get GetLam Add DoubleSymbol InfinitySymbol MulSymbol
  R State No Bits G1 G128 PS PT PX Len1 LenLam Count1 CountLam Load1 LoadLam Absent1 AbsentLam
  Table Bounds Tight Aux AuxBounds AuxLiteral InvBounds Inv FreeR FreeD FreeT FreeX FreeZ.
 destruct (exec_strauss_general_point_stage_flag count e le m br bs bp bd bt bx bz xs ys aux inv bits1 bitslam digits1 digitslam bg1 bg128 bitsg1 bitsg128 digitsg1 digitsg128
  Count Plain Separate Tables ArrayG1 ArrayG128 GetStorage AddZinv TableG1 TableG128 LenG1 LenG128 ValidG1 ValidG128 LoadG1 LoadG128 AbsentG1 AbsentG128 Local ZLocal Get GetLam Add DoubleSymbol InfinitySymbol MulSymbol R State No Bits G1 G128 PS PT PX Len1 LenLam Count1 CountLam Load1 LoadLam Absent1 AbsentLam Table Bounds Tight Aux AuxBounds AuxLiteral InvBounds Inv FreeR FreeD FreeT FreeX FreeZ)
  as (lef & mf & ox & oy & oz & Exec & ROut & X & Y & Z & BX & BY & BZ & Literal &
   FR & FD & FT & FX & FZ & Keep & Read & Frame & Conditional).
 exists lef,mf,ox,oy,oz;repeat first [assumption|split].
Qed.
