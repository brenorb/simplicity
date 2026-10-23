(** Original Strauss point stage: actual infinity initialization, descending
    loop and final correction, against the literal generate digit program.
    The caller must still establish the represented wNAF arrays and Z=1. *)
From Coq Require Import ZArith Lia List.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_local_regions C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_field_read_preservation C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_double_var_owned C.jet_secp_rescale_literal C.jet_secp_canonical_zero
 C.jet_secp_literal_infinity C.jet_secp_curve_literal C.jet_secp_gej_infinity_owned
 C.jet_secp_generator_globals C.jet_secp_generator_program C.jet_secp_generator_loop
 C.jet_secp_generator_loop_literal C.jet_secp_generator_loop_control C.jet_secp_statement_prefix
 C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_array C.jet_secp_wnaf_loop.
Require Import C.jet_secp_generator_digit_index C.jet_secp_generator_final.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output literal_generator_digits129 literal_gej_infinity literal_wnaf15.

Definition generator_point_stage := statement_sequence
 (skipn 9 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf))))
 (snd (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf))).
Definition generator_infinity_statement := curve_call _secp256k1_gej_set_infinity f_secp256k1_gej_set_infinity None
 [Etempvar _r (tptr (Tstruct __6123 noattr))].
Definition generator_start_index_statement := Sset _i
 (Ebinop Osub (Etempvar _bits tint) (Econst_int Int.one tint) tint).
Lemma generator_point_stage_source : generator_point_stage=Ssequence generator_infinity_statement
 (Ssequence (Ssequence generator_start_index_statement generator_descending_loop) generator_final_statement).
Proof. reflexivity. Qed.

Lemma generator_wnaf_short_result count word1 word128 : (count<=129)%nat ->
 (forall j,(count<=j<129)%nat -> wnaf_literal_digit_at word1 (Z.of_nat j)=inl tt /\
   wnaf_literal_digit_at word128 (Z.of_nat j)=inl tt) ->
 generator_loop_result count (wnaf_literal_digit_at word1) (wnaf_literal_digit_at word128)
   (@literal_gej_infinity Alg.CoreFunSem tt)=
 @literal_generator_digits129 Alg.CoreFunSem (@literal_gej_infinity Alg.CoreFunSem tt,
   (@literal_wnaf15 Alg.CoreFunSem (inl tt,word1),@literal_wnaf15 Alg.CoreFunSem (inl tt,word128))).
Proof.
 intros Count Zeros;pose proof (wnaf_literal_digit_at_vectors word1 word128) as Digits.
 destruct (@literal_wnaf15 Alg.CoreFunSem (inl tt,word1)) as [h1 t1],
   (@literal_wnaf15 Alg.CoreFunSem (inl tt,word128)) as [h128 t128].
 exact (generator_short_loop_literal129 count (wnaf_literal_digit_at word1) (wnaf_literal_digit_at word128)
   h1 t1 h128 t128 Count Zeros Digits).
Qed.

Theorem exec_generator_point_stage e le m bp ba bb b1 b128 inv word1 word128 digits1 digits128 last1 last128 :
 NoDup [bp;ba;bb;b1;b128] -> (forall h,generator_table_state h m) ->
 le!_r=Some (Vptr bp Ptrofs.zero) -> le!_no=Some (Vlong Int64.zero) ->
 le!_bits=Some (Vint (Int.repr (Z.max (last1+1) (last128+1)))) ->
 le!_bits_ng_1=Some (Vint (Int.repr (last1+1))) -> le!_bits_ng_128=Some (Vint (Int.repr (last128+1))) ->
 e!_wnaf_ng_1=Some (b1,tarray tint 129) -> e!_wnaf_ng_128=Some (b128,tarray tint 129) ->
 e!_tmpa=Some (ba,curve_ge_type) -> e!_Z=Some (bb,curve_fe_type) ->
 e!_secp256k1_ecmult_table_get_ge_storage=None -> e!_secp256k1_gej_add_zinv_var=None ->
 e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None -> e!_secp256k1_fe_mul=None ->
 e!(generator_table_id false)=None -> e!(generator_table_id true)=None ->
 wnaf_array_state m b1 0 129 15 1 129 last1 digits1 ->
 wnaf_array_state m b128 0 129 15 1 129 last128 digits128 ->
 map wnaf_literal_value (literal_wnaf15_digits (inl tt,word1))=
   rev (map (fun j=>digits1 (Z.of_nat j)) (seq 0 129)) ->
 map wnaf_literal_value (literal_wnaf15_digits (inl tt,word128))=
   rev (map (fun j=>digits128 (Z.of_nat j)) (seq 0 129)) ->
 square_input_bounds inv -> radix_value inv mod feP=1 -> fe_at m bb 0 (words5 inv) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> exists lef mf ox oy oz,
 Clight2.exec_stmt secp_ge e le m generator_point_stage E0 lef mf Out_normal /\
 lef!_r=Some (Vptr bp Ptrofs.zero) /\
 fe_at mf bp 0 (words5 ox) /\ fe_at mf bp 40 (words5 oy) /\ fe_at mf bp 80 (words5 oz) /\
 Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 fe_at mf bb 0 (words5 inv) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bb 0 40 Cur Freeable /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
 @literal_generator_digits129 Alg.CoreFunSem (@literal_gej_infinity Alg.CoreFunSem tt,
   (@literal_wnaf15 Alg.CoreFunSem (inl tt,word1),@literal_wnaf15 Alg.CoreFunSem (inl tt,word128))) /\
 lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf.
Proof.
 intros Sep Tables PR No Bits L1 L128 E1 E128 EA EZ EL EAdd ED EInf EM ET1 ET128
   Array1 Array128 Digits1 Digits128 BI One Inv PF AF IF.
 pose proof Sep as Sep0;repeat rewrite NoDup_cons_iff in Sep0;cbn [In] in Sep0.
 assert (BPB : bp<>bb) by intuition congruence.
 assert (BAP : ba<>bp) by intuition congruence.
 assert (BAB : ba<>bb) by intuition congruence.
 assert (B1P : b1<>bp) by intuition congruence.
 assert (B128P : b128<>bp) by intuition congruence.
 destruct (eval_gej_infinity_initializer_owned m bp 0 ltac:(lia) ltac:(exists 0;reflexivity)
   ltac:(change (128<=18446744073709551615);lia) (freeable_range_writable _ _ _ _ PF))
   as (mi & Initialize & XI & YI & ZI & FlagI & LoadsI & PermI & ValidI).
 assert (FrameI : lframe (fun b _=>b<>bp) m mi).
 { split.
   - intros chunk b ofs Valid Outside;apply LoadsI;left;apply (Outside ofs);pose proof (size_chunk_pos chunk);lia.
   - split;[intros b pos k p Valid Outside Perm;apply (proj2 (PermI b pos k p));exact Perm|exact ValidI]. }
 assert (InvI : fe_at mi bb 0 (words5 inv)).
 { eapply field_at_lframe;[exact Inv|exact FrameI|];intros;congruence. }
 assert (PFI : Mem.range_perm mi bp 0 128 Cur Freeable) by
   (intros pos Bound;apply (proj2 (PermI bp pos Cur Freeable));apply PF;exact Bound).
 assert (AFI : Mem.range_perm mi ba 0 88 Cur Freeable) by
   (intros pos Bound;apply (proj2 (PermI ba pos Cur Freeable));apply AF;exact Bound).
 assert (IFI : Mem.range_perm mi bb 0 40 Cur Freeable) by
   (intros pos Bound;apply (proj2 (PermI bb pos Cur Freeable));apply IF;exact Bound).
 assert (TablesI : forall h,generator_table_state h mi).
 { intro h;pose proof (Tables h) as [Table Readonly].
   assert (Outside : generator_table_block h<>bp).
   { intro Equal;rewrite Equal in Readonly.
     destruct (proj1 (Readonly 0 Cur Freeable) (PF 0 ltac:(lia))) as [_ Order];inversion Order. }
   split.
   - exact (generator_table_rep_lframe h m mi _ Table FrameI ltac:(intros;exact Outside)).
   - intros pos k p;rewrite PermI;apply Readonly. }
 pose proof (wnaf_129_array_lframe m mi b1 0 15 1 129 last1 digits1 _ Array1 FrameI ltac:(intros;exact B1P)) as Array1I.
 pose proof (wnaf_129_array_lframe m mi b128 0 15 1 129 last128 digits128 _ Array128 FrameI ltac:(intros;exact B128P)) as Array128I.
 destruct (wnaf_literal_array_for_generator mi b1 0 word1 digits1 last1 Array1I Digits1) as [Bound1 Data1].
 destruct (wnaf_literal_array_for_generator mi b128 0 word128 digits128 last128 Array128I Digits128) as [Bound128 Data128].
 set (bits:=Z.max (last1+1) (last128+1)) in *.
 assert (Bound : 0<=bits<=129) by (unfold bits;lia).
 assert (Count : (Z.to_nat bits<=129)%nat) by (apply Nat2Z.inj_le;rewrite Z2Nat.id by lia;lia).
 set (li:=PTree.set _i (Vint (Int.repr (bits-1))) le).
 assert (PRL : li!_r=Some (Vptr bp Ptrofs.zero)) by (unfold li;rewrite PTree.gso by discriminate;exact PR).
 assert (NoL : li!_no=Some (Vlong Int64.zero)) by (unfold li;rewrite PTree.gso by discriminate;exact No).
 assert (L1L : li!_bits_ng_1=Some (Vint (Int.repr (last1+1)))) by (unfold li;rewrite PTree.gso by discriminate;exact L1).
 assert (L128L : li!_bits_ng_128=Some (Vint (Int.repr (last128+1)))) by (unfold li;rewrite PTree.gso by discriminate;exact L128).
 assert (PI : li!_i=Some (Vint (Int.repr (Z.of_nat (Z.to_nat bits)-1)))).
 { rewrite Z2Nat.id by lia;unfold li;apply PTree.gss. }
 assert (ZeroOut : rescale_field_output (fun _ : nat=>Int64.zero)=@literal_fe_zero256 Alg.CoreFunSem tt)
   by exact zero_field_writer_literal_output.
 assert (ZeroTest : Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (@literal_fe_zero256 Alg.CoreFunSem tt))=true).
 { rewrite literal_curve_zero_numeric;unfold literal_fe_zero256;rewrite Word.zero_correct;reflexivity. }
 assert (FlagReady : Mem.load Mint32 mi bp 120=Some (Vint
   (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (@literal_fe_zero256 Alg.CoreFunSem tt)))))).
 { rewrite ZeroTest;exact FlagI. }
 assert (Repr : ((rescale_field_output (fun _ : nat=>Int64.zero),rescale_field_output (fun _ : nat=>Int64.zero)),
   rescale_field_output (fun _ : nat=>Int64.zero))=
   ((@literal_fe_zero256 Alg.CoreFunSem tt,@literal_fe_zero256 Alg.CoreFunSem tt),@literal_fe_zero256 Alg.CoreFunSem tt)).
 { rewrite ZeroOut;reflexivity. }
 destruct (exec_generator_loop e bp ba bb b1 b128 inv (last1+1) (last128+1)
   (wnaf_literal_digit_at word1) (wnaf_literal_digit_at word128) Bound1 Bound128 Sep
   (wnaf_literal_digit_at_valid word1) (wnaf_literal_digit_at_valid word128)
   ltac:(intros j Range Above;exact (proj2 (proj2 (Data1 j Range)) Above))
   ltac:(intros j Range Above;exact (proj2 (proj2 (Data128 j Range)) Above))
   E1 E128 EA EZ EL EAdd ED ET1 ET128 BI One (Z.to_nat bits) Count li mi
   (fun _ : nat=>Int64.zero) (fun _ : nat=>Int64.zero) (fun _ : nat=>Int64.zero)
   (@literal_fe_zero256 Alg.CoreFunSem tt) (@literal_fe_zero256 Alg.CoreFunSem tt) (@literal_fe_zero256 Alg.CoreFunSem tt)
   TablesI PRL NoL PI L1L L128L
   ltac:(intros j Range;exact (proj1 (proj2 (Data1 j ltac:(lia)))))
   ltac:(intros j Range;exact (proj1 (proj2 (Data128 j ltac:(lia)))))
   square_zero_bounds square_zero_bounds square_zero_bounds Repr FlagReady XI YI ZI InvI PFI AFI IFI)
   as (ll & ml & ox & oy & lz & Loop & PRF & EndI & XL & YL & ZL & FlagL & InvL & PFL & AFL & IFL &
     BXL & BYL & BZL & LiteralL & TablesL & FrameL).
 assert (LiteralLoop : ((rescale_field_output ox,rescale_field_output oy),rescale_field_output lz)=
   @literal_generator_digits129 Alg.CoreFunSem (@literal_gej_infinity Alg.CoreFunSem tt,
     (@literal_wnaf15 Alg.CoreFunSem (inl tt,word1),@literal_wnaf15 Alg.CoreFunSem (inl tt,word128)))).
 { change (((rescale_field_output ox,rescale_field_output oy),rescale_field_output lz)=
     generator_loop_result (Z.to_nat bits) (wnaf_literal_digit_at word1) (wnaf_literal_digit_at word128)
       (@literal_gej_infinity Alg.CoreFunSem tt)) in LiteralL.
   rewrite LiteralL;apply generator_wnaf_short_result;[exact Count|].
   intros j Range;assert (RangeZ : 0<=Z.of_nat j<129) by lia.
   assert (Above : bits<=Z.of_nat j).
   { pose proof (proj1 Range) as Lower;apply Nat2Z.inj_le in Lower;rewrite Z2Nat.id in Lower by lia;exact Lower. }
   split.
   - apply (proj2 (proj2 (Data1 _ RangeZ)));unfold bits in Above;lia.
   - apply (proj2 (proj2 (Data128 _ RangeZ)));unfold bits in Above;lia. }
 destruct (exec_generator_final_one ox oy lz inv e ll ml bp bb
   (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output lz))))
   PRF EZ EM BPB BXL BYL BZL BI One FlagL XL YL ZL InvL PFL IFL)
   as (mf & oz & Final & XO & YO & ZO & FlagO & InvO & PFO & IFO & BZO & ZValue & FrameF).
 assert (AFO : Mem.range_perm mf ba 0 88 Cur Freeable).
 { eapply curve_keep_free;[lia|exact AFL|exact FrameF|];intros;split;assumption. }
 assert (FlagOut : Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz)))))).
 { rewrite ZValue;exact FlagO. }
 assert (Literal : ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
   @literal_generator_digits129 Alg.CoreFunSem (@literal_gej_infinity Alg.CoreFunSem tt,
     (@literal_wnaf15 Alg.CoreFunSem (inl tt,word1),@literal_wnaf15 Alg.CoreFunSem (inl tt,word128))))
   by (rewrite ZValue;exact LiteralLoop).
 assert (Frame : lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameI|];intros b pos Outside Valid;tauto.
   - eapply lframe_trans;[exact FrameL|];eapply lframe_implies;[exact FrameF|];intros b pos Outside Valid;tauto. }
 set (lf:=PTree.set _t'16 (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output lz))))) ll).
 assert (PRout : lf!_r=Some (Vptr bp Ptrofs.zero)) by (unfold lf;rewrite PTree.gso by discriminate;exact PRF).
 exists lf,mf,ox,oy,oz;split;[|repeat first [assumption|split]].
 rewrite generator_point_stage_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mi).
 - unfold generator_infinity_statement;eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero]) (v:=Vundef).
   + unfold secp_pure;repeat first [left;reflexivity|right].
   + exact EInf.
   + eapply eval_Econs;[apply eval_Etempvar;exact PR|reflexivity|constructor].
   + exact Initialize.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=ll) (m1:=ml);[|exact Final].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=li) (m1:=mi);[|exact Loop].
   unfold generator_start_index_statement;apply exec_Sset;eapply eval_Ebinop;
     [apply eval_Etempvar;exact Bits|constructor|].
   change (Some (Vint (Int.sub (Int.repr bits) Int.one))=Some (Vint (Int.repr (bits-1)))).
   change Int.one with (Int.repr 1);rewrite Int.sub_signed,!Int.signed_repr by
     (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia);reflexivity.
(** This composed call checks a larger closed proof term; individual tactics
    above retain the 10-second development limit. *)
Set Default Timeout 60.
Time Qed.
