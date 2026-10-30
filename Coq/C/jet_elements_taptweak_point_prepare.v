(** Original first-point preprocessing guard and loop controls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_sx_exec C.jet_sx_pure
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_generator_preprocess C.jet_secp_generator_zero_scalar C.jet_secp_gej_flag_read
 C.jet_secp_statement_prefix
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_scalar_zero_exec C.jet_secp_scalar_zero_numeric C.jet_secp_scalar_negate_canonical
 C.jet_secp_scalar_overflow_numeric C.jet_secp_strauss_bits_max C.jet_secp_strauss_table_call
 C.jet_word_repr C.jet_memset_model C.jet_secp_canonical_scalar C.jet_secp_split_literal
 C.jet_secp_split_constants C.jet_secp_split_function C.jet_secp_strauss_split_wnaf
 C.jet_secp_strauss_wnaf_calls C.jet_secp_generator_globalz_call C.jet_secp_fe_nv
 C.jet_secp_square_columns C.jet_secp_point_mul_storage C.jet_secp_double_all_calls
 C.jet_secp_odd_table_body C.jet_secp_odd_table_loop C.jet_secp_scalar_table_literal
 C.jet_secp_odd_table_literal_walk C.jet_secp_globalz_loop C.jet_secp_globalz_word_walk
 C.jet_secp_globalz_pass2 C.jet_secp_field_mul_small C.jet_secp_field_zero_owned
 C.jet_secp_rescale_literal C.jet_secp_multiply_normalize_bridge C.jet_secp_wnaf_slice_frame
 C.jet_secp_wnaf_loop C.jet_secp_wnaf_pair5 C.jet_secp_wnaf5_input C.jet_secp_wnaf5_literal
 C.jet_secp_wnaf5_signed_array C.jet_secp_field_read_preservation C.jet_secp_scalar_add_reader_support
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Opaque secp_ge canonical_scalar_normalize literal_scalar_split_lambda odd_table_final_state
 point_mul_words literal_scalar_table5.
Set Default Timeout 10.

Require Import C.jet_secp_strauss_first_loop C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_split_constants C.jet_elements_taptweak_split_function
 C.jet_elements_taptweak_split_wnaf C.jet_elements_taptweak_scalar_prepare C.jet_transport C.jet_transport_locals.
Require Import C.jet_elements_taptweak_point_table.
Local Opaque elements_taptweak_ge elements_taptweak_multiplier_block elements_taptweak_basis_block elements_taptweak_lambda_block.
Theorem exec_elements_taptweak_strauss_check_finite e le m value bk ba :
 edom e(fn_vars f_secp256k1_ecmult_strauss_wnaf) ->
 (forall id,In id(map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)) ->exists b ty,e!id=Some(b,ty)) ->
 e!_secp256k1_scalar_is_zero=None -> e!_secp256k1_gej_is_infinity=None ->
 le!_na=Some (Vptr bk Ptrofs.zero) -> le!_a=Some (Vptr ba Ptrofs.zero) ->
 le!_np=Some (Vlong Int64.zero) -> 0<=value<2^256 -> value<>0 ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of value)) ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 Clight2.exec_stmt elements_taptweak_ge e le m generator_preprocess_check E0 (strauss_checked_temps le) m Out_normal.
Proof.
 intros Domain Bound ScalarSymbol FlagSymbol NA A NP Range Nonzero Input Flag.
 eapply elements_taptweak_preprocess_pure_transport;[exact Domain|exact Bound|left;reflexivity|].
 exact(exec_strauss_check_finite e le m value bk ba ScalarSymbol FlagSymbol NA A NP Range Nonzero Input Flag).
Qed.
Lemma exec_elements_taptweak_strauss_preprocess_one_from_work e le m lw mw :
 le!_np=Some (Vlong Int64.zero) -> le!_num=Some (Vlong Int64.one) ->
 Clight2.exec_stmt elements_taptweak_ge e le m generator_preprocess_work E0 lw mw Out_normal ->
 lw!_np=Some (Vlong Int64.zero) -> lw!_num=Some (Vlong Int64.one) ->
 Clight2.exec_stmt elements_taptweak_ge e le m generator_preprocess_loop E0
  (PTree.set _np (Vlong Int64.one) lw) mw Out_normal.
Proof.
 intros NP Num Work NPW NumW;rewrite generator_preprocess_loop_source.
 eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0) (out1:=Out_normal)
  (le1:=lw) (m1:=mw) (le2:=PTree.set _np (Vlong Int64.one) lw) (m2:=mw).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[|exact Work].
   eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=Datatypes.true);[|reflexivity|constructor].
   eapply eval_Ebinop;[apply eval_Etempvar;exact NP|apply eval_Etempvar;exact Num|reflexivity].
 - constructor.
 - apply exec_Sset;eapply eval_Ebinop;[apply eval_Etempvar;exact NPW|constructor|reflexivity].
 - eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
   eapply exec_Sseq_2;[|discriminate].
   eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=Datatypes.false);[|reflexivity|constructor].
   eapply eval_Ebinop.
   + apply eval_Etempvar;apply PTree.gss.
   + apply eval_Etempvar;rewrite PTree.gso by discriminate;exact NumW.
   + reflexivity.
Qed.
Theorem exec_elements_taptweak_strauss_preprocess_finite (Model:memset_model) e le m raw bk br1 br2 bs bp ba bt bx bo bj
 x y z (ax ay az:Ty.tySem (Word 8)) :
 edom e(fn_vars f_secp256k1_ecmult_strauss_wnaf) ->
 (forall id,In id(map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)) ->exists b ty,e!id=Some(b,ty)) ->
 e!_na_1=Some (br1,Tstruct __5826 noattr) -> e!_na_lam=Some (br2,Tstruct __5826 noattr) ->
 e!_Z=Some (bo,Tstruct __5467 noattr) -> e!_tmp=Some (bj,Tstruct __6123 noattr) ->
 e!_secp256k1_scalar_is_zero=None -> e!_secp256k1_gej_is_infinity=None ->
 e!_secp256k1_scalar_split_lambda=None -> e!_secp256k1_ecmult_wnaf=None ->
 e!_secp256k1_ecmult_odd_multiples_table=None -> e!_secp256k1_ge_table_set_globalz=None ->
 le!_na=Some (Vptr bk Ptrofs.zero) -> le!_a=Some (Vptr ba Ptrofs.zero) ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_num=Some (Vlong Int64.one) ->
 le!_no=Some (Vlong Int64.zero) -> le!_bits=Some (Vint Int.zero) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 elements_taptweak_split_ready m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)<>0 ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 (forall b hi,In (b,hi) (strauss_preprocess_storage bk br1 br2 bs bp ba bt bx bo bj) ->
  Mem.range_perm m b 0 hi Cur Freeable) -> NoDup [bk;br1;br2;bs;bp;ba;bt;bx;bo;bj] ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az -> field_zero_result z=Int.zero ->
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 let sf:=odd_table_final_state x y z in exists lef mf last1 last2 digits1 digits2 xf yf,
 Clight2.exec_stmt elements_taptweak_ge e le m strauss_preprocess_finite_statement E0 lef mf Out_normal /\
 lef!_np=Some (Vlong Int64.one) /\ lef!_no=Some (Vlong Int64.one) /\
 lef!_bits=Some (Vint (Int.repr (Z.max (last1+1) (last2+1)))) /\
 0<=Z.max (last1+1) (last2+1)<=129 /\
 wnaf_array_state mf bp 0 129 5 (wnaf5_input_sign (fst (fst halves))) 129 last1 digits1 /\
 wnaf_array_state mf bp 516 129 5 (wnaf5_input_sign (fst (snd halves))) 129 last2 digits2 /\
 0<=last1+1<=129 /\ 0<=last2+1<=129 /\
 Mem.load Mint32 mf bp 1032=Some (Vint (Int.repr (last1+1))) /\
 Mem.load Mint32 mf bp 1036=Some (Vint (Int.repr (last2+1))) /\
 map wnaf5_literal_value (literal_wnaf5_digits (fst halves))=
  rev (map (fun i=>wnaf5_input_sign (fst (fst halves))*digits1 (Z.of_nat i)) (seq 0 129)) /\
 map wnaf5_literal_value (literal_wnaf5_digits (snd halves))=
  rev (map (fun i=>wnaf5_input_sign (fst (snd halves))*digits2 (Z.of_nat i)) (seq 0 129)) /\
 globalz_table_rep mf bt xf yf /\ globalz_table_bounds xf yf /\
 (forall k,(k<8)%nat -> mul_small_input_bounds (yf k)) /\
 fe_at mf bo 0 (words5 (point_mul_words (odd_table_z sf) (double_output_z_words y z))) /\
 square_input_bounds (point_mul_words (odd_table_z sf) (double_output_z_words y z)) /\
 (rescale_field_output (point_mul_words (odd_table_z sf) (double_output_z_words y z)),
  globalz_word_vector (globalz_decoded_points xf yf))=@literal_scalar_table5 Alg.CoreFunSem ((ax,ay),az) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
 Mem.load Mint32 mf ba 120=Some (Vint Int.zero) /\
 Mem.load Mptr mf bs 16=Some (Vptr bp Ptrofs.zero) /\
 Mem.load Mptr mf bs 8=Some (Vptr bt Ptrofs.zero) /\ Mem.load Mptr mf bs 0=Some (Vptr bx Ptrofs.zero) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) /\
 (forall b hi,In (b,hi) (strauss_preprocess_storage bk br1 br2 bs bp ba bt bx bo bj) ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\ elements_taptweak_split_ready mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun old pos=>elements_taptweak_split_function_frame bk br1 br2 old pos /\
  wnaf_slice_outside bp 0 260 old pos /\ old<>bt /\ old<>bj /\ old<>bx /\ old<>bo) m mf /\
 (forall id,~In id [_np;_no;_bits;_t'1;_t'2;_t'3;_t'4;_t'5;_t'32;_t'33;_t'36;_t'37;
   _t'38;_t'39;_t'40;_t'41;_t'42;_t'43;_t'44;_t'45;_t'46;_t'47] -> lef!id=le!id).
Proof.
 intros Domain BoundEnv Low High LocalZ LocalTmp ZeroSymbol FlagSymbol SplitSymbol WnafSymbol OddSymbol GlobalSymbol
  NA A State Num No Bits PS PT PX Ready Input Nonzero BX BY BZ X Y Z Flag Owned Separate HX HY HZ Finite;
  cbv zeta.
 assert (FK:Mem.range_perm m bk 0 32 Cur Freeable) by (apply Owned;unfold strauss_preprocess_storage;cbn [In];tauto).
 assert (F1:Mem.range_perm m br1 0 32 Cur Freeable) by (apply Owned;unfold strauss_preprocess_storage;cbn [In];tauto).
 assert (F2:Mem.range_perm m br2 0 32 Cur Freeable) by (apply Owned;unfold strauss_preprocess_storage;cbn [In];tauto).
 assert (FS:Mem.range_perm m bs 0 24 Cur Freeable) by (apply Owned;unfold strauss_preprocess_storage;cbn [In];tauto).
 assert (FP:Mem.range_perm m bp 0 1040 Cur Freeable) by (apply Owned;unfold strauss_preprocess_storage;cbn [In];tauto).
 assert (FA:Mem.range_perm m ba 0 128 Cur Freeable) by (apply Owned;unfold strauss_preprocess_storage;cbn [In];tauto).
 pose (l0:=PTree.set _np (Vlong Int64.zero) le).
 pose (lc:=strauss_checked_temps l0).
 assert (NP0:l0!_np=Some (Vlong Int64.zero)) by (unfold l0;apply PTree.gss).
 assert (OtherC:forall id,~In id [_np;_t'1;_t'2;_t'3] -> lc!id=le!id).
 { intros id Outside;unfold lc;rewrite strauss_checked_other;
   [unfold l0;rewrite PTree.gso;cbn [In] in Outside;intuition congruence|cbn [In] in Outside|-*;tauto]. }
 assert (NPC:lc!_np=Some (Vlong Int64.zero)).
 { unfold lc;rewrite strauss_checked_other by (cbn [In];intuition discriminate);exact NP0. }
 assert (NC:lc!_na=Some (Vptr bk Ptrofs.zero)) by (rewrite OtherC by (cbn [In];intuition discriminate);exact NA).
 assert (SC:lc!_state=Some (Vptr bs Ptrofs.zero)) by (rewrite OtherC by (cbn [In];intuition discriminate);exact State).
 assert (NoC:lc!_no=Some (Vlong Int64.zero)) by (rewrite OtherC by (cbn [In];intuition discriminate);exact No).
 assert (BitsC:lc!_bits=Some (Vint Int.zero)) by (rewrite OtherC by (cbn [In];intuition discriminate);exact Bits).
 assert (Guard:Clight2.exec_stmt elements_taptweak_ge e l0 m generator_preprocess_check E0 lc m Out_normal).
 { apply (exec_elements_taptweak_strauss_check_finite e l0 m
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)) bk ba Domain BoundEnv).
   - exact ZeroSymbol.
   - exact FlagSymbol.
   - unfold l0;rewrite PTree.gso by discriminate;exact NA.
   - unfold l0;rewrite PTree.gso by discriminate;exact A.
   - exact NP0.
   - apply word_toZ_range.
   - exact Nonzero.
   - exact Input.
   - exact Flag. }
 assert (D:bk<>br1 /\ bk<>br2 /\ bk<>bs /\ bk<>bp /\ bk<>ba /\ bk<>bt /\ bk<>bx /\ bk<>bo /\ bk<>bj /\
  br1<>br2 /\ br1<>bs /\ br1<>bp /\ br1<>ba /\ br1<>bt /\ br1<>bx /\ br1<>bo /\ br1<>bj /\
  br2<>bs /\ br2<>bp /\ br2<>ba /\ br2<>bt /\ br2<>bx /\ br2<>bo /\ br2<>bj /\
  bs<>bp /\ bs<>ba /\ bs<>bt /\ bs<>bx /\ bs<>bo /\ bs<>bj /\ bp<>ba /\ bp<>bt /\ bp<>bx /\ bp<>bo /\ bp<>bj /\
  ba<>bt /\ ba<>bx /\ ba<>bo /\ ba<>bj /\ bt<>bx /\ bt<>bo /\ bt<>bj /\ bx<>bo /\ bx<>bj /\ bo<>bj).
 { repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence. }
 assert (ScalarSep:NoDup [bk;br1;br2;bs;bp]) by (repeat constructor;cbn [In];intuition congruence).
 destruct (exec_elements_taptweak_strauss_scalar_prepare Model e lc m raw bk br1 br2 bs bp Low High SplitSymbol WnafSymbol
  NC NPC SC NoC BitsC PS Ready Input FK F1 F2 FS FP ScalarSep)
  as (ms & last1 & last2 & digits1 & digits2 & Scalar & Max & MaxBound & ScalarOther & Array1 & Array2 &
   Bound1 & Bound2 & Count1 & Count2 & PSS & Source1 & Source2 & SourceK & FPS & ReadyS & KeepS & ReadonlyS &
   FrameS & Literal1 & Literal2).
 pose (ls:=strauss_scalar_prepare_temps lc bp (last1+1) (last2+1)).
 assert (OtherS:forall id,~In id [_np;_bits;_t'1;_t'2;_t'3;_t'4;_t'5;_t'38;_t'39;_t'40;_t'41;_t'42;_t'43;
   _t'44;_t'45;_t'46;_t'47] -> ls!id=le!id).
 { intros id Outside;unfold ls;rewrite ScalarOther;
   [apply OtherC|];cbn [In] in Outside|-*;tauto. }
 assert (NPS:ls!_np=Some (Vlong Int64.zero)).
 { unfold ls;rewrite ScalarOther by (cbn [In];intuition discriminate);exact NPC. }
 assert (AS:ls!_a=Some (Vptr ba Ptrofs.zero)) by (rewrite OtherS by (cbn [In];intuition discriminate);exact A).
 assert (SS:ls!_state=Some (Vptr bs Ptrofs.zero)) by (rewrite OtherS by (cbn [In];intuition discriminate);exact State).
 assert (NoS:ls!_no=Some (Vlong Int64.zero)) by (rewrite OtherS by (cbn [In];intuition discriminate);exact No).
 assert (StateOutside:forall pos,elements_taptweak_split_function_frame bk br1 br2 bs pos /\ wnaf_slice_outside bp 0 260 bs pos).
 { intro pos;split.
   - exact (elements_taptweak_strauss_split_owned_frame m bk br1 br2 bs Ready (FS 0 ltac:(clear;lia))
      ltac:(clear -D;intuition congruence) ltac:(clear -D;intuition congruence)
      ltac:(clear -D;intuition congruence) pos).
   - left;clear -D;tauto. }
 assert (PointOutside:forall pos,elements_taptweak_split_function_frame bk br1 br2 ba pos /\ wnaf_slice_outside bp 0 260 ba pos).
 { intro pos;split.
   - exact (elements_taptweak_strauss_split_owned_frame m bk br1 br2 ba Ready (FA 0 ltac:(clear;lia))
      ltac:(clear -D;intuition congruence) ltac:(clear -D;intuition congruence)
      ltac:(clear -D;intuition congruence) pos).
   - left;clear -D;intuition congruence. }
 assert (VS:Mem.valid_block m bs) by (eapply Mem.perm_valid_block;apply (FS 0);clear;lia).
 assert (VA:Mem.valid_block m ba) by (eapply Mem.perm_valid_block;apply (FA 0);clear;lia).
 assert (PTS:Mem.load Mptr ms bs 8=Some (Vptr bt Ptrofs.zero)).
 { rewrite (proj1 FrameS Mptr bs 8 VS ltac:(intros;apply StateOutside));exact PT. }
 assert (PXS:Mem.load Mptr ms bs 0=Some (Vptr bx Ptrofs.zero)).
 { rewrite (proj1 FrameS Mptr bs 0 VS ltac:(intros;apply StateOutside));exact PX. }
 assert (XS:fe_at ms ba 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact FrameS|exact PointOutside]).
 assert (YS:fe_at ms ba 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact FrameS|exact PointOutside]).
 assert (ZS:fe_at ms ba 80 (words5 z)) by (eapply field_at_lframe;[exact Z|exact FrameS|exact PointOutside]).
 assert (FlagS:Mem.load Mint32 ms ba 120=Some (Vint Int.zero)).
 { rewrite (proj1 FrameS Mint32 ba 120 VA ltac:(intros;apply PointOutside));exact Flag. }
 assert (TableSep:NoDup [ba;bs;bt;bx;bo;bj]) by (repeat constructor;cbn [In];intuition congruence).
 assert (OwnedTable:forall b hi,In (b,hi) [(bs,24);(ba,128);(bj,128);(bt,704);(bx,320);(bo,40)] ->
  Mem.range_perm ms b 0 hi Cur Freeable).
 { intros b hi Slot pos Range;apply KeepS,(Owned b hi);[unfold strauss_preprocess_storage;cbn [In] in Slot|-*;tauto|exact Range]. }
 destruct (exec_elements_taptweak_strauss_table_prepare e ls ms ba bs bt bx bo bj x y z ax ay az Domain BoundEnv
  LocalZ LocalTmp OddSymbol GlobalSymbol AS NPS SS NoS PTS PXS BX BY BZ XS YS ZS FlagS OwnedTable TableSep HX HY HZ Finite)
  as (mf & xf & yf & TableRun & Table & TableBound & TightY & Product & ProductBound & TableLiteral &
   XF & YF & ZF & FlagF & PTF & PXF & OwnedTF & KeepT & ReadonlyT & FrameT & NoT & TableOther &
   m1 & Caller & GlobalCall & PT1 & PX1).
 pose (lb:=strauss_first_table_temps ls bt bx).
 assert (Body:Clight2.exec_stmt elements_taptweak_ge e lc m generator_preprocess_after_check E0 lb m1 Out_normal).
 { eapply exec_elements_taptweak_strauss_scalar_prepare_then_rest;[exact Scalar|exact Caller]. }
 assert (Work:Clight2.exec_stmt elements_taptweak_ge e l0 m generator_preprocess_work E0 lb m1 Out_normal).
 { rewrite generator_preprocess_work_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Guard|exact Body]. }
 assert (NPB:lb!_np=Some (Vlong Int64.zero)).
 { unfold lb,strauss_first_table_temps,strauss_table_call_temps;rewrite !PTree.gso by discriminate;exact NPS. }
 assert (NumB:lb!_num=Some (Vlong Int64.one)).
 { unfold lb,strauss_first_table_temps,strauss_table_call_temps;rewrite !PTree.gso by discriminate;
   rewrite OtherS by (cbn [In];intuition discriminate);exact Num. }
 pose (ll:=PTree.set _np (Vlong Int64.one) lb).
 assert (Loop:Clight2.exec_stmt elements_taptweak_ge e le m generator_preprocess_statement E0 ll m1 Out_normal).
 { rewrite generator_preprocess_statement_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=l0) (m1:=m).
   - apply exec_Sset;eapply eval_Ecast;[constructor|reflexivity].
   - apply (exec_elements_taptweak_strauss_preprocess_one_from_work e l0 m lb m1 NP0);[unfold l0;rewrite PTree.gso by discriminate;exact Num|exact Work|exact NPB|exact NumB]. }
 assert (StateL:ll!_state=Some (Vptr bs Ptrofs.zero)).
 { unfold ll,lb,strauss_first_table_temps,strauss_table_call_temps;rewrite !PTree.gso by discriminate;exact SS. }
 assert (NoL:ll!_no=Some (Vlong Int64.one)).
 { unfold ll,lb,strauss_first_table_temps;rewrite PTree.gso by discriminate;apply PTree.gss. }
 pose (lef:=generator_globalz_call_temps ll (Vptr bt Ptrofs.zero) (Vptr bx Ptrofs.zero)).
 pose proof (exec_elements_taptweak_strauss_globalz_from_call e ll m1 mf bs bt bx GlobalSymbol StateL NoL PT1 PX1 GlobalCall) as Global.
 assert (A1F:wnaf_array_state mf bp 0 129 5
  (wnaf5_input_sign (fst (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw)))) 129 last1 digits1).
 { eapply wnaf_array_slice_lframe;[exact Array1|exact FrameT|intros;intuition congruence]. }
 assert (A2F:wnaf_array_state mf bp 516 129 5
  (wnaf5_input_sign (fst (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw)))) 129 last2 digits2).
 { eapply wnaf_array_slice_lframe;[exact Array2|exact FrameT|intros;intuition congruence]. }
 assert (VPS:Mem.valid_block ms bp) by (eapply Mem.perm_valid_block;apply (FPS 0);clear;lia).
 assert (Count1F:Mem.load Mint32 mf bp 1032=Some (Vint (Int.repr (last1+1)))).
 { rewrite (proj1 FrameT Mint32 bp 1032 VPS);[exact Count1|intros;intuition congruence]. }
 assert (Count2F:Mem.load Mint32 mf bp 1036=Some (Vint (Int.repr (last2+1)))).
 { rewrite (proj1 FrameT Mint32 bp 1036 VPS);[exact Count2|intros;intuition congruence]. }
 assert (VSS:Mem.valid_block ms bs) by (eapply Mem.perm_valid_block;apply KeepS,(FS 0);clear;lia).
 assert (PSF:Mem.load Mptr mf bs 16=Some (Vptr bp Ptrofs.zero)).
 { rewrite (proj1 FrameT Mptr bs 16 VSS);[exact PSS|intros;intuition congruence]. }
 assert (InputF:scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))))).
 { eapply scalar_at_lframe;[exact SourceK|exact FrameT|intros;intuition congruence]. }
 assert (Keep:keeps_permissions m mf) by (eapply keeps_permissions_trans;[exact KeepS|exact KeepT]).
 exists lef,mf,last1,last2,digits1,digits2,xf,yf;split.
 - unfold strauss_preprocess_finite_statement;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Loop|exact Global].
 - split;[unfold lef,generator_globalz_call_temps;rewrite !PTree.gso by discriminate;unfold ll;apply PTree.gss|];
   split;[unfold lef,generator_globalz_call_temps;rewrite !PTree.gso by discriminate;exact NoL|];split.
   + unfold lef,generator_globalz_call_temps,ll,lb,strauss_first_table_temps,strauss_table_call_temps;
     rewrite !PTree.gso by discriminate;exact Max.
   + split;[exact MaxBound|];split;[exact A1F|];split;[exact A2F|];split;[exact Bound1|];split;[exact Bound2|];
     split;[exact Count1F|];split;[exact Count2F|];split;[exact Literal1|];split;[exact Literal2|];
     split;[exact Table|];split;[exact TableBound|];split;[exact TightY|];split;[exact Product|];
     split;[exact ProductBound|];split;[exact TableLiteral|];split;[exact XF|];split;[exact YF|];split;[exact ZF|];
     split;[exact FlagF|];split;[exact PSF|];split;[exact PTF|];split;[exact PXF|];split;[exact InputF|];split.
     * intros b hi Slot pos Range;apply Keep,(Owned b hi Slot);exact Range.
     * split;[eapply elements_taptweak_split_readonly;[exact ReadyS|exact ReadonlyT]|];split;[exact Keep|];split.
       -- eapply preserved_trans;[exact ReadonlyS|exact ReadonlyT].
       -- split.
          ++ eapply lframe_trans.
             ** eapply lframe_implies;[exact FrameS|intros b pos (SplitF & WnafF & _) _;split;assumption].
             ** eapply lframe_implies;[exact FrameT|intros b pos (_ & _ & T & J & Xb & O) _;repeat split;assumption].
          ++ intros id Outside;unfold lef,generator_globalz_call_temps,ll,lb,strauss_first_table_temps,strauss_table_call_temps.
             rewrite !PTree.gso by (clear -Outside;cbn [In] in Outside;intuition congruence).
             apply OtherS;clear -Outside;cbn [In] in Outside|-*;tauto.
Qed.
