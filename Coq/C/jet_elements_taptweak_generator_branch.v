(** Original nonnull generator branch with an arbitrary incoming bit count.
    Scalar splitting and both wNAF calls execute here, using the approved
    memset model for the original clear operations. Point-stage composition,
    entry/preparation and final Strauss-local frees remain caller obligations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Cop Clight Clightdefs ClightBigstep
  Integers Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_curve_statements C.jet_secp_curve_frame
  C.jet_secp_field_read_preservation C.jet_secp_multiply_normalize_bridge
  C.jet_secp_multiply_finish_product C.jet_secp_square_columns C.jet_secp_rescale_literal
  C.jet_secp_canonical_zero C.jet_secp_canonical_scalar C.jet_secp_point_set_bit
  C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
  C.jet_secp_scalar_split128_literal C.jet_secp_statement_prefix C.jet_secp_generator_entry
  C.jet_secp_generator_split_call C.jet_secp_generator_wnaf_setup
  C.jet_secp_generator_globals C.jet_secp_generator_point_stage C.jet_secp_generate_program
  C.jet_secp_wnaf_digit C.jet_secp_wnaf_entry15 C.jet_secp_wnaf_loop.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_generate rescale_field_output.


Require Import C.jet_secp_generator_wnaf_general C.jet_secp_wnaf_memset C.jet_memset_model
 C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_values C.jet_secp_wnaf_literal_array C.jet_clight_readonly_frame
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve
 C.jet_secp_generator_pair_general.
Require Import C.jet_secp_strauss_generator_branch C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_generator_globals C.jet_elements_taptweak_internal.
Require Import C.jet_elements_taptweak_generator_from C.jet_elements_taptweak_generator_split.
Local Opaque elements_taptweak_ge elements_taptweak_generator_table_block.
Theorem exec_elements_taptweak_strauss_generator_branch (Model:memset_model) e le m value bng b0 b128 bw0 bw128 current :
 NoDup [b0;b128;bw0;bw128;bng] ->
 e!_ng_1=Some (b0,Tstruct __5826 noattr) ->
 e!_ng_128=Some (b128,Tstruct __5826 noattr) ->
 e!_wnaf_ng_1=Some (bw0,tarray tint 129) ->
 e!_wnaf_ng_128=Some (bw128,tarray tint 129) ->
 e!_secp256k1_scalar_split_128=None -> e!_secp256k1_ecmult_wnaf=None ->
 le!_ng=Some (Vptr bng Ptrofs.zero) -> 0<=current<=129 ->
 le!_bits=Some (Vint (Int.repr current)) ->
 scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))) ->
 Mem.range_perm m bng 0 32 Cur Freeable ->
 Mem.range_perm m b0 0 32 Cur Freeable -> Mem.range_perm m b128 0 32 Cur Freeable ->
 Mem.range_perm m bw0 0 516 Cur Freeable -> Mem.range_perm m bw128 0 516 Cur Freeable ->
 exists mf last0 last128 digits0 digits128,
 let lef:=generator_wnaf_setup_temps_from le current (last0+1) (last128+1) in
 Clight2.exec_stmt elements_taptweak_ge e le m generator_scalar_branch E0 lef mf Out_normal /\
 lef!_bits=Some (Vint (Int.repr (Z.max (Z.max current (last0+1)) (last128+1)))) /\
 lef!_bits_ng_1=Some (Vint (Int.repr (last0+1))) /\
 lef!_bits_ng_128=Some (Vint (Int.repr (last128+1))) /\
 (forall id,id<>_bits -> id<>_bits_ng_1 -> id<>_bits_ng_128 -> id<>_t'6 -> id<>_t'7 -> lef!id=le!id) /\
 wnaf_array_state mf bw0 0 129 15 1 129 last0 digits0 /\
 wnaf_array_state mf bw128 0 129 15 1 129 last128 digits128 /\
 map wnaf_literal_value (literal_wnaf15_digits (inl tt,literal_split128_low value))=
  rev (map (fun i=>digits0 (Z.of_nat i)) (seq 0 129)) /\
 map wnaf_literal_value (literal_wnaf15_digits (inl tt,literal_split128_high value))=
  rev (map (fun i=>digits128 (Z.of_nat i)) (seq 0 129)) /\
 (forall old pos k p,Mem.valid_block m old ->
  (Mem.perm mf old pos k p <-> Mem.perm m old pos k p)) /\
 (forall h,elements_taptweak_generator_table_state h m -> elements_taptweak_generator_table_state h mf) /\
 lframe (fun b _=>b<>b0 /\ b<>b128 /\ b<>bw0 /\ b<>bw128 /\ b<>bng) m mf /\readonly_preserved m mf.
Proof.
 intros Sep S0 S128 W0 W128 SplitSymbol WnafSymbol NG Current Bits Input
  OwnedNG Owned0 Owned128 OwnedW0 OwnedW128.
 pose proof Sep as Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate.
 assert (S0S128:b0<>b128) by intuition congruence.
 assert (S0NG:b0<>bng) by intuition congruence.
 assert (S128NG:b128<>bng) by intuition congruence.
 assert (Small:NoDup [b0;b128;bw0;bw128]) by
  (exact (NoDup_app_remove_r [b0;b128;bw0;bw128] [bng] Sep)).
 assert (Present:Cop.bool_val (Vptr bng Ptrofs.zero) (tptr (Tstruct __5826 noattr)) m=Some Datatypes.true).
 { change ((if Mem.weak_valid_pointer m bng 0 then Some Datatypes.true else None)=Some Datatypes.true).
   assert (Pointer:Mem.weak_valid_pointer m bng 0=Datatypes.true).
   { apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm.
     eapply Mem.perm_implies;[exact (OwnedNG 0 ltac:(clear;lia))|apply perm_any_N]. }
   rewrite Pointer;reflexivity. }
 destruct (exec_elements_taptweak_generator_scalar_split e le m value b0 b128 bng 0 S0 S128 SplitSymbol NG
  S0S128 S0NG S128NG Owned0 Owned128 Input)
  as (ms & Split & Low & High & Free0 & Free128 & BlocksS & PermS & FrameS & ReadS).

 assert (TablesS:forall h,elements_taptweak_generator_table_state h m -> elements_taptweak_generator_table_state h ms).
 { intros h Table;pose proof Table as [Rep Bounds].
   eapply elements_taptweak_generator_table_state_unchanged;[|exact Table].
   eapply Mem.unchanged_on_implies;[exact (proj2 ReadS)|].
   intros b pos Same Valid;subst b;split;[exact (proj1 Rep)|].
   eapply readonly_bounds_not_writable;exact Bounds. }
 assert (OwnedW0S:Mem.range_perm ms bw0 0 516 Cur Freeable).
 { intros pos Range;apply (proj2 (PermS bw0 pos Cur Freeable)),OwnedW0;exact Range. }
 assert (OwnedW128S:Mem.range_perm ms bw128 0 516 Cur Freeable).
 { intros pos Range;apply (proj2 (PermS bw128 pos Cur Freeable)),OwnedW128;exact Range. }
 destruct (exec_elements_taptweak_generator_wnaf_setup_from Model e le ms (literal_split128_low value) (literal_split128_high value)
  b0 b128 bw0 bw128 current Small W0 W128 S0 S128 WnafSymbol Current Bits Low High OwnedW0S OwnedW128S)
  as (mf & last0 & last128 & digits0 & digits128 & Wnaf & Maximum & Count0 & Count128 &
   Temps & Array0 & Array128 & FreeW0 & FreeW128 & FrameW & Literal0 & Literal128 & PermW & TablesW & ReadW).
 assert (Perms:forall old pos k p,Mem.valid_block m old ->
  (Mem.perm mf old pos k p <-> Mem.perm m old pos k p)).
 { intros old pos k p Valid;rewrite (PermW old pos k p (proj2 (proj2 FrameS) old Valid));apply PermS. }
 assert (Frame:lframe (fun b _=>b<>b0 /\ b<>b128 /\ b<>bw0 /\ b<>bw128 /\ b<>bng) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FrameS|intros b pos (N0 & N128 & NW0 & NW128 & NG0) _;repeat split;assumption].
   - eapply lframe_implies;[exact FrameW|intros b pos (N0 & N128 & NW0 & NW128 & NG0) _;split;assumption]. }
 exists mf,last0,last128,digits0,digits128;cbn zeta;split.
 - rewrite generator_scalar_branch_source;eapply exec_Sifthenelse
    with (v1:=Vptr bng Ptrofs.zero) (b:=Datatypes.true);
    [apply eval_Etempvar;exact NG|exact Present|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=ms);[exact Split|exact Wnaf].
 - split;[exact Maximum|];split;[exact Count0|];split;[exact Count128|];split;[exact Temps|];
   split;[exact Array0|];split;[exact Array128|];split;[exact Literal0|];split;[exact Literal128|];
   split;[exact Perms|];split;[|split;[exact Frame|eapply preserved_trans;[exact ReadS|exact ReadW]]].
   intros h Table;apply TablesW,TablesS;exact Table.
Qed.

