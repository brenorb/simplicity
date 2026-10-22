(** Both infinity branches against the fixed projective-addition expression.
    The branch premises are internal dispatch cases, not public input exclusions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge C.jet_secp_square_spec_bridge
 C.jet_secp_square_columns C.jet_secp_rescale_literal C.jet_secp_canonical_normalize
 C.jet_secp_canonical_zero C.jet_secp_literal_gej_predicate C.jet_secp_add_literal
 C.jet_secp_gej_add_infinite C.jet_secp_mixed_infinite_literal C.jet_secp_field_read_preservation.
Require Import C.jet_secp_multiply_literal_spec C.jet_secp_square_execution C.jet_secp_literal_add_program
 C.jet_secp_negate_literal_contract C.jet_secp_double_literal C.jet_secp_literal_infinity.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output canonical_fe_normalize literal_gej_is_infinity
 literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube literal_fe_negate
 literal_fe_multiply_int canonical_fe_is_zero literal_fe_one256 literal_fe_zero256 literal_gej_double literal_gej_infinity.

Lemma gej_add_left_infinite_value (ax ay az bx byword bz : Ty.tySem (Word 8)) :
 @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inr tt ->
 @literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz))=
 ((@canonical_fe_normalize Alg.CoreFunSem bx,@canonical_fe_normalize Alg.CoreFunSem byword),
   @canonical_fe_normalize Alg.CoreFunSem bz).
Proof.
 intro Inf;unfold literal_gej_add.
 change (snd (@literal_gej_add_ex Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)))=
   ((@canonical_fe_normalize Alg.CoreFunSem bx,@canonical_fe_normalize Alg.CoreFunSem byword),
    @canonical_fe_normalize Alg.CoreFunSem bz)).
 rewrite literal_gej_add_ex_infinite by exact Inf;reflexivity.
Qed.

Lemma gej_add_right_infinite_value (ax ay az bx byword bz : Ty.tySem (Word 8)) :
 @literal_gej_is_infinity Alg.CoreFunSem ((ax,ay),az)=inl tt ->
 @literal_gej_is_infinity Alg.CoreFunSem ((bx,byword),bz)=inr tt ->
 @literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz))=
 ((@canonical_fe_normalize Alg.CoreFunSem ax,@canonical_fe_normalize Alg.CoreFunSem ay),
   @canonical_fe_normalize Alg.CoreFunSem az).
Proof.
 intros Fin Inf;unfold literal_gej_add,literal_gej_add_ex.
 cbn -[literal_fe_add literal_fe_multiply literal_fe_square literal_fe_cube
 literal_fe_negate literal_fe_multiply_int canonical_fe_is_zero canonical_fe_normalize
 literal_fe_one256 literal_fe_zero256 literal_gej_double literal_gej_infinity literal_gej_is_infinity].
 match goal with |- snd (match ?c with inl _=>_ | inr _=>_ end)=_ =>
   assert (C : c=inl tt) by exact Fin;rewrite C end.
 match goal with |- snd (match ?c with inl _=>_ | inr _=>_ end)=_ =>
   assert (C' : c=inr tt) by exact Inf;rewrite C' end.
 reflexivity.
Qed.

Theorem exec_gej_add_a_infinite_literal e le m ba bb
 (ax ay az bx byword bz : Ty.tySem (Word 8)) flagB :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
 le!_b=Some (Vptr bb Ptrofs.zero) -> ba<>bb ->
 Mem.load Mint32 m ba 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=true ->
 Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bb 0 128 Cur Freeable ->
 fe_at m bb 0 (words5 (square_reader_rho bx)) -> fe_at m bb 40 (words5 (square_reader_rho byword)) ->
 fe_at m bb 80 (words5 (square_reader_rho bz)) -> Mem.load Mint32 m bb 120=Some (Vint flagB) -> exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_var) E0
  (PTree.set _t'4 (Vint Int.one) le) mf (Out_return None) /\
 fe_at mf ba 0 (words5 (square_reader_rho bx)) /\ fe_at mf ba 40 (words5 (square_reader_rho byword)) /\
 fe_at mf ba 80 (words5 (square_reader_rho bz)) /\
 ((rescale_field_output (square_reader_rho bx),rescale_field_output (square_reader_rho byword)),
   rescale_field_output (square_reader_rho bz))=
 @literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)) /\
 Mem.load Mint32 mf ba 120=Some (Vint flagB) /\
 Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bb 0 128 Cur Freeable /\
 lframe (fun b _=>b<>ba) m mf.
Proof.
 intros A R B Sep Flag Inf FA FB X Y Z FlagB.
 rewrite Inf in Flag;change (Mem.load Mint32 m ba 120=Some (Vint Int.one)) in Flag.
 destruct (exec_gej_add_a_infinite e le m ba bb (square_reader_rho bx) (square_reader_rho byword)
   (square_reader_rho bz) Int.one flagB A R B Sep Flag ltac:(discriminate) FA FB X Y Z FlagB)
   as (mf & Call & XO & YO & ZO & FlagO & FAF & FBF & Frame).
 exists mf;split;[exact Call|];split;[exact XO|];split;[exact YO|];split;[exact ZO|];split.
 - rewrite !mixed_reader_output,gej_add_left_infinite_value;[reflexivity|].
   change (@canonical_fe_is_zero Alg.CoreFunSem az=inr tt).
   destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [[] | []];[discriminate Inf|reflexivity].
 - split;[exact FlagO|];split;[exact FAF|];split;[exact FBF|exact Frame].
Qed.

Theorem exec_gej_add_b_infinite_literal e le m ba bb
 (ax ay az bx byword bz : Ty.tySem (Word 8)) :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
 le!_b=Some (Vptr bb Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
 Mem.load Mint32 m ba 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 Mem.load Mint32 m bb 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem bz)))) ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)=false ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem bz)=true ->
 Mem.range_perm m ba 0 128 Cur Freeable ->
 fe_at m ba 0 (words5 (square_reader_rho ax)) -> fe_at m ba 40 (words5 (square_reader_rho ay)) ->
 fe_at m ba 80 (words5 (square_reader_rho az)) -> exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_var) E0
  (PTree.set _t'3 (Vint Int.one) (PTree.set _t'4 (Vint Int.zero) le)) mf (Out_return None) /\
 fe_at mf ba 0 (words5 (square_reader_rho ax)) /\ fe_at mf ba 40 (words5 (square_reader_rho ay)) /\
 fe_at mf ba 80 (words5 (square_reader_rho az)) /\
 ((rescale_field_output (square_reader_rho ax),rescale_field_output (square_reader_rho ay)),
   rescale_field_output (square_reader_rho az))=
 @literal_gej_add Alg.CoreFunSem (((ax,ay),az),((bx,byword),bz)) /\
 Mem.range_perm mf ba 0 128 Cur Freeable /\ lframe (fun _ _=>True) m mf.
Proof.
 intros A R B Null FlagA FlagB Fin Inf Free X Y Z.
 rewrite Fin in FlagA;rewrite Inf in FlagB.
 change (Mem.load Mint32 m ba 120=Some (Vint Int.zero)) in FlagA.
 change (Mem.load Mint32 m bb 120=Some (Vint Int.one)) in FlagB.
 destruct (exec_gej_add_b_infinite e le m ba bb Int.one A R B Null FlagA FlagB ltac:(discriminate) Free)
   as (mf & Call & Frame).
 assert (XO : fe_at mf ba 0 (words5 (square_reader_rho ax))).
 { eapply field_at_lframe;[exact X|exact Frame|];intros;exact Logic.I. }
 assert (YO : fe_at mf ba 40 (words5 (square_reader_rho ay))).
 { eapply field_at_lframe;[exact Y|exact Frame|];intros;exact Logic.I. }
 assert (ZO : fe_at mf ba 80 (words5 (square_reader_rho az))).
 { eapply field_at_lframe;[exact Z|exact Frame|];intros;exact Logic.I. }
 exists mf;split;[exact Call|];split;[exact XO|];split;[exact YO|];split;[exact ZO|];split.
 - rewrite !mixed_reader_output,gej_add_right_infinite_value;[reflexivity| |].
   + change (@canonical_fe_is_zero Alg.CoreFunSem az=inl tt).
     destruct (@canonical_fe_is_zero Alg.CoreFunSem az) as [[] | []];[reflexivity|discriminate Fin].
   + change (@canonical_fe_is_zero Alg.CoreFunSem bz=inr tt).
     destruct (@canonical_fe_is_zero Alg.CoreFunSem bz) as [[] | []];[discriminate Inf|reflexivity].
 - split;[|exact Frame].
   intros pos Pos;apply (proj1 (proj2 Frame));[|exact Logic.I|apply Free;exact Pos].
   eapply Mem.perm_valid_block;apply (Free 0);lia.
Qed.
