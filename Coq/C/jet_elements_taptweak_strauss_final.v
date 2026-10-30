(** Retain the stored infinity flag through the actual final Z correction
    when the shared denominator is nonzero. The caller must derive that
    internal condition from its valid affine input, not assume it publicly. *)
From Coq Require Import ZArith Lia List.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_sx_mem C.jet_readBit_layout C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_curve_statements
 C.jet_secp_curve_frame C.jet_secp_rescale_statements C.jet_secp_rescale_literal
 C.jet_secp_strauss_final_literal C.jet_secp_generator_final C.jet_secp_multiply_literal_spec
 C.jet_secp_curve_literal C.jet_secp_canonical_zero C.jet_secp_negate_literal_contract C.jet_secp_field_prime.
Import Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output literal_fe_multiply canonical_fe_is_zero.

(** Original final Z correction in the linked Elements program. Domain and
    bound-local obligations are internal and discharged at the real entry. *)
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_strauss_final_literal C.jet_secp_strauss_final_flag
 C.jet_secp_generator_final C.jet_secp_curve_statements C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_curve_transport C.jet_elements_taptweak_strauss_transport
 C.jet_transport C.jet_transport_locals.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_strauss_final_checked:
 locals_stmt_okb secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf))generator_final_statement=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_curve_helpers.
Lemma elements_taptweak_strauss_final_transport e le m trace lef mf out:
 edom e(fn_vars f_secp256k1_ecmult_strauss_wnaf) ->
 (forall id,In id(map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)) ->exists b ty,e!id=Some(b,ty)) ->
 Clight2.exec_stmt secp_ge e le m generator_final_statement trace lef mf out ->
 Clight2.exec_stmt elements_taptweak_ge e le m generator_final_statement trace lef mf out.
Proof.
 intros Domain Bound Run.
 eapply(proj1(locals_transport_main secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (locals_transportable_of_entries secp_ge elements_taptweak_ge elements_taptweak_curve_helpers
 elements_taptweak_curve_entries elements_taptweak_curve_ok)));
 [exact Run|exact Domain|exact Bound|exact elements_taptweak_strauss_final_checked].
Qed.
Theorem exec_elements_taptweak_strauss_final_any x y z inv e le m bp bb flag :
 edom e(fn_vars f_secp256k1_ecmult_strauss_wnaf) ->
 (forall id,In id(map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)) ->exists b ty,e!id=Some(b,ty)) ->
 le!_r=Some (Vptr bp Ptrofs.zero) -> e!_Z=Some (bb,curve_fe_type) -> e!_secp256k1_fe_mul=None -> bp<>bb ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds inv ->
  Mem.load Mint32 m bp 120=Some (Vint flag) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m bb 0 (words5 inv) -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> exists mf oz,
 Clight2.exec_stmt elements_taptweak_ge e le m generator_final_statement E0 (PTree.set _t'16 (Vint flag) le) mf Out_normal /\
 fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 oz) /\
 Mem.load Mint32 mf bp 120=Some (Vint flag) /\ fe_at mf bb 0 (words5 inv) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
 square_input_bounds oz /\ rescale_field_output oz=
 (if Int.eq flag Int.zero then @literal_fe_multiply Alg.CoreFunSem (rescale_field_output z,rescale_field_output inv) else rescale_field_output z) /\
 lframe (fun b _=>b<>bp /\ b<>bb) m mf.
Proof.
 intros Domain Bound R ZLocal MulSymbol Separate BX BY BZ BI Flag X Y ZAt Inv FreeR FreeI.
 destruct(exec_strauss_final_any x y z inv e le m bp bb flag R ZLocal MulSymbol Separate BX BY BZ BI Flag X Y ZAt Inv FreeR FreeI)
 as(mf & oz & Run & XO & YO & ZO & FlagO & InvO & FreeRO & FreeIO & Bounds & Literal & Frame).
 exists mf,oz;split;[eapply elements_taptweak_strauss_final_transport;[exact Domain|exact Bound|exact Run]|].
 repeat first[assumption|split].
Qed.
Theorem exec_elements_taptweak_strauss_final_literal x y z inv e le m bp bb :
 edom e(fn_vars f_secp256k1_ecmult_strauss_wnaf) ->
 (forall id,In id(map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)) ->exists b ty,e!id=Some(b,ty)) ->
 le!_r=Some (Vptr bp Ptrofs.zero) -> e!_Z=Some (bb,curve_fe_type) -> e!_secp256k1_fe_mul=None -> bp<>bb ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds inv ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output z))))) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m bb 0 (words5 inv) -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> exists mf oz,
 Clight2.exec_stmt elements_taptweak_ge e le m generator_final_statement E0
  (PTree.set _t'16 (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output z))))) le) mf Out_normal /\
 fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 oz) /\
 Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output z))))) /\
 fe_at mf bb 0 (words5 inv) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
 square_input_bounds oz /\
 rescale_field_output oz=@literal_fe_multiply Alg.CoreFunSem (rescale_field_output z,rescale_field_output inv) /\
 lframe (fun b _=>b<>bp /\ b<>bb) m mf.
Proof.
 intros Domain Bound R ZLocal MulSymbol Separate BX BY BZ BI Flag X Y ZAt Inv FreeR FreeI.
 destruct(exec_strauss_final_literal x y z inv e le m bp bb R ZLocal MulSymbol Separate BX BY BZ BI Flag X Y ZAt Inv FreeR FreeI)
 as(mf & oz & Run & XO & YO & ZO & FlagO & InvO & FreeRO & FreeIO & Bounds & Literal & Frame).
 exists mf,oz;split;[eapply elements_taptweak_strauss_final_transport;[exact Domain|exact Bound|exact Run]|].
 repeat first[assumption|split].
Qed.
Theorem exec_elements_taptweak_strauss_final_flag x y z inv e le m bp bb :
 edom e(fn_vars f_secp256k1_ecmult_strauss_wnaf) ->
 (forall id,In id(map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)) ->exists b ty,e!id=Some(b,ty)) ->
 le!_r=Some (Vptr bp Ptrofs.zero) -> e!_Z=Some (bb,curve_fe_type) -> e!_secp256k1_fe_mul=None -> bp<>bb ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds inv ->
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output inv))=false ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output z))))) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m bb 0 (words5 inv) -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> exists mf oz,
 Clight2.exec_stmt elements_taptweak_ge e le m generator_final_statement E0
  (PTree.set _t'16 (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output z))))) le) mf Out_normal /\
 fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 oz) /\
 Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 fe_at mf bb 0 (words5 inv) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
 square_input_bounds oz /\
 rescale_field_output oz=@literal_fe_multiply Alg.CoreFunSem (rescale_field_output z,rescale_field_output inv) /\
 lframe (fun b _=>b<>bp /\ b<>bb) m mf.
Proof.
 intros Domain Bound R ZLocal MulSymbol Separate BX BY BZ BI Nonzero Flag X Y ZAt Inv FreeR FreeI.
 destruct(exec_strauss_final_flag x y z inv e le m bp bb R ZLocal MulSymbol Separate BX BY BZ BI Nonzero Flag X Y ZAt Inv FreeR FreeI)
 as(mf & oz & Run & XO & YO & ZO & FlagO & InvO & FreeRO & FreeIO & Bounds & Literal & Frame).
 exists mf,oz;split;[eapply elements_taptweak_strauss_final_transport;[exact Domain|exact Bound|exact Run]|].
 repeat first[assumption|split].
Qed.
