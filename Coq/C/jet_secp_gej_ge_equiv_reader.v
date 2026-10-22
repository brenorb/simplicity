(** Specialize the actual C helper to arbitrary Word256 reader results.
    The returned bit is a C-derived model, not the Simplicity specification. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_gej_ge_equiv_function C.jet_secp_mixed_body_loose C.jet_secp_mixed_finite_return
 C.jet_secp_mixed_zero_return C.jet_secp_double_var_owned C.jet_secp_field_weak_loose
 C.jet_secp_square_spec_bridge C.jet_secp_field_weak_tight C.jet_secp_multiply_input_input
 C.jet_secp_multiply_normalize_bridge C.jet_secp_canonical_zero C.jet_secp_canonical_normalize.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_is_zero canonical_fe_normalize normalized_value.

Definition gej_ge_equiv_bit x value z u v flag := Int.eq (gej_ge_equiv_result x value z u v flag) Int.one.

Lemma gej_ge_equiv_result_cases x value z u v flag :
 gej_ge_equiv_result x value z u v flag=Int.one \/ gej_ge_equiv_result x value z u v flag=Int.zero.
Proof.
 unfold gej_ge_equiv_result,mixed_loose_body_flag,mixed_loose_finite_flag,mixed_zero_flag,double_var_zflag.
 repeat match goal with |- context[if ?b then _ else _]=>destruct b end;auto.
Qed.
Lemma gej_ge_equiv_result_bit x value z u v flag :
 gej_ge_equiv_result x value z u v flag=if gej_ge_equiv_bit x value z u v flag then Int.one else Int.zero.
Proof.
 destruct (gej_ge_equiv_result_cases x value z u v flag) as [Eq|Eq];
  unfold gej_ge_equiv_bit;rewrite Eq;reflexivity.
Qed.

Definition gej_ge_equiv_reader_bit (x y z u v : Ty.tySem (Word 8)) :=
 gej_ge_equiv_bit (square_reader_rho x) (normalized_value y) (square_reader_rho z)
  (square_reader_rho u) (square_reader_rho v) (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z))).

Theorem eval_gej_ge_equiv_reader (x y z u v : Ty.tySem (Word 8)) m bp ba :
 bp<>ba ->
 fe_at m bp 0 (words5 (square_reader_rho x)) -> fe_at m bp 40 (words5 (square_reader_rho y)) ->
 fe_at m bp 80 (words5 (square_reader_rho z)) ->
 fe_at m ba 0 (words5 (square_reader_rho u)) -> fe_at m ba 40 (words5 (square_reader_rho v)) ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)))) ->
 Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_eq_ge_var)
  [Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf
  (Vint (if gej_ge_equiv_reader_bit x y z u v then Int.one else Int.zero)) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 lframe (fun b _=>b<>bp /\ b<>ba) m mf.
Proof.
 intros Sep X Y Z U V FlagA FlagB FreeP FreeA.
 destruct (eval_gej_ge_equiv_function (square_reader_rho x) (normalized_value y) (square_reader_rho z)
  (square_reader_rho u) (square_reader_rho v) (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z))) m bp ba
  Sep (normalized_value_range y) (square_reader_positioned x) (square_reader_bounds z)
  (square_reader_bounds u) (square_reader_bounds v) FlagA FlagB X Y Z U V FreeP FreeA)
  as (mf & Call & FP & FA & Frame).
 rewrite gej_ge_equiv_result_bit in Call.
 exists mf;split;[exact Call|];split;[exact FP|];split;assumption.
Qed.
