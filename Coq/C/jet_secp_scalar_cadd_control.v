(** Original scalar_cadd_bit(r,0,flag) sequence and argument evaluation.
    The two flags are exactly those produced by mul_shift_var's round bit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix C.jet_secp_curve_statements.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition cadd_spine := fst (split_statement_last (fn_body f_secp256k1_scalar_cadd_bit)).
Definition cadd_last := snd (split_statement_last (fn_body f_secp256k1_scalar_cadd_bit)).
Definition cadd_prefix_spine := firstn 3 cadd_spine.
Definition cadd_prefix_statement := statement_sequence cadd_prefix_spine Sskip.
Definition cadd_selector_statement j := nth (3+4*j)%nat cadd_spine Sskip.
Definition cadd_gap_spine j := firstn 3 (skipn (4+4*j)%nat cadd_spine).
Definition cadd_gap_statement j := statement_sequence (cadd_gap_spine j) Sskip.
Definition cadd_tail := statement_sequence (skipn 16 cadd_spine) cadd_last.

Definition cadd_selector_expr j := Ebinop Oshl
 (Ecast (Ebinop Oeq (Ebinop Oshr (Etempvar _bit tuint) (Econst_int (Int.repr 6) tint) tuint)
   (Econst_int (Int.repr (Z.of_nat j)) tint) tint) tulong)
 (Ebinop Oand (Etempvar _bit tuint) (Econst_int (Int.repr 63) tint) tuint) tulong.
Definition cadd_t_address := Eaddrof (Evar _t (Tstruct _secp256k1_uint128 noattr))
 (tptr (Tstruct _secp256k1_uint128 noattr)).
Definition cadd_bit_setting (flag:bool) := if flag then Int.zero else Int.repr 256.
Definition cadd_selector_value (flag:bool) (j:nat) := if (flag && Nat.eqb j 0)%bool then Int64.one else Int64.zero.

Lemma cadd_selector_source j : (j<4)%nat -> cadd_selector_statement j=
 curve_call _secp256k1_u128_accum_u64 f_secp256k1_u128_accum_u64 None [cadd_t_address;cadd_selector_expr j].
Proof. intro J;destruct j as [|[|[|[|j]]]];try lia;reflexivity. Qed.

Lemma cadd_body_source : statement_sequence cadd_prefix_spine
 (Ssequence (cadd_selector_statement 0) (statement_sequence (cadd_gap_spine 0)
 (Ssequence (cadd_selector_statement 1) (statement_sequence (cadd_gap_spine 1)
 (Ssequence (cadd_selector_statement 2) (statement_sequence (cadd_gap_spine 2)
 (Ssequence (cadd_selector_statement 3) cadd_tail)))))))=fn_body f_secp256k1_scalar_cadd_bit.
Proof. reflexivity. Qed.

Lemma eval_cadd_t_address e le m bt : e!_t=Some (bt,Tstruct _secp256k1_uint128 noattr) ->
 eval_expr secp_ge e le m cadd_t_address (Vptr bt Ptrofs.zero).
Proof. intro T;unfold cadd_t_address;apply eval_Eaddrof;apply eval_Evar_local;exact T. Qed.

Lemma eval_cadd_bit_index e le m flag : le!_bit=Some (Vint (cadd_bit_setting flag)) ->
 eval_expr secp_ge e le m
 (Ebinop Oshr (Etempvar _bit tuint) (Econst_int (Int.repr 6) tint) tuint)
 (Vint (Int.repr (if flag then 0 else 4))).
Proof.
 intro Bit;eapply eval_Ebinop with (v1:=Vint (cadd_bit_setting flag)) (v2:=Vint (Int.repr 6));
 [apply eval_Etempvar;exact Bit|constructor|destruct flag;reflexivity].
Qed.
Lemma eval_cadd_bit_offset e le m flag : le!_bit=Some (Vint (cadd_bit_setting flag)) ->
 eval_expr secp_ge e le m
 (Ebinop Oand (Etempvar _bit tuint) (Econst_int (Int.repr 63) tint) tuint) (Vint Int.zero).
Proof.
 intro Bit;eapply eval_Ebinop with (v1:=Vint (cadd_bit_setting flag)) (v2:=Vint (Int.repr 63));
 [apply eval_Etempvar;exact Bit|constructor|destruct flag;reflexivity].
Qed.

Lemma eval_cadd_selector_expr e le m flag j : (j<4)%nat -> le!_bit=Some (Vint (cadd_bit_setting flag)) ->
 eval_expr secp_ge e le m (cadd_selector_expr j) (Vlong (cadd_selector_value flag j)).
Proof.
 intros J Bit;unfold cadd_selector_expr.
 eapply eval_Ebinop with (v1:=Vlong (cadd_selector_value flag j)) (v2:=Vint Int.zero).
 - eapply eval_Ecast with (v1:=Vint (if (flag && Nat.eqb j 0)%bool then Int.one else Int.zero)).
   + eapply eval_Ebinop with (v1:=Vint (Int.repr (if flag then 0 else 4)))
     (v2:=Vint (Int.repr (Z.of_nat j))).
     * exact (eval_cadd_bit_index e le m flag Bit).
     * constructor.
     * destruct j as [|[|[|[|j]]]];try lia;destruct flag;reflexivity.
   + destruct j as [|[|[|[|j]]]];try lia;destruct flag;reflexivity.
 - exact (eval_cadd_bit_offset e le m flag Bit).
 - destruct j as [|[|[|[|j]]]];try lia;destruct flag;reflexivity.
Qed.
