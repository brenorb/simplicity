(** Original rounded-product helper at the shift used by split_lambda.
    All statements are projections of the unchanged generated function. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix C.jet_secp_scalar_get_bits.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition shift384_parts := split_statement_last (fn_body f_secp256k1_scalar_mul_shift_var).
Definition shift384_product_statement := nth 1 (fst shift384_parts) Sskip.
Definition shift384_settings := statement_sequence (firstn 3 (skipn 2 (fst shift384_parts))) Sskip.
Definition shift384_copy_statement i := nth (5+i)%nat (fst shift384_parts) Sskip.
Definition shift384_round_load := nth 9 (fst shift384_parts) Sskip.
Definition shift384_round_call := snd shift384_parts.
Definition shift384_env bl := PTree.set _l (bl,tarray tulong 8) empty_env.
Definition shift384_settings_temps le := PTree.set _shifthigh (Vint (Int.repr 64))
 (PTree.set _shiftlow (Vint Int.zero) (PTree.set _shiftlimbs (Vint (Int.repr 6)) le)).

Lemma shift384_body_source : fn_body f_secp256k1_scalar_mul_shift_var=
 Ssequence (Sloop Sskip Sbreak) (Ssequence shift384_product_statement
 (statement_sequence (firstn 3 (skipn 2 (fst shift384_parts)))
 (Ssequence (shift384_copy_statement 0) (Ssequence (shift384_copy_statement 1)
 (Ssequence (shift384_copy_statement 2) (Ssequence (shift384_copy_statement 3)
 (Ssequence shift384_round_load shift384_round_call))))))).
Proof. reflexivity. Qed.

Local Ltac shift_lookup := first [eassumption|apply PTree.gss|rewrite PTree.gso by discriminate;shift_lookup].
Local Ltac shift_expr := first [apply eval_Etempvar;shift_lookup|apply eval_Econst_int|
 eapply eval_Ebinop;[shift_expr|shift_expr|reflexivity]].
Theorem exec_shift384_settings e le m : le!_shift=Some (Vint (Int.repr 384)) ->
 Clight2.exec_stmt secp_ge e le m shift384_settings E0 (shift384_settings_temps le) m Out_normal.
Proof.
 intro Shift.
 change (Clight2.exec_stmt secp_ge e le m
  (Ssequence (Sset _shiftlimbs (Ebinop Oshr (Etempvar _shift tuint) (Econst_int (Int.repr 6) tint) tuint))
  (Ssequence (Sset _shiftlow (Ebinop Oand (Etempvar _shift tuint) (Econst_int (Int.repr 63) tint) tuint))
  (Ssequence (Sset _shifthigh (Ebinop Osub (Econst_int (Int.repr 64) tint) (Etempvar _shiftlow tuint) tuint)) Sskip)))
  E0 (shift384_settings_temps le) m Out_normal).
 unfold shift384_settings_temps.
 repeat (eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m);[apply exec_Sset;shift_expr|]);constructor.
Qed.

Definition shift384_array_read (i:nat) := Ederef (Ebinop Oadd (Evar _l (tarray tulong 8))
 (Ebinop Oadd (Econst_int (Int.repr (Z.of_nat i)) tint) (Etempvar _shiftlimbs tuint) tuint) (tptr tulong)) tulong.
Definition shift384_dest (i:nat) := Ederef (Ebinop Oadd
 (Efield (Ederef (Etempvar _r (tptr (Tstruct __5826 noattr))) (Tstruct __5826 noattr)) _d (tarray tulong 4))
 (Econst_int (Int.repr (Z.of_nat i)) tint) (tptr tulong)) tulong.

Lemma eval_shift384_array e le m bl i word : (i<2)%nat ->
 e!_l=Some (bl,tarray tulong 8) -> le!_shiftlimbs=Some (Vint (Int.repr 6)) ->
 Mem.load Mint64 m bl (8*(6+Z.of_nat i))=Some (Vlong word) ->
 eval_expr secp_ge e le m (shift384_array_read i) (Vlong word).
Proof.
 intros Index Local Limbs Load;unfold shift384_array_read.
 eapply eval_Elvalue with (loc:=bl) (ofs:=Ptrofs.repr (8*(6+Z.of_nat i))).
 - apply eval_Ederef;eapply eval_Ebinop with (v1:=Vptr bl Ptrofs.zero) (v2:=Vint (Int.repr (6+Z.of_nat i))).
   + eapply eval_Elvalue;[apply eval_Evar_local;exact Local|apply deref_loc_reference;reflexivity].
   + eapply eval_Ebinop;[constructor|apply eval_Etempvar;exact Limbs|].
     destruct i as [|[|i]];try lia;reflexivity.
   + destruct i as [|[|i]];try lia;reflexivity.
 - apply deref_loc_value with (chunk:=Mint64);[reflexivity|].
   cbn [Mem.loadv];rewrite Ptrofs.unsigned_repr;[exact Load|].
   destruct i as [|[|i]];try lia;change Ptrofs.max_unsigned with 18446744073709551615;cbn;lia.
Qed.

Lemma eval_shift384_dest e le m br i : (i<4)%nat -> le!_r=Some (Vptr br Ptrofs.zero) ->
 eval_lvalue secp_ge e le m (shift384_dest i) br (Ptrofs.repr (8*Z.of_nat i)) Full.
Proof.
 intros Index R;unfold shift384_dest;destruct scalar_bits_d_layout as (co & Composite & Offset).
 apply eval_Ederef;eapply eval_Ebinop with (v1:=Vptr br Ptrofs.zero) (v2:=Vint (Int.repr (Z.of_nat i))).
 - rewrite <-(Ptrofs.add_zero Ptrofs.zero);eapply eval_Elvalue.
   + eapply eval_Efield_struct with (co:=co) (delta:=0) (ofs:=Ptrofs.zero).
     * eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact R|apply deref_loc_copy;reflexivity].
     * reflexivity.
     * exact Composite.
     * exact Offset.
   + apply deref_loc_reference;reflexivity.
 - constructor.
 - destruct i as [|[|[|[|i]]]];try lia;reflexivity.
Qed.
