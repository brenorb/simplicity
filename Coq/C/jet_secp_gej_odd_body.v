(** Exact original public parity statement tree and actual call adapters. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_readBit_layout C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_gej_odd_entry
 C.jet_secp_curve_statements C.jet_secp_gej_predicate_body C.jet_secp_gej_flag_read C.jet_secp_gej_norm_preserve.
Require C.jets.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition gej_odd_y_address := Eaddrof(Efield(Evar _b curve_ge_type)_y curve_fe_type)(tptr curve_fe_type).
Definition gej_odd_flag_stmt := curve_call _secp256k1_gej_is_infinity f_secp256k1_gej_is_infinity(Some _t'2)
 [Eaddrof(Evar _a(Tstruct __6123 noattr))(tptr(Tstruct __6123 noattr))].
Definition gej_odd_affine_stmt := curve_call _secp256k1_ge_set_gej_var f_secp256k1_ge_set_gej_var None
 [Eaddrof(Evar _b curve_ge_type)(tptr curve_ge_type);
  Eaddrof(Evar _a(Tstruct __6123 noattr))(tptr(Tstruct __6123 noattr))].
Definition gej_odd_normalize_stmt := curve_call _secp256k1_fe_normalize_var f_secp256k1_fe_normalize_var None[gej_odd_y_address].
Definition gej_odd_parity_stmt := curve_call _secp256k1_fe_is_odd f_secp256k1_fe_is_odd(Some _t'1)[gej_odd_y_address].
Definition gej_odd_write_stmt argument := Scall None(Evar _writeBit(type_of_function C.jets.f_writeBit))
 [Etempvar _dst(tptr(Tstruct _frameItem noattr));argument].
Definition gej_odd_finite_stmt := Ssequence gej_odd_affine_stmt(Ssequence gej_odd_normalize_stmt
 (Ssequence gej_odd_parity_stmt(gej_odd_write_stmt(Etempvar _t'1 tint)))).
Definition gej_odd_branch := Sifthenelse(Etempvar _t'2 tint)
 (gej_odd_write_stmt(Econst_int Int.zero tint))gej_odd_finite_stmt.
Definition gej_odd_after_read := Ssequence(Ssequence gej_odd_flag_stmt gej_odd_branch)
 (Sreturn(Some(Econst_int Int.one tint))).
Definition gej_odd_flagged le infinity := PTree.set _t'2(Vint(bit_int infinity))le.
Definition gej_odd_parity_temps le bit := PTree.set _t'1(Vint(bit_int bit))le.

Lemma gej_odd_body_source : fn_body f_simplicity_gej_y_is_odd=
 Ssequence(Sassign(Evar _src(Tstruct _frameItem noattr))(Etempvar _src(Tstruct _frameItem noattr)))
 (Ssequence gej_predicate_read_stmt gej_odd_after_read).
Proof. reflexivity. Qed.

Lemma eval_gej_odd_y_address le m bl bp br :
 eval_expr secp_ge(gej_odd_env bl bp br)le m gej_odd_y_address(Vptr br(Ptrofs.repr 40)).
Proof.
 destruct(curve_affine_layout _y 40 ltac:(right;left;reflexivity)) as(co & Env & Offset).
 unfold gej_odd_y_address;apply eval_Eaddrof.
 rewrite <-(Ptrofs.add_zero_l(Ptrofs.repr 40));eapply eval_Efield_struct with(co:=co)(delta:=40).
 - eapply eval_Elvalue;[apply eval_Evar_local;reflexivity|apply deref_loc_copy;reflexivity].
 - reflexivity.
 - exact Env.
 - exact Offset.
Qed.

Lemma exec_gej_odd_read le m mf bl bp br :
 Clight2.eval_funcall secp_ge m(Internal f_read_gej)[Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero]E0 mf Vundef ->
 Clight2.exec_stmt secp_ge(gej_odd_env bl bp br)le m gej_predicate_read_stmt E0 le mf Out_normal.
Proof.
 intro Read;destruct gej_predicate_reader_symbol as(bf & Symbol & Funct).
 unfold gej_predicate_read_stmt;eapply exec_Scall with(vf:=Vptr bf Ptrofs.zero)
  (f:=Internal f_read_gej)(vargs:=[Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero])(vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact Symbol]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
 - change(Genv.find_funct_ptr secp_ge bf=Some(Internal f_read_gej));exact Funct.
 - reflexivity.
 - exact Read.
Qed.

Lemma exec_gej_odd_flag le m bl bp br infinity :
 Mem.load Mint32 m bp 120=Some(Vint(bit_int infinity)) ->
 Clight2.exec_stmt secp_ge(gej_odd_env bl bp br)le m gej_odd_flag_stmt E0
  (gej_odd_flagged le infinity)m Out_normal.
Proof.
 intro Flag;unfold gej_odd_flag_stmt,gej_odd_flagged;eapply exec_curve_call with
  (vargs:=[Vptr bp Ptrofs.zero])(v:=Vint(bit_int infinity)).
 - unfold secp_pure;repeat(first[left;reflexivity|right]).
 - reflexivity.
 - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
 - apply(eval_gej_flag_accessor m bp 0(bit_int infinity));[lia|change(128<=18446744073709551615);lia|exact Flag].
Qed.

Lemma exec_gej_odd_write le m mf bl bp br bd base argument bit :
 le!_dst=Some(Vptr bd(Ptrofs.repr base)) -> typeof argument=tint ->
 eval_expr secp_ge(gej_odd_env bl bp br)le m argument(Vint(bit_int bit)) ->
 Clight2.eval_funcall secp_ge m(Internal C.jets.f_writeBit)
  [Vptr bd(Ptrofs.repr base);Vint(bit_int bit)]E0 mf(Vint(bit_int bit)) ->
 Clight2.exec_stmt secp_ge(gej_odd_env bl bp br)le m(gej_odd_write_stmt argument)E0 le mf Out_normal.
Proof.
 intros Dst ArgType Value Write;unfold gej_odd_write_stmt.
 eapply exec_Scall with(vf:=Vptr(secp_symbol_block _writeBit)Ptrofs.zero)
  (f:=Internal C.jets.f_writeBit)(vargs:=[Vptr bd(Ptrofs.repr base);Vint(bit_int bit)])(vres:=Vint(bit_int bit)).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact(proj1 secp_writeBit_link)]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs;[apply eval_Etempvar;exact Dst|reflexivity|].
   eapply eval_Econs;[exact Value|rewrite ArgType;destruct bit;reflexivity|constructor].
 - exact(proj2 secp_writeBit_link).
 - reflexivity.
 - exact Write.
Qed.

Lemma exec_gej_odd_finite_from_calls le m ma mn mo mf bl bp br bd base bit :
 le!_dst=Some(Vptr bd(Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge m(Internal f_secp256k1_ge_set_gej_var)
  [Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero]E0 ma Vundef ->
 Clight2.eval_funcall secp_ge ma(Internal f_secp256k1_fe_normalize_var)[Vptr br(Ptrofs.repr 40)]E0 mn Vundef ->
 Clight2.eval_funcall secp_ge mn(Internal f_secp256k1_fe_is_odd)[Vptr br(Ptrofs.repr 40)]E0 mo(Vint(bit_int bit)) ->
 Clight2.eval_funcall secp_ge mo(Internal C.jets.f_writeBit)
  [Vptr bd(Ptrofs.repr base);Vint(bit_int bit)]E0 mf(Vint(bit_int bit)) ->
 Clight2.exec_stmt secp_ge(gej_odd_env bl bp br)le m gej_odd_finite_stmt E0
  (gej_odd_parity_temps le bit)mf Out_normal.
Proof.
 intros Dst Affine Normalize Odd Write;unfold gej_odd_finite_stmt.
 eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=ma)(le1:=le).
 - unfold gej_odd_affine_stmt;eapply exec_curve_call with(vargs:=[Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero])(v:=Vundef).
   + unfold secp_pure;repeat(first[left;reflexivity|right]).
   + reflexivity.
   + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
   + exact Affine.
 - eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mn)(le1:=le).
   + unfold gej_odd_normalize_stmt;eapply exec_curve_call with(vargs:=[Vptr br(Ptrofs.repr 40)])(v:=Vundef).
     * unfold secp_pure;repeat(first[left;reflexivity|right]).
     * reflexivity.
     * eapply eval_Econs;[apply eval_gej_odd_y_address|reflexivity|constructor].
     * exact Normalize.
   + eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mo)(le1:=gej_odd_parity_temps le bit).
     * unfold gej_odd_parity_stmt,gej_odd_parity_temps;eapply exec_curve_call with
       (vargs:=[Vptr br(Ptrofs.repr 40)])(v:=Vint(bit_int bit)).
       -- unfold secp_pure;repeat(first[left;reflexivity|right]).
       -- reflexivity.
       -- eapply eval_Econs;[apply eval_gej_odd_y_address|reflexivity|constructor].
       -- exact Odd.
     * apply(exec_gej_odd_write(gej_odd_parity_temps le bit)mo mf bl bp br bd base(Etempvar _t'1 tint)bit).
       -- unfold gej_odd_parity_temps;rewrite PTree.gso by discriminate;exact Dst.
       -- reflexivity.
       -- apply eval_Etempvar;unfold gej_odd_parity_temps;apply PTree.gss.
       -- exact Write.
Qed.
