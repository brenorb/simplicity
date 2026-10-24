(** The original public field-invert read/inverse/write/return statement tree. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Values Maps Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_sx_mem C.jet_sx_state C.jet_sx_exec C.jet_secp_linkage C.jets_secp
 C.jet_secp_fns C.jet_secp_curve_statements C.jet_secp_frame C.jet_secp_wrapper_run
 C.jet_frame_layout C.jet_frame_inv C.jet_input_layout C.jet_output_layout C.jet_encoding
 C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_invert_literal
 C.jet_secp_fe_invert_call_chain C.jet_secp_modinfo_fe_caller C.jet_clight_internal_preserve.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition field_invert_inplace_stmt := match fn_body f_simplicity_fe_invert with
 | Ssequence _ (Ssequence _ (Ssequence invert _))=>invert | _=>Sskip end.
Definition field_invert_rest := match fn_body f_simplicity_fe_invert with Ssequence _ rest=>rest | _=>Sskip end.
Lemma field_invert_rest_eq : field_invert_rest=Ssequence secp_public_read_stmt
 (Ssequence field_invert_inplace_stmt
  (Ssequence secp_public_write_stmt(Sreturn(Some(Econst_int(Int.repr 1)tint))))).
Proof. reflexivity. Qed.
Lemma field_invert_inplace_source : field_invert_inplace_stmt=
 curve_call _secp256k1_fe_inv_var f_secp256k1_fe_inv_var None
 [Eaddrof(Evar _a secp_field_type)(tptr secp_field_type);Eaddrof(Evar _a secp_field_type)(tptr secp_field_type)].
Proof. reflexivity. Qed.
Local Opaque secp_ge literal_fe_invert encode.
Lemma exec_public_field_invert le m mf bl ba :
 Clight2.eval_funcall secp_ge m(Internal f_secp256k1_fe_inv_var)
  [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge(secp_public_env bl ba)le m field_invert_inplace_stmt E0 le mf Out_normal.
Proof.
 intro Call;rewrite field_invert_inplace_source;eapply exec_curve_call with
  (vargs:=[Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero])(v:=Vundef).
 - unfold secp_pure;repeat(first[left;reflexivity|right]).
 - reflexivity.
 - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
 - exact Call.
Qed.

Theorem exec_field_invert_rest le m0 bd dbase bw outedge cursor N bi edge rc
 (value:Ty.tySem(Word 8)) m ba bl :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 le!_dst=Some(Vptr bd(Ptrofs.repr dbase)) -> write_frame_at m0 bd dbase bw outedge cursor N ->
 frame_input_cells_at m0 bi edge rc(map Some(frame_input_word_bits value)) ->
 0<=rc -> rc+256<=Int64.max_unsigned ->
 Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
 frame_fields_at m bl 0 bi edge rc -> ba<>bl -> xsep(extA m0 bd bw bi)[(ba,0);(bl,0)] ->
 invA m0 bd dbase bw outedge cursor N bi rc false [] 256(read_fe_rho(frame_input_word_bits value)rc)[]m ->
 modinfo_fe_state m -> exists mf,
 Clight2.exec_stmt secp_ge(secp_public_env bl ba)le m field_invert_rest E0 le mf
  (Out_return(Some(Vint Int.one,tint))) /\
 finv m0 bd dbase bw outedge cursor N bi mf true(encode(@literal_fe_invert Alg.CoreFunSem value)) /\
 Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bl 0 16 Cur Freeable /\
 lframe(secp_locals_outside m0 bd bw bi ba bl)m mf /\ modinfo_fe_state mf /\ readonly_preserved m mf.
Proof.
 intros CountCall HD HO HI Hrc HM HA HL HS Separate Sep Inv Ready.
 destruct(eval_field_read_invert_write m0 bd dbase bw outedge cursor N bi edge rc value m ba bl
  CountCall HO HI Hrc HM HA HL HS Separate Sep Inv Ready)
  as(mr & mn & mf & Read & Inverse & Write & Final & FreeA & FreeL & Frame & ReadyF & Preserved).
 exists mf;split.
 - rewrite field_invert_rest_eq;eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mr)(le1:=le).
   + apply exec_secp_public_read;exact Read.
   + eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mn)(le1:=le).
     * apply exec_public_field_invert;exact Inverse.
     * eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mf)(le1:=le).
       -- eapply exec_secp_public_write;[exact HD|exact Write].
       -- apply exec_Sreturn_some;constructor.
 - split;[exact Final|];split;[exact FreeA|];split;[exact FreeL|];split;[exact Frame|];split;assumption.
Qed.
