(** Actual scalar-invert public read/invert/write/return statement tree. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Values Maps Memory Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_exec C.jet_sx_mem C.jet_sx_state C.jet_sx_exec
 C.jet_secp_linkage C.jets_secp C.jet_secp_frame C.jet_secp_wrapper_run
 C.jet_frame_layout C.jet_frame_inv C.jet_input_layout C.jet_output_layout C.jet_encoding
 C.jet_secp_public_body C.jet_secp_scalar_public_entry C.jet_secp_scalar_public_calls
 C.jet_secp_scalar_normalize_rest C.jet_secp_scalar_invert_literal
 C.jet_secp_scalar_invert_call_chain C.jet_secp_modinfo_scalar_initialized
 C.jet_clight_internal_preserve.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_invert_inplace_stmt :=
 match fn_body f_simplicity_scalar_invert with
 | Ssequence _ (Ssequence _ (Ssequence invert _))=>invert | _=>Sskip end.
Definition scalar_invert_rest :=
 match fn_body f_simplicity_scalar_invert with Ssequence _ rest=>rest | _=>Sskip end.
Lemma scalar_invert_rest_eq : scalar_invert_rest=Ssequence scalar_public_read_stmt
 (Ssequence scalar_invert_inplace_stmt
  (Ssequence scalar_normalize_write_stmt (Sreturn(Some(Econst_int(Int.repr 1)tint))))).
Proof. reflexivity. Qed.
Lemma scalar_invert_symbols :
 Genv.find_symbol secp_ge _secp256k1_scalar_inverse_var=Some(secp_symbol_block _secp256k1_scalar_inverse_var) /\
 Genv.find_funct secp_ge (Vptr(secp_symbol_block _secp256k1_scalar_inverse_var)Ptrofs.zero)=
  Some(Internal f_secp256k1_scalar_inverse_var).
Proof. vm_compute;split;reflexivity. Qed.
Local Opaque secp_ge literal_scalar_invert encode.

Lemma exec_scalar_invert_inplace le m mf bl ba :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_inverse_var)
  [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (scalar_public_env bl ba) le m scalar_invert_inplace_stmt E0 le mf Out_normal.
Proof.
 intro Call;destruct scalar_invert_symbols as[Symbol Function].
 eapply exec_Scall with(vf:=Vptr(secp_symbol_block _secp256k1_scalar_inverse_var)Ptrofs.zero)
  (vargs:=[Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero])
  (f:=Internal f_secp256k1_scalar_inverse_var)(vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue.
   + eapply eval_Evar_global;[reflexivity|exact Symbol].
   + apply deref_loc_reference;reflexivity.
 - eapply eval_Econs.
   + apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
   + reflexivity.
   + eapply eval_Econs.
     * apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
     * reflexivity.
     * apply eval_Enil.
 - exact Function.
 - reflexivity.
 - exact Call.
Qed.

Theorem exec_scalar_invert_rest le m0 bd dbase bw outedge cursor N bi edge rc
 (value:Ty.tySem(Word 8)) m ba bl :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 le!_dst=Some(Vptr bd(Ptrofs.repr dbase)) ->
 write_frame_at m0 bd dbase bw outedge cursor N ->
 frame_input_cells_at m0 bi edge rc (map Some(frame_input_word_bits value)) ->
 0<=rc -> rc+256<=Int64.max_unsigned ->
 Mem.range_perm m ba 0 32 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
 frame_fields_at m bl 0 bi edge rc -> ba<>bl ->
 xsep(extA m0 bd bw bi)[(ba,0);(bl,0)] ->
 invA m0 bd dbase bw outedge cursor N bi rc false [] 256
  (read_fe_rho(frame_input_word_bits value)rc) [] m ->
 modinfo_scalar_initialized m -> exists mf,
 Clight2.exec_stmt secp_ge (scalar_public_env bl ba) le m scalar_invert_rest E0 le mf
  (Out_return(Some(Vint Int.one,tint))) /\
 finv m0 bd dbase bw outedge cursor N bi mf true
  (encode(@literal_scalar_invert Alg.CoreFunSem value)) /\
 Mem.range_perm mf ba 0 32 Cur Freeable /\ Mem.range_perm mf bl 0 16 Cur Freeable /\
 lframe(secp_locals_outside m0 bd bw bi ba bl) m mf /\
 modinfo_scalar_initialized mf /\ readonly_preserved m mf.
Proof.
 intros CountCall HD HO HI Hrc HM HA HL HS Separate Sep Inv Ready.
 destruct(eval_scalar_read_invert_write m0 bd dbase bw outedge cursor N bi edge rc value m ba bl
  CountCall HO HI Hrc HM HA HL HS Separate Sep Inv Ready)
  as(mr & mn & mf & Read & Inverse & Write & Final & FreeA & Cursor & FreeL & Frame & ReadyF & Preserved).
 exists mf;split.
 - rewrite scalar_invert_rest_eq.
   eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mr)(le1:=le).
   + apply exec_scalar_public_read;exact Read.
   + eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mn)(le1:=le).
     * apply exec_scalar_invert_inplace;exact Inverse.
     * eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mf)(le1:=le).
       -- eapply exec_scalar_normalize_write;[exact HD|exact Write].
       -- apply exec_Sreturn_some;constructor.
 - split;[exact Final|];split;[exact FreeA|];split;[exact FreeL|];
   split;[exact Frame|];split;assumption.
Qed.
