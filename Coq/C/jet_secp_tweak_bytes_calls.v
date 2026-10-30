(** Byte-scalar tweak helper: actual parser call and both short-circuit exits. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns C.jet_secp_curve_statements C.jet_secp_tweak_bytes_entry
 C.jet_exec C.jet_readBit_layout C.jet_sx_expr.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Lemma exec_tweak_bytes_init e le m mf bf:
 e!_overflow=Some (bf,tint) ->Mem.store Mint32 m bf 0 (Vint Int.zero)=Some mf ->
 Clight2.exec_stmt secp_ge e le m tweak_bytes_init E0 le mf Out_normal.
Proof.
 intros Flag Store;unfold tweak_bytes_init;eapply exec_Sassign_value with
 (b:=bf) (ofs:=Ptrofs.zero) (v2:=Vint Int.zero) (v:=Vint Int.zero).
 - apply eval_Evar_local;exact Flag.
 - constructor.
 - reflexivity.
 - apply assign_loc_value with (chunk:=Mint32);[reflexivity|exact Store].
Qed.
Lemma exec_tweak_bytes_parse e le m mf bt bb bf:
 e!_term=Some (bt,Tstruct __5826 noattr) ->e!_overflow=Some (bf,tint) ->
 e!_secp256k1_scalar_set_b32=None ->le!_tweak32=Some (Vptr bb Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_set_b32)
 [Vptr bt Ptrofs.zero;Vptr bb Ptrofs.zero;Vptr bf Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m tweak_bytes_parse E0 le mf Out_normal.
Proof.
 intros Term Flag Symbol Bytes Call;unfold tweak_bytes_parse;eapply exec_curve_call with
 (vargs:=[Vptr bt Ptrofs.zero;Vptr bb Ptrofs.zero;Vptr bf Ptrofs.zero]) (v:=Vundef).
 - unfold secp_pure;repeat first [left;reflexivity|right].
 - exact Symbol.
 - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Term|reflexivity|].
   eapply eval_Econs;[apply eval_Etempvar;exact Bytes|reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Flag|reflexivity|constructor].
 - exact Call.
Qed.
Definition tweak_bytes_guard_temps (le:temp_env) (overflow result:bool):=
 if overflow then PTree.set _t'1 (Vint Int.zero) (PTree.set _t'3 (Vint Int.one) le)
 else PTree.set _t'1 (Vint (bit_int result))
 (PTree.set _t'2 (Vint (bit_int result)) (PTree.set _t'3 (Vint Int.zero) le)).
Lemma exec_tweak_bytes_guard_reject e le m bf:
 e!_overflow=Some (bf,tint) ->Mem.load Mint32 m bf 0=Some (Vint Int.one) ->
 Clight2.exec_stmt secp_ge e le m tweak_bytes_guard E0
 (tweak_bytes_guard_temps le true false) m Out_normal.
Proof.
 intros Flag Load;unfold tweak_bytes_guard,tweak_bytes_guard_temps.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'3 (Vint Int.one) le).
 - apply exec_Sset;eapply eval_Elvalue.
   + apply eval_Evar_local;exact Flag.
   + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|exact Load].
 - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
   + eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity].
   + reflexivity.
   + apply exec_Sset;constructor.
Qed.
Lemma exec_tweak_bytes_guard_accept e le m mf bt bk bf result:
 e!_term=Some (bt,Tstruct __5826 noattr) ->e!_overflow=Some (bf,tint) ->
 e!_secp256k1_eckey_pubkey_tweak_add=None ->le!_p=Some (Vptr bk Ptrofs.zero) ->
 Mem.load Mint32 m bf 0=Some (Vint Int.zero) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_eckey_pubkey_tweak_add)
 [Vptr bk Ptrofs.zero;Vptr bt Ptrofs.zero] E0 mf (Vint (bit_int result)) ->
 Clight2.exec_stmt secp_ge e le m tweak_bytes_guard E0
 (tweak_bytes_guard_temps le false result) mf Out_normal.
Proof.
 intros Term Flag Symbol Key Load Call;unfold tweak_bytes_guard,tweak_bytes_guard_temps.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'3 (Vint Int.zero) le).
 - apply exec_Sset;eapply eval_Elvalue.
   + apply eval_Evar_local;exact Flag.
   + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|exact Load].
 - eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
   + eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity].
   + reflexivity.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
      (le1:=PTree.set _t'2 (Vint (bit_int result)) (PTree.set _t'3 (Vint Int.zero) le)).
     * unfold tweak_bytes_native;eapply exec_curve_call with
       (vargs:=[Vptr bk Ptrofs.zero;Vptr bt Ptrofs.zero]) (v:=Vint (bit_int result)).
       -- unfold secp_pure;repeat first [left;reflexivity|right].
       -- exact Symbol.
       -- eapply eval_Econs.
          ++ apply eval_Etempvar;rewrite PTree.gso by discriminate;exact Key.
          ++ reflexivity.
          ++ eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Term|reflexivity|constructor].
       -- exact Call.
     * apply exec_Sset;eapply eval_Ecast.
       -- apply eval_Etempvar;apply PTree.gss.
       -- destruct result;reflexivity.
Qed.
Lemma exec_tweak_bytes_return e le m overflow result:
 Clight2.exec_stmt secp_ge e (tweak_bytes_guard_temps le overflow result) m tweak_bytes_return E0
 (tweak_bytes_guard_temps le overflow result) m
 (Out_return (Some (Vint (bit_int (if overflow then false else result)),tint))).
Proof.
 unfold tweak_bytes_return;apply exec_Sreturn_some;apply eval_Etempvar;
 destruct overflow;apply PTree.gss.
Qed.
