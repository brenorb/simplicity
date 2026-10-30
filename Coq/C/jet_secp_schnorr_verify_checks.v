(** Actual signature/message/key pointer checks at the original verifier entry. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements C.jet_secp_statement_prefix C.jet_clight_nonnull_guard C.jet_secp_root_chain_owned.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition schnorr_verify_message_check:=Sloop
 (Ssequence
  (Sifthenelse (Ebinop One (Etempvar _msg (tptr tuchar))
   (Ecast (Econst_int Int.zero tint) (tptr tvoid)) tint)
   (Sset _t'1 (Econst_int Int.one tint))
   (Sset _t'1 (Ecast (Ebinop Oeq (Etempvar _msglen tulong) (Econst_int Int.zero tint) tint) tbool)))
  (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
   (Sreturn (Some (Econst_int Int.zero tint))) Sskip)) Sbreak.
Definition schnorr_verify_checks:=
 [nonnull_return_zero _sig64 tuchar;schnorr_verify_message_check;
  nonnull_return_zero _pubkey (Tstruct __6478 noattr)].
Definition schnorr_verify_checked_temps le:=PTree.set _t'1 (Vint Int.one) le.
Lemma schnorr_verify_checks_source:fn_body f_secp256k1_schnorrsig_verify=
 statement_sequence schnorr_verify_checks (root_drop_statements 3 (fn_body f_secp256k1_schnorrsig_verify)).
Proof. reflexivity. Qed.
Theorem exec_schnorr_verify_message_check e le m b ofs:
 le!_msg=Some (Vptr b ofs) ->Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs)=true ->
 Clight2.exec_stmt secp_ge e le m schnorr_verify_message_check E0 (schnorr_verify_checked_temps le) m Out_normal.
Proof.
 intros Msg Valid;unfold schnorr_verify_message_check.
 change E0 with (E0**E0);eapply exec_Sloop_stop2 with (out1:=Out_normal) (out2:=Out_break).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=schnorr_verify_checked_temps le).
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|apply exec_Sset;constructor].
     eapply eval_Ebinop with (v1:=Vptr b ofs) (v2:=Vlong Int64.zero).
     * apply eval_Etempvar;exact Msg.
     * eapply eval_Ecast;[constructor|reflexivity].
     * change (option_map Val.of_bool
       (if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some true else None)=Some (Vint Int.one)).
       rewrite Valid;reflexivity.
   + eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
     eapply eval_Eunop;[apply eval_Etempvar;unfold schnorr_verify_checked_temps;apply PTree.gss|reflexivity].
 - constructor.
 - constructor.
 - constructor.
Qed.
Theorem exec_schnorr_verify_checks e le m bsig bmsg omsg bkey okey:
 le!_sig64=Some (Vptr bsig Ptrofs.zero) ->le!_msg=Some (Vptr bmsg omsg) ->le!_pubkey=Some (Vptr bkey okey) ->
 Mem.weak_valid_pointer m bsig 0=true ->Mem.weak_valid_pointer m bmsg (Ptrofs.unsigned omsg)=true ->
 Mem.weak_valid_pointer m bkey (Ptrofs.unsigned okey)=true ->
 Clight2.exec_stmt secp_ge e le m (statement_sequence schnorr_verify_checks Sskip) E0
 (schnorr_verify_checked_temps le) m Out_normal.
Proof.
 intros Sig Msg Key SigValid MsgValid KeyValid;cbn [schnorr_verify_checks statement_sequence].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le).
 - apply exec_nonnull_return_zero with (b:=bsig) (ofs:=Ptrofs.zero);[exact Sig|exact SigValid].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=schnorr_verify_checked_temps le).
   + apply exec_schnorr_verify_message_check with (b:=bmsg) (ofs:=omsg);assumption.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=schnorr_verify_checked_temps le);[|constructor].
     apply exec_nonnull_return_zero with (b:=bkey) (ofs:=okey);[|exact KeyValid].
     unfold schnorr_verify_checked_temps;rewrite PTree.gso by (clear;discriminate);exact Key.
Qed.
