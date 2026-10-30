(** Actual linked x-only call spine and short-circuit result. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_xonly_tweak_entry C.jet_readBit_layout.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_xonly_tweak_calls C.jet_elements_taptweak_pure C.jet_elements_taptweak_globals C.jet_elements_taptweak_parse_start.
Lemma elements_taptweak_xonly_pubkey_load_call_linked:exists b,
 Genv.find_symbol elements_taptweak_ge _secp256k1_xonly_pubkey_load=Some b /\
 Genv.find_funct_ptr elements_taptweak_ge b=Some(Internal f_secp256k1_xonly_pubkey_load).
Proof. exists(elements_taptweak_symbol_block _secp256k1_xonly_pubkey_load);split;vm_compute;reflexivity. Qed.
Lemma elements_taptweak_ec_pubkey_tweak_add_helper_call_linked:exists b,
 Genv.find_symbol elements_taptweak_ge _secp256k1_ec_pubkey_tweak_add_helper=Some b /\
 Genv.find_funct_ptr elements_taptweak_ge b=Some(Internal f_secp256k1_ec_pubkey_tweak_add_helper).
Proof. exists(elements_taptweak_symbol_block _secp256k1_ec_pubkey_tweak_add_helper);split;vm_compute;reflexivity. Qed.
Lemma elements_taptweak_pubkey_save_call_linked:exists b,
 Genv.find_symbol elements_taptweak_ge _secp256k1_pubkey_save=Some b /\
 Genv.find_funct_ptr elements_taptweak_ge b=Some(Internal f_secp256k1_pubkey_save).
Proof. exists(elements_taptweak_symbol_block _secp256k1_pubkey_save);split;vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge.
Theorem exec_elements_taptweak_xonly_test e le m ml mt bk bin bb result:
 e!_pk=Some (bk,curve_ge_type) ->e!_secp256k1_xonly_pubkey_load=None ->
 e!_secp256k1_ec_pubkey_tweak_add_helper=None ->
 le!_internal_pubkey=Some (Vptr bin Ptrofs.zero) ->le!_tweak32=Some (Vptr bb Ptrofs.zero) ->
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_xonly_pubkey_load)
 [Vptr bk Ptrofs.zero;Vptr bin Ptrofs.zero] E0 ml (Vint Int.one) ->
 Clight2.eval_funcall elements_taptweak_ge ml (Internal f_secp256k1_ec_pubkey_tweak_add_helper)
 [Vptr bk Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mt (Vint (bit_int result)) ->
 Clight2.exec_stmt elements_taptweak_ge e le m xonly_tweak_test E0
 (xonly_tweak_test_temps le result) mt (xonly_tweak_test_outcome result).
Proof.
 intros PK LoadSymbol TweakSymbol Input Bytes Load Tweak;
 destruct elements_taptweak_xonly_pubkey_load_call_linked as(bl & SL & FL);
 destruct elements_taptweak_ec_pubkey_tweak_add_helper_call_linked as(bt & ST & FT);unfold xonly_tweak_test,xonly_tweak_test_temps.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mt)
 (le1:=PTree.set _t'2 (Vint (bit_int (negb result)))
 (PTree.set _t'3 (Vint (bit_int result)) (PTree.set _t'1 (Vint Int.one) le))).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ml) (le1:=PTree.set _t'1 (Vint Int.one) le).
   + unfold xonly_tweak_load;eapply exec_elements_taptweak_curve_call with(bf:=bl)
     (vargs:=[Vptr bk Ptrofs.zero;Vptr bin Ptrofs.zero]) (v:=Vint Int.one).
     * exact SL.
     * unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact FL.
     * exact LoadSymbol.
     * eapply eval_Econs.
       -- unfold xonly_tweak_pk;apply eval_Eaddrof;apply eval_Evar_local;exact PK.
       -- reflexivity.
       -- eapply eval_Econs;[apply eval_Etempvar;exact Input|reflexivity|constructor].
     * exact Load.
   + eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
     * eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity].
     * reflexivity.
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mt)
       (le1:=PTree.set _t'3 (Vint (bit_int result)) (PTree.set _t'1 (Vint Int.one) le)).
       -- unfold xonly_tweak_scalar;eapply exec_elements_taptweak_curve_call with(bf:=bt)
         (vargs:=[Vptr bk Ptrofs.zero;Vptr bb Ptrofs.zero]) (v:=Vint (bit_int result)).
          ++ exact ST.
          ++ unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact FT.
          ++ exact TweakSymbol.
          ++ eapply eval_Econs.
             ** unfold xonly_tweak_pk;apply eval_Eaddrof;apply eval_Evar_local;exact PK.
             ** reflexivity.
             ** eapply eval_Econs;[apply eval_Etempvar;rewrite PTree.gso by discriminate;exact Bytes|reflexivity|constructor].
          ++ exact Tweak.
       -- apply exec_Sset;eapply eval_Ecast.
          ++ eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|destruct result;reflexivity].
          ++ destruct result;reflexivity.
 - destruct result.
   + eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);
     [apply eval_Etempvar;apply PTree.gss|reflexivity|constructor].
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);
     [apply eval_Etempvar;apply PTree.gss|reflexivity|apply exec_Sreturn_some;constructor].
Qed.
Lemma exec_elements_taptweak_xonly_finish e le m mf bk bout:
 e!_pk=Some (bk,curve_ge_type) ->e!_secp256k1_pubkey_save=None ->
 le!_output_pubkey=Some (Vptr bout Ptrofs.zero) ->
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_pubkey_save)
 [Vptr bout Ptrofs.zero;Vptr bk Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt elements_taptweak_ge e le m xonly_tweak_finish E0 le mf
 (Out_return (Some (Vint Int.one,tint))).
Proof.
 intros PK Symbol Output Save;destruct elements_taptweak_pubkey_save_call_linked as(bs & SS & FS);unfold xonly_tweak_finish;
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
 - unfold xonly_tweak_save;eapply exec_elements_taptweak_curve_call with(bf:=bs)
   (vargs:=[Vptr bout Ptrofs.zero;Vptr bk Ptrofs.zero]) (v:=Vundef).
   + exact SS.
   + unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact FS.
   + exact Symbol.
   + eapply eval_Econs;[apply eval_Etempvar;exact Output|reflexivity|].
     eapply eval_Econs;[unfold xonly_tweak_pk;apply eval_Eaddrof;apply eval_Evar_local;exact PK|reflexivity|constructor].
   + exact Save.
 - apply exec_Sreturn_some;constructor.
Qed.
