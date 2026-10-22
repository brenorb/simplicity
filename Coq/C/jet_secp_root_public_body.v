(** Exact public square-root statement tree, including both bool conversions.
    The call premises here are discharged from frame/storage in the next layer. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_root_public_entry
 C.jet_secp_root_public_prepare C.jet_secp_rescale_public_body.
Require C.jets.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition root_public_read := rescale_local_call _read_fe
 (Tstruct __5467 noattr) (Tstruct _frameItem noattr) _a _src.
Definition root_public_helper := Scall (Some _t'1)
 (Evar _secp256k1_fe_sqrt_var (type_of_function f_secp256k1_fe_sqrt_var))
 [Eaddrof (Evar _r (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr));
  Eaddrof (Evar _a (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr))].
Definition root_public_tag := Scall (Some _t'2)
 (Evar _writeBit (type_of_function C.jets.f_writeBit))
 [Etempvar _dst (tptr (Tstruct _frameItem noattr));Etempvar _result tint].
Definition root_public_payload := Scall None
 (Evar _write_fe (type_of_function f_write_fe))
 [Etempvar _dst (tptr (Tstruct _frameItem noattr));
  Eaddrof (Evar _r (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr))].
Definition root_public_padding := Scall None
 (Evar _skip_fe (type_of_function f_skip_fe))
 [Etempvar _dst (tptr (Tstruct _frameItem noattr))].
Definition root_public_rest := Ssequence root_public_read
 (Ssequence (Ssequence root_public_helper (Sset _result (Etempvar _t'1 tint)))
  (Ssequence (Ssequence root_public_tag
   (Sifthenelse (Etempvar _t'2 tbool) root_public_payload root_public_padding))
   (Sreturn (Some (Econst_int Int.one tint))))).
Definition root_public_result_temps le (bit : bool) :=
 PTree.set _result (Vint (if bit then Int.one else Int.zero))
  (PTree.set _t'1 (Vint (if bit then Int.one else Int.zero)) le).
Definition root_public_final_temps le (bit : bool) :=
 PTree.set _t'2 (Vint (if bit then Int.one else Int.zero)) (root_public_result_temps le bit).

Lemma root_public_body : fn_body f_simplicity_fe_square_root=Ssequence root_public_copy root_public_rest.
Proof. reflexivity. Qed.
Lemma root_public_symbols :
 (exists b,Genv.find_symbol secp_ge _read_fe=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal f_read_fe)) /\
 (exists b,Genv.find_symbol secp_ge _secp256k1_fe_sqrt_var=Some b /\
   Genv.find_funct_ptr secp_ge b=Some (Internal f_secp256k1_fe_sqrt_var)) /\
 (exists b,Genv.find_symbol secp_ge _writeBit=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal C.jets.f_writeBit)) /\
 (exists b,Genv.find_symbol secp_ge _write_fe=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal f_write_fe)) /\
 (exists b,Genv.find_symbol secp_ge _skip_fe=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal f_skip_fe)).
Proof.
 split;[exists (secp_symbol_block _read_fe);split;reflexivity|].
 split;[exists (secp_symbol_block _secp256k1_fe_sqrt_var);split;reflexivity|].
 split;[exists (secp_symbol_block _writeBit);split;reflexivity|].
 split;[exists (secp_symbol_block _write_fe);split;reflexivity|].
 exists (secp_symbol_block _skip_fe);split;reflexivity.
Qed.
Local Opaque secp_ge.

Lemma exec_root_public_helper le m mf bl br ba (bit : bool) :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqrt_var)
  [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.exec_stmt secp_ge (root_public_env bl br ba) le m root_public_helper E0
  (PTree.set _t'1 (Vint (if bit then Int.one else Int.zero)) le) mf Out_normal.
Proof.
 intro HC;destruct root_public_symbols as (_ & (bf & HS & HF) & _).
 unfold root_public_helper.
 eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero) (vargs:=[Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero])
  (f:=Internal f_secp256k1_fe_sqrt_var) (vres:=Vint (if bit then Int.one else Int.zero)).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HS]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs.
   + apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
   + reflexivity.
   + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
 - exact HF.
 - reflexivity.
 - exact HC.
Qed.

Lemma exec_root_public_tag le m mf bl br ba bd base (bit : bool) :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 le!_result=Some (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_writeBit)
  [Vptr bd (Ptrofs.repr base);Vint (if bit then Int.one else Int.zero)] E0 mf
  (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.exec_stmt secp_ge (root_public_env bl br ba) le m root_public_tag E0
  (PTree.set _t'2 (Vint (if bit then Int.one else Int.zero)) le) mf Out_normal.
Proof.
 intros HD HT HC;destruct root_public_symbols as (_ & _ & (bf & HS & HF) & _).
 unfold root_public_tag.
 eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
  (vargs:=[Vptr bd (Ptrofs.repr base);Vint (if bit then Int.one else Int.zero)])
  (f:=Internal C.jets.f_writeBit) (vres:=Vint (if bit then Int.one else Int.zero)).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HS]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs.
   + apply eval_Etempvar;exact HD.
   + reflexivity.
   + eapply eval_Econs;[apply eval_Etempvar;exact HT|destruct bit;reflexivity|constructor].
 - exact HF.
 - reflexivity.
 - exact HC.
Qed.

Lemma exec_root_public_payload le m mf bl br ba bd base (bit : bool) :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge m (Internal (if bit then f_write_fe else f_skip_fe))
  (if bit then [Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero] else [Vptr bd (Ptrofs.repr base)]) E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (root_public_env bl br ba) le m
  (if bit then root_public_payload else root_public_padding) E0 le mf Out_normal.
Proof.
 intros HD HC;destruct root_public_symbols as (_ & _ & _ & (bf & HS & HF) & (bg & HT & HG)).
 destruct bit;unfold root_public_payload,root_public_padding.
 - eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
    (vargs:=[Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero]) (f:=Internal f_write_fe) (vres:=Vundef).
   + reflexivity.
   + eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HS]|apply deref_loc_reference;reflexivity].
   + eapply eval_Econs;[apply eval_Etempvar;exact HD|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
   + exact HF.
   + reflexivity.
   + exact HC.
 - eapply exec_Scall with (vf:=Vptr bg Ptrofs.zero)
    (vargs:=[Vptr bd (Ptrofs.repr base)]) (f:=Internal f_skip_fe) (vres:=Vundef).
   + reflexivity.
   + eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HT]|apply deref_loc_reference;reflexivity].
   + eapply eval_Econs;[apply eval_Etempvar;exact HD|reflexivity|constructor].
   + exact HG.
   + reflexivity.
   + exact HC.
Qed.

Theorem exec_root_public_rest_from_calls le m mr mn mt mf bl br ba bd base (bit : bool) :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge m (Internal f_read_fe) [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
 Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_fe_sqrt_var)
  [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mn (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.eval_funcall secp_ge mn (Internal C.jets.f_writeBit)
  [Vptr bd (Ptrofs.repr base);Vint (if bit then Int.one else Int.zero)] E0 mt
  (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.eval_funcall secp_ge mt (Internal (if bit then f_write_fe else f_skip_fe))
  (if bit then [Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero] else [Vptr bd (Ptrofs.repr base)]) E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (root_public_env bl br ba) le m root_public_rest E0
  (root_public_final_temps le bit) mf (Out_return (Some (Vint Int.one,tint))).
Proof.
 intros HD HR HC HT HW;destruct root_public_symbols as (SR & _).
 unfold root_public_rest,root_public_read.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le).
 - eapply exec_rescale_local_call;[exact SR|reflexivity|reflexivity|reflexivity|reflexivity|exact HR].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=root_public_result_temps le bit).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn)
      (le1:=PTree.set _t'1 (Vint (if bit then Int.one else Int.zero)) le).
     * apply exec_root_public_helper;exact HC.
     * apply exec_Sset;apply eval_Etempvar;apply PTree.gss.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=root_public_final_temps le bit).
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mt) (le1:=root_public_final_temps le bit).
       -- eapply exec_root_public_tag.
          ++ unfold root_public_result_temps;rewrite !PTree.gso by discriminate;exact HD.
          ++ apply PTree.gss.
          ++ exact HT.
       -- eapply exec_Sifthenelse with (v1:=Vint (if bit then Int.one else Int.zero)) (b:=bit).
          ++ apply eval_Etempvar;apply PTree.gss.
          ++ destruct bit;reflexivity.
          ++ eapply exec_root_public_payload;[|exact HW].
             unfold root_public_final_temps,root_public_result_temps;rewrite !PTree.gso by discriminate;exact HD.
     * apply exec_Sreturn_some;constructor.
Qed.
