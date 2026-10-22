(** Exact original public projective-addition statement tree and typed call adapters. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_gej_add_public_entry C.jet_secp_rescale_public_body.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition gej_add_public_read_point := rescale_local_call _read_gej
 (Tstruct __6123 noattr) (Tstruct _frameItem noattr) _a _src.
Definition gej_add_public_read_second := rescale_local_call _read_gej
 (Tstruct __6123 noattr) (Tstruct _frameItem noattr) _b _src.
Definition gej_add_public_helper := Scall None
 (Evar _secp256k1_gej_add_var (type_of_function f_secp256k1_gej_add_var))
 [Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
  Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
  Eaddrof (Evar _b (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
  Ecast (Econst_int Int.zero tint) (tptr tvoid)].
Definition gej_add_public_rest := Ssequence gej_add_public_read_point
 (Ssequence gej_add_public_read_second (Ssequence gej_add_public_helper
   (Ssequence rescale_public_write (Sreturn (Some (Econst_int Int.one tint)))))).
Lemma gej_add_public_body : fn_body f_simplicity_gej_add=Ssequence rescale_public_copy gej_add_public_rest.
Proof. reflexivity. Qed.
Lemma gej_add_public_symbols :
 (exists b, Genv.find_symbol secp_ge _read_gej=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal f_read_gej)) /\
 (exists b, Genv.find_symbol secp_ge _read_gej=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal f_read_gej)) /\
 (exists b, Genv.find_symbol secp_ge _secp256k1_gej_add_var=Some b /\
   Genv.find_funct_ptr secp_ge b=Some (Internal f_secp256k1_gej_add_var)) /\
 (exists b, Genv.find_symbol secp_ge _write_gej=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal f_write_gej)).
Proof.
 split;[exists (secp_symbol_block _read_gej);split;reflexivity|].
 split;[exists (secp_symbol_block _read_gej);split;reflexivity|].
 split;[exists (secp_symbol_block _secp256k1_gej_add_var);split;reflexivity|].
 exists (secp_symbol_block _write_gej);split;reflexivity.
Qed.
Local Opaque secp_ge.

Lemma exec_gej_add_public_helper le m mf bl bp ba :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_add_var)
  [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (gej_add_public_env bl bp ba) le m gej_add_public_helper E0 le mf Out_normal.
Proof.
 intro HC;destruct gej_add_public_symbols as (_ & _ & (bf & HS & HF) & _).
 unfold gej_add_public_helper.
 eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
  (vargs:=[Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong Int64.zero])
  (f:=Internal f_secp256k1_gej_add_var) (vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HS]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs.
   + apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
   + reflexivity.
   + eapply eval_Econs.
     * apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
     * reflexivity.
     * eapply eval_Econs.
       -- apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
       -- reflexivity.
       -- eapply eval_Econs.
          ++ eapply eval_Ecast with (v1:=Vint Int.zero);[constructor|reflexivity].
          ++ reflexivity.
          ++ constructor.
 - exact HF.
 - reflexivity.
 - exact HC.
Qed.
Lemma exec_gej_add_public_write le m mf bl bp ba bd dbase :
 le!_dst=Some (Vptr bd (Ptrofs.repr dbase)) ->
 Clight2.eval_funcall secp_ge m (Internal f_write_gej)
   [Vptr bd (Ptrofs.repr dbase);Vptr bp Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (gej_add_public_env bl bp ba) le m rescale_public_write E0 le mf Out_normal.
Proof.
 intros HD HC;destruct gej_add_public_symbols as (_ & _ & _ & bf & HS & HF).
 unfold rescale_public_write.
 eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
   (vargs:=[Vptr bd (Ptrofs.repr dbase);Vptr bp Ptrofs.zero]) (f:=Internal f_write_gej) (vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HS]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs.
   + apply eval_Etempvar;exact HD.
   + reflexivity.
   + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
 - exact HF.
 - reflexivity.
 - exact HC.
Qed.
Lemma exec_gej_add_rest_from_calls le m mr ms mn mf bl bp ba bd dbase :
 le!_dst=Some (Vptr bd (Ptrofs.repr dbase)) ->
 Clight2.eval_funcall secp_ge m (Internal f_read_gej) [Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
 Clight2.eval_funcall secp_ge mr (Internal f_read_gej) [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 ms Vundef ->
 Clight2.eval_funcall secp_ge ms (Internal f_secp256k1_gej_add_var)
   [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong Int64.zero] E0 mn Vundef ->
 Clight2.eval_funcall secp_ge mn (Internal f_write_gej) [Vptr bd (Ptrofs.repr dbase);Vptr bp Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (gej_add_public_env bl bp ba) le m gej_add_public_rest E0 le mf
   (Out_return (Some (Vint Int.one,tint))).
Proof.
 intros HD HR HA HN HW;destruct gej_add_public_symbols as (SR & SA & SN & SW).
 unfold gej_add_public_rest,gej_add_public_read_point,gej_add_public_read_second.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le).
 - eapply exec_rescale_local_call;[exact SR|reflexivity|reflexivity|reflexivity|reflexivity|exact HR].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ms) (le1:=le).
   + eapply exec_rescale_local_call;[exact SA|reflexivity|reflexivity|reflexivity|reflexivity|exact HA].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=le).
     * apply exec_gej_add_public_helper;exact HN.
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
       -- eapply exec_gej_add_public_write;eassumption.
       -- apply exec_Sreturn_some;constructor.
Qed.
