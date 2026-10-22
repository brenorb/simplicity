(** Exact public decompression statement tree; call premises are discharged
    by the general input, helper and output contracts in the caller layer. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_decompress_public_entry
 C.jet_secp_decompress_public_prepare C.jet_secp_rescale_public_body.
Require C.jets.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition decompress_public_bit := Scall (Some _t'1)
 (Evar _readBit (type_of_function C.jets.f_readBit))
 [Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))].
Definition decompress_public_parity := Ssequence decompress_public_bit
 (Sset _y (Ecast (Etempvar _t'1 tbool) tbool)).
Definition decompress_public_read := rescale_local_call _read_fe
 (Tstruct __5467 noattr) (Tstruct _frameItem noattr) _x _src.
Definition decompress_public_helper := Scall (Some _t'2)
 (Evar _secp256k1_ge_set_xo_var (type_of_function f_secp256k1_ge_set_xo_var))
 [Eaddrof (Evar _r (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr));
  Eaddrof (Evar _x (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr));Etempvar _y tbool].
Definition decompress_public_tag := Scall (Some _t'3)
 (Evar _writeBit (type_of_function C.jets.f_writeBit))
 [Etempvar _dst (tptr (Tstruct _frameItem noattr));Etempvar _t'2 tint].
Definition decompress_public_payload := Scall None
 (Evar _write_ge (type_of_function f_write_ge))
 [Etempvar _dst (tptr (Tstruct _frameItem noattr));
  Eaddrof (Evar _r (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr))].
Definition decompress_public_padding := Scall None
 (Evar _skip_ge (type_of_function f_skip_ge))
 [Etempvar _dst (tptr (Tstruct _frameItem noattr))].
Definition decompress_public_rest := Ssequence decompress_public_parity
 (Ssequence decompress_public_read
  (Ssequence (Ssequence (Ssequence decompress_public_helper decompress_public_tag)
    (Sifthenelse (Etempvar _t'3 tbool) decompress_public_payload decompress_public_padding))
   (Sreturn (Some (Econst_int Int.one tint))))).
Definition decompress_parity_temps le (odd : bool) :=
 PTree.set _y (Vint (if odd then Int.one else Int.zero))
  (PTree.set _t'1 (Vint (if odd then Int.one else Int.zero)) le).
Definition decompress_result_temps le odd (bit : bool) :=
 PTree.set _t'2 (Vint (if bit then Int.one else Int.zero)) (decompress_parity_temps le odd).
Definition decompress_final_temps le odd (bit : bool) :=
 PTree.set _t'3 (Vint (if bit then Int.one else Int.zero)) (decompress_result_temps le odd bit).
Lemma decompress_public_body_source : fn_body f_simplicity_decompress=
 Ssequence decompress_public_copy decompress_public_rest.
Proof. reflexivity. Qed.
Lemma decompress_public_symbols :
 (exists b,Genv.find_symbol secp_ge _readBit=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal C.jets.f_readBit)) /\
 (exists b,Genv.find_symbol secp_ge _read_fe=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal f_read_fe)) /\
 (exists b,Genv.find_symbol secp_ge _secp256k1_ge_set_xo_var=Some b /\
   Genv.find_funct_ptr secp_ge b=Some (Internal f_secp256k1_ge_set_xo_var)) /\
 (exists b,Genv.find_symbol secp_ge _writeBit=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal C.jets.f_writeBit)) /\
 (exists b,Genv.find_symbol secp_ge _write_ge=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal f_write_ge)) /\
 (exists b,Genv.find_symbol secp_ge _skip_ge=Some b /\ Genv.find_funct_ptr secp_ge b=Some (Internal f_skip_ge)).
Proof.
 split;[exists (secp_symbol_block _readBit);split;reflexivity|].
 split;[exists (secp_symbol_block _read_fe);split;reflexivity|].
 split;[exists (secp_symbol_block _secp256k1_ge_set_xo_var);split;reflexivity|].
 split;[exists (secp_symbol_block _writeBit);split;reflexivity|].
 split;[exists (secp_symbol_block _write_ge);split;reflexivity|].
 exists (secp_symbol_block _skip_ge);split;reflexivity.
Qed.
Local Opaque secp_ge.

Lemma exec_decompress_public_parity le m mf bl bx br (odd : bool) :
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_readBit) [Vptr bl Ptrofs.zero] E0 mf
  (Vint (if odd then Int.one else Int.zero)) ->
 Clight2.exec_stmt secp_ge (decompress_public_env bl bx br) le m decompress_public_parity E0
  (decompress_parity_temps le odd) mf Out_normal.
Proof.
 intro Call;destruct decompress_public_symbols as ((bf & HS & HF) & _).
 unfold decompress_public_parity,decompress_parity_temps.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
  (le1:=PTree.set _t'1 (Vint (if odd then Int.one else Int.zero)) le).
 - unfold decompress_public_bit;eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
    (vargs:=[Vptr bl Ptrofs.zero]) (f:=Internal C.jets.f_readBit)
    (vres:=Vint (if odd then Int.one else Int.zero)).
   + reflexivity.
   + eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HS]|apply deref_loc_reference;reflexivity].
   + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
   + exact HF.
   + reflexivity.
   + exact Call.
 - apply exec_Sset;eapply eval_Ecast;[apply eval_Etempvar;apply PTree.gss|destruct odd;reflexivity].
Qed.

Lemma exec_decompress_public_helper le m mf bl bx br (odd bit : bool) :
 le!_y=Some (Vint (if odd then Int.one else Int.zero)) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_xo_var)
  [Vptr br Ptrofs.zero;Vptr bx Ptrofs.zero;Vint (if odd then Int.one else Int.zero)] E0 mf
  (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.exec_stmt secp_ge (decompress_public_env bl bx br) le m decompress_public_helper E0
  (PTree.set _t'2 (Vint (if bit then Int.one else Int.zero)) le) mf Out_normal.
Proof.
 intros Odd Call;destruct decompress_public_symbols as (_ & _ & (bf & HS & HF) & _).
 unfold decompress_public_helper;eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
  (vargs:=[Vptr br Ptrofs.zero;Vptr bx Ptrofs.zero;Vint (if odd then Int.one else Int.zero)])
  (f:=Internal f_secp256k1_ge_set_xo_var) (vres:=Vint (if bit then Int.one else Int.zero)).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HS]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs.
   + apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
   + reflexivity.
   + eapply eval_Econs.
     * apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
     * reflexivity.
     * eapply eval_Econs;[apply eval_Etempvar;exact Odd|destruct odd;reflexivity|constructor].
 - exact HF.
 - reflexivity.
 - exact Call.
Qed.

Lemma exec_decompress_public_tag le m mf bl bx br bd base (bit : bool) :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 le!_t'2=Some (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_writeBit)
  [Vptr bd (Ptrofs.repr base);Vint (if bit then Int.one else Int.zero)] E0 mf
  (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.exec_stmt secp_ge (decompress_public_env bl bx br) le m decompress_public_tag E0
  (PTree.set _t'3 (Vint (if bit then Int.one else Int.zero)) le) mf Out_normal.
Proof.
 intros HD HT Call;destruct decompress_public_symbols as (_ & _ & _ & (bf & HS & HF) & _).
 unfold decompress_public_tag;eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
  (vargs:=[Vptr bd (Ptrofs.repr base);Vint (if bit then Int.one else Int.zero)])
  (f:=Internal C.jets.f_writeBit) (vres:=Vint (if bit then Int.one else Int.zero)).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HS]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs;[apply eval_Etempvar;exact HD|reflexivity|].
   eapply eval_Econs;[apply eval_Etempvar;exact HT|destruct bit;reflexivity|constructor].
 - exact HF.
 - reflexivity.
 - exact Call.
Qed.

Lemma exec_decompress_public_payload le m mf bl bx br bd base (bit : bool) :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge m (Internal (if bit then f_write_ge else f_skip_ge))
  (if bit then [Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero] else [Vptr bd (Ptrofs.repr base)]) E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (decompress_public_env bl bx br) le m
  (if bit then decompress_public_payload else decompress_public_padding) E0 le mf Out_normal.
Proof.
 intros HD Call;destruct decompress_public_symbols as (_ & _ & _ & _ & (bf & HS & HF) & (bg & HT & HG)).
 destruct bit;unfold decompress_public_payload,decompress_public_padding.
 - eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
    (vargs:=[Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero]) (f:=Internal f_write_ge) (vres:=Vundef).
   + reflexivity.
   + eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HS]|apply deref_loc_reference;reflexivity].
   + eapply eval_Econs;[apply eval_Etempvar;exact HD|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
   + exact HF.
   + reflexivity.
   + exact Call.
 - eapply exec_Scall with (vf:=Vptr bg Ptrofs.zero)
    (vargs:=[Vptr bd (Ptrofs.repr base)]) (f:=Internal f_skip_ge) (vres:=Vundef).
   + reflexivity.
   + eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HT]|apply deref_loc_reference;reflexivity].
   + eapply eval_Econs;[apply eval_Etempvar;exact HD|reflexivity|constructor].
   + exact HG.
   + reflexivity.
   + exact Call.
Qed.

Theorem exec_decompress_public_rest_from_calls le m mp mr mn mt mf bl bx br bd base (odd bit : bool) :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_readBit) [Vptr bl Ptrofs.zero] E0 mp
  (Vint (if odd then Int.one else Int.zero)) ->
 Clight2.eval_funcall secp_ge mp (Internal f_read_fe) [Vptr bx Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
 Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_ge_set_xo_var)
  [Vptr br Ptrofs.zero;Vptr bx Ptrofs.zero;Vint (if odd then Int.one else Int.zero)] E0 mn
  (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.eval_funcall secp_ge mn (Internal C.jets.f_writeBit)
  [Vptr bd (Ptrofs.repr base);Vint (if bit then Int.one else Int.zero)] E0 mt
  (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.eval_funcall secp_ge mt (Internal (if bit then f_write_ge else f_skip_ge))
  (if bit then [Vptr bd (Ptrofs.repr base);Vptr br Ptrofs.zero] else [Vptr bd (Ptrofs.repr base)]) E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (decompress_public_env bl bx br) le m decompress_public_rest E0
  (decompress_final_temps le odd bit) mf (Out_return (Some (Vint Int.one,tint))).
Proof.
 intros HD BitCall Read Helper Tag Payload;destruct decompress_public_symbols as (_ & SR & _).
 unfold decompress_public_rest,decompress_public_read.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mp) (le1:=decompress_parity_temps le odd).
 - apply exec_decompress_public_parity;exact BitCall.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=decompress_parity_temps le odd).
   + eapply exec_rescale_local_call;[exact SR|reflexivity|reflexivity|reflexivity|reflexivity|exact Read].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=decompress_final_temps le odd bit).
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mt) (le1:=decompress_final_temps le odd bit).
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=decompress_result_temps le odd bit).
          ++ apply exec_decompress_public_helper with (odd:=odd);[apply PTree.gss|exact Helper].
          ++ eapply exec_decompress_public_tag.
             ** unfold decompress_result_temps,decompress_parity_temps;rewrite !PTree.gso by discriminate;exact HD.
             ** apply PTree.gss.
             ** exact Tag.
       -- eapply exec_Sifthenelse with (v1:=Vint (if bit then Int.one else Int.zero)) (b:=bit).
          ++ apply eval_Etempvar;apply PTree.gss.
          ++ destruct bit;reflexivity.
          ++ eapply exec_decompress_public_payload;[|exact Payload].
             unfold decompress_final_temps,decompress_result_temps,decompress_parity_temps;
             rewrite !PTree.gso by discriminate;exact HD.
     * apply exec_Sreturn_some;constructor.
Qed.
