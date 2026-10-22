(** Original public wrapper: entry and typed read/read/helper/bit-write/return.
    Its call premises are discharged from frames in the next layer. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_exec C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_mixed_public_entry C.jet_secp_mixed_public_body C.jet_secp_rescale_public_body
 C.jet_secp_gej_add_public_entry C.jet_secp_gej_add_public_body
 C.jet_secp_curve_statements C.jet_secp_odd_body C.jet_secp_rescale_public_entry.
Require C.jets.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition gej_equiv_public_temps (v_env : val) bd base bs sbase :=
 PTree.set _env v_env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
  (PTree.set _dst (Vptr bd (Ptrofs.repr base)) (create_undef_temps (fn_temps f_simplicity_gej_equiv)))).
Definition gej_equiv_public_helper := curve_call _secp256k1_gej_eq_var f_secp256k1_gej_eq_var
 (Some _t'1) [Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
             Eaddrof (Evar _b (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))].
Definition gej_equiv_public_rest := Ssequence gej_add_public_read_point (Ssequence gej_add_public_read_second
 (Ssequence (Ssequence gej_equiv_public_helper secp_public_bit_write_stmt)
  (Sreturn (Some (Econst_int Int.one tint))))).

Lemma gej_equiv_public_source : fn_body f_simplicity_gej_equiv=
 Ssequence rescale_public_copy gej_equiv_public_rest.
Proof. reflexivity. Qed.
Lemma gej_equiv_public_entry v_env m ma mb mc bl bp ba bd base bs sbase :
 Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 128=(mb,bp) -> Mem.alloc mb 0 128=(mc,ba) ->
 function_entry2 secp_ge f_simplicity_gej_equiv
  [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
  (gej_add_public_env bl bp ba) (gej_equiv_public_temps v_env bd base bs sbase) mc.
Proof.
 intros A1 A2 A3;assert (Ok : fn_okb f_simplicity_gej_equiv=true) by reflexivity.
 destruct (fn_okb_true _ Ok) as (HN1 & HN2 & HD);constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
 eapply alloc_variables_cons with (m1:=ma) (b1:=bl);[exact A1|].
 eapply alloc_variables_cons with (m1:=mb) (b1:=bp);[exact A2|].
 eapply alloc_variables_cons with (m1:=mc) (b1:=ba);[exact A3|constructor].
Qed.

Lemma exec_gej_equiv_public_helper le m mf bl bp ba (bit : bool) :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_eq_var)
  [Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.exec_stmt secp_ge (gej_add_public_env bl bp ba) le m gej_equiv_public_helper E0
  (PTree.set _t'1 (Vint (if bit then Int.one else Int.zero)) le) mf Out_normal.
Proof.
 intro Call;unfold gej_equiv_public_helper;eapply exec_curve_call with
  (vargs:=[Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero]) (v:=Vint (if bit then Int.one else Int.zero)).
 - unfold secp_pure;repeat (first [left;reflexivity|right]).
 - reflexivity.
 - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
 - exact Call.
Qed.

Lemma exec_gej_equiv_public_write le m mf bl bp ba bd base (bit : bool) :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) -> le!_t'1=Some (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_writeBit)
  [Vptr bd (Ptrofs.repr base);Vint (if bit then Int.one else Int.zero)] E0 mf
  (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.exec_stmt secp_ge (gej_add_public_env bl bp ba) le m secp_public_bit_write_stmt E0 le mf Out_normal.
Proof.
 intros HD HT Call;destruct secp_odd_helper_symbols as (_ & _ & Sym & Func).
 unfold secp_public_bit_write_stmt;eapply exec_Scall with
  (vf:=Vptr (secp_symbol_block _writeBit) Ptrofs.zero)
  (vargs:=[Vptr bd (Ptrofs.repr base);Vint (if bit then Int.one else Int.zero)])
  (f:=Internal C.jets.f_writeBit) (vres:=Vint (if bit then Int.one else Int.zero)).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact Sym]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs;[apply eval_Etempvar;exact HD|reflexivity|].
   eapply eval_Econs;[apply eval_Etempvar;exact HT|destruct bit;reflexivity|constructor].
 - exact Func.
 - reflexivity.
 - exact Call.
Qed.

Theorem exec_gej_equiv_public_rest_from_calls le m mr ms mn mf bl bp ba bd base (bit : bool) :
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge m (Internal f_read_gej) [Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
 Clight2.eval_funcall secp_ge mr (Internal f_read_gej) [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 ms Vundef ->
 Clight2.eval_funcall secp_ge ms (Internal f_secp256k1_gej_eq_var)
  [Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mn (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.eval_funcall secp_ge mn (Internal C.jets.f_writeBit)
  [Vptr bd (Ptrofs.repr base);Vint (if bit then Int.one else Int.zero)] E0 mf
  (Vint (if bit then Int.one else Int.zero)) ->
 Clight2.exec_stmt secp_ge (gej_add_public_env bl bp ba) le m gej_equiv_public_rest E0
  (PTree.set _t'1 (Vint (if bit then Int.one else Int.zero)) le) mf (Out_return (Some (Vint Int.one,tint))).
Proof.
 intros HD RP RA Helper Write;destruct gej_add_public_symbols as (SP & SA & _).
 unfold gej_equiv_public_rest,gej_add_public_read_point,gej_add_public_read_second.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le).
 - eapply exec_rescale_local_call;[exact SP|reflexivity|reflexivity|reflexivity|reflexivity|exact RP].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ms) (le1:=le).
   + eapply exec_rescale_local_call;[exact SA|reflexivity|reflexivity|reflexivity|reflexivity|exact RA].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
      (le1:=PTree.set _t'1 (Vint (if bit then Int.one else Int.zero)) le).
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn)
        (le1:=PTree.set _t'1 (Vint (if bit then Int.one else Int.zero)) le).
       -- apply exec_gej_equiv_public_helper;exact Helper.
       -- eapply exec_gej_equiv_public_write;[rewrite PTree.gso by discriminate;exact HD|apply PTree.gss|exact Write].
     * apply exec_Sreturn_some;constructor.
Qed.
