(** Exact original extended mixed-addition wrapper and its typed call nodes.
    This composes calls; storage-based results are discharged by the caller. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements
  C.jet_secp_mixed_public_entry C.jet_secp_mixed_public_body C.jet_secp_rescale_public_body.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition mixed_ex_public_env bl bp ba br :=
  PTree.set _rzr (br,curve_fe_type) (mixed_public_env bl bp ba).
Definition mixed_ex_public_clear := curve_call _secp256k1_fe_clear f_secp256k1_fe_clear None
  [curve_local_address _rzr].
Definition mixed_ex_public_helper := curve_call _secp256k1_gej_add_ge_var f_secp256k1_gej_add_ge_var None
  [Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
   Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr));
   Eaddrof (Evar _b (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr));
   curve_local_address _rzr].
Definition mixed_ex_public_writer fid fd id ty := curve_call fid fd None
  [Etempvar _dst (tptr (Tstruct _frameItem noattr));Eaddrof (Evar id ty) (tptr ty)].
Definition mixed_ex_public_rest := Ssequence mixed_ex_public_clear
  (Ssequence mixed_public_read_point (Ssequence mixed_public_read_affine
    (Ssequence mixed_ex_public_helper
      (Ssequence (mixed_ex_public_writer _write_fe f_write_fe _rzr curve_fe_type)
        (Ssequence (mixed_ex_public_writer _write_gej f_write_gej _a (Tstruct __6123 noattr))
          (Sreturn (Some (Econst_int Int.one tint)))))))).
Lemma mixed_ex_public_source : fn_body f_simplicity_gej_ge_add_ex=
  Ssequence rescale_public_copy mixed_ex_public_rest.
Proof. reflexivity. Qed.
Lemma mixed_ex_public_symbols :
  (exists b, Genv.find_symbol secp_ge _secp256k1_fe_clear=Some b /\
    Genv.find_funct_ptr secp_ge b=Some (Internal f_secp256k1_fe_clear)) /\
  (exists b, Genv.find_symbol secp_ge _write_fe=Some b /\
    Genv.find_funct_ptr secp_ge b=Some (Internal f_write_fe)).
Proof.
  split;[exists (secp_symbol_block _secp256k1_fe_clear)|exists (secp_symbol_block _write_fe)];split;reflexivity.
Qed.
Local Opaque secp_ge.

Lemma exec_mixed_ex_public_clear le m mf bl bp ba br :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_clear) [Vptr br Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (mixed_ex_public_env bl bp ba br) le m mixed_ex_public_clear E0 le mf Out_normal.
Proof.
  intro HC;unfold mixed_ex_public_clear.
  eapply exec_curve_call with (vargs:=[Vptr br Ptrofs.zero]) (v:=Vundef).
  - unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
  - reflexivity.
  - eapply eval_Econs;[apply eval_curve_local;reflexivity|reflexivity|constructor].
  - exact HC.
Qed.

Lemma exec_mixed_ex_public_helper le m mf bl bp ba br :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_add_ge_var)
    [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (mixed_ex_public_env bl bp ba br) le m mixed_ex_public_helper E0 le mf Out_normal.
Proof.
  intro HC;destruct mixed_public_symbols as (_ & _ & (bf & HS & HF) & _).
  unfold mixed_ex_public_helper,curve_call.
  eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
    (vargs:=[Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br Ptrofs.zero])
    (f:=Internal f_secp256k1_gej_add_ge_var) (vres:=Vundef).
  - reflexivity.
  - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact HS]|apply deref_loc_reference;reflexivity].
  - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
    eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
    eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
    eapply eval_Econs;[apply eval_curve_local;reflexivity|reflexivity|constructor].
  - exact HF.
  - reflexivity.
  - exact HC.
Qed.

Lemma exec_mixed_ex_public_writer fid fd id ty e le m mf b bd dbase :
  (exists bf, Genv.find_symbol secp_ge fid=Some bf /\ Genv.find_funct_ptr secp_ge bf=Some (Internal fd)) ->
  e!fid=None -> e!id=Some (b,ty) -> le!_dst=Some (Vptr bd (Ptrofs.repr dbase)) ->
  type_of_fundef (Internal fd)=Tfunction
    (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr ty) Tnil)) tvoid cc_default ->
  Clight2.eval_funcall secp_ge m (Internal fd)
    [Vptr bd (Ptrofs.repr dbase);Vptr b Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m (mixed_ex_public_writer fid fd id ty) E0 le mf Out_normal.
Proof.
  intros (bf & HS & HF) HG HL HD HT HC;unfold mixed_ex_public_writer,curve_call.
  eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
    (vargs:=[Vptr bd (Ptrofs.repr dbase);Vptr b Ptrofs.zero]) (f:=Internal fd) (vres:=Vundef).
  - reflexivity.
  - eapply eval_Elvalue;[eapply eval_Evar_global;[exact HG|exact HS]|apply deref_loc_reference;reflexivity].
  - pose proof (f_equal (fun t=>match t with Tfunction args _ _=>args|_=>Tnil end) HT) as Params.
    change (type_of_params (fn_params fd)=
      Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr ty) Tnil)) in Params.
    rewrite Params.
    eapply eval_Econs;[apply eval_Etempvar;exact HD|reflexivity|].
    eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact HL|reflexivity|constructor].
  - exact HF.
  - reflexivity.
  - exact HC.
Qed.

Lemma exec_mixed_ex_rest_from_calls le m mc mr ms mn mw mf bl bp ba br bd dbase :
  le!_dst=Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_clear) [Vptr br Ptrofs.zero] E0 mc Vundef ->
  Clight2.eval_funcall secp_ge mc (Internal f_read_gej) [Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
  Clight2.eval_funcall secp_ge mr (Internal f_read_ge) [Vptr ba Ptrofs.zero;Vptr bl Ptrofs.zero] E0 ms Vundef ->
  Clight2.eval_funcall secp_ge ms (Internal f_secp256k1_gej_add_ge_var)
    [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr br Ptrofs.zero] E0 mn Vundef ->
  Clight2.eval_funcall secp_ge mn (Internal f_write_fe)
    [Vptr bd (Ptrofs.repr dbase);Vptr br Ptrofs.zero] E0 mw Vundef ->
  Clight2.eval_funcall secp_ge mw (Internal f_write_gej)
    [Vptr bd (Ptrofs.repr dbase);Vptr bp Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (mixed_ex_public_env bl bp ba br) le m mixed_ex_public_rest E0 le mf
    (Out_return (Some (Vint Int.one,tint))).
Proof.
  intros HD CC CR CA CH CW CP.
  destruct mixed_public_symbols as (SR & SA & SH & SP).
  destruct mixed_ex_public_symbols as (_ & SW).
  unfold mixed_ex_public_rest,mixed_public_read_point,mixed_public_read_affine.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=le).
  - apply exec_mixed_ex_public_clear;exact CC.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mr) (le1:=le).
    + eapply exec_rescale_local_call;[exact SR|reflexivity|reflexivity|reflexivity|reflexivity|exact CR].
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ms) (le1:=le).
      * eapply exec_rescale_local_call;[exact SA|reflexivity|reflexivity|reflexivity|reflexivity|exact CA].
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=le).
        -- apply exec_mixed_ex_public_helper;exact CH.
        -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mw) (le1:=le).
           ++ eapply exec_mixed_ex_public_writer;[exact SW|reflexivity|reflexivity|exact HD|reflexivity|exact CW].
           ++ eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
              ** eapply exec_mixed_ex_public_writer;[exact SP|reflexivity|reflexivity|exact HD|reflexivity|exact CP].
              ** apply exec_Sreturn_some;constructor.
Qed.
