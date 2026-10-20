(** Exact public body, with typed adapters for its actual four calls. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_rescale_public_entry.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition rescale_local_call fid ty1 ty2 id1 id2 :=
  Scall None (Evar fid (Tfunction (Tcons (tptr ty1) (Tcons (tptr ty2) Tnil)) tvoid cc_default))
    [Eaddrof (Evar id1 ty1) (tptr ty1);Eaddrof (Evar id2 ty2) (tptr ty2)].
Definition rescale_public_read_point := rescale_local_call _read_gej
  (Tstruct __6123 noattr) (Tstruct _frameItem noattr) _a _src.
Definition rescale_public_read_scale := rescale_local_call _read_fe
  (Tstruct __5467 noattr) (Tstruct _frameItem noattr) _c _src.
Definition rescale_public_helper := rescale_local_call _secp256k1_gej_rescale
  (Tstruct __6123 noattr) (Tstruct __5467 noattr) _a _c.
Definition rescale_public_write := Scall None
  (Evar _write_gej (Tfunction (Tcons (tptr (Tstruct _frameItem noattr))
    (Tcons (tptr (Tstruct __6123 noattr)) Tnil)) tvoid cc_default))
  [Etempvar _dst (tptr (Tstruct _frameItem noattr));
    Eaddrof (Evar _a (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))].
Definition rescale_public_rest := Ssequence rescale_public_read_point
  (Ssequence rescale_public_read_scale (Ssequence rescale_public_helper
    (Ssequence rescale_public_write (Sreturn (Some (Econst_int Int.one tint)))))).
Definition rescale_public_copy := Sassign (Evar _src (Tstruct _frameItem noattr))
  (Etempvar _src (Tstruct _frameItem noattr)).
Lemma rescale_public_body : fn_body f_simplicity_gej_rescale =
  Ssequence rescale_public_copy rescale_public_rest.
Proof. reflexivity. Qed.

Lemma rescale_public_symbols :
  (exists b, Genv.find_symbol secp_ge _read_gej = Some b /\
    Genv.find_funct_ptr secp_ge b = Some (Internal f_read_gej)) /\
  (exists b, Genv.find_symbol secp_ge _read_fe = Some b /\
    Genv.find_funct_ptr secp_ge b = Some (Internal f_read_fe)) /\
  (exists b, Genv.find_symbol secp_ge _secp256k1_gej_rescale = Some b /\
    Genv.find_funct_ptr secp_ge b = Some (Internal f_secp256k1_gej_rescale)) /\
  (exists b, Genv.find_symbol secp_ge _write_gej = Some b /\
    Genv.find_funct_ptr secp_ge b = Some (Internal f_write_gej)).
Proof.
  split; [exists (secp_symbol_block _read_gej); split; reflexivity|].
  split; [exists (secp_symbol_block _read_fe); split; reflexivity|].
  split; [exists (secp_symbol_block _secp256k1_gej_rescale); split; reflexivity|].
  exists (secp_symbol_block _write_gej); split; reflexivity.
Qed.
Local Opaque secp_ge.

Lemma exec_rescale_local_call fid fd ty1 ty2 id1 id2 e le m mf b1 b2 :
  (exists b, Genv.find_symbol secp_ge fid = Some b /\ Genv.find_funct_ptr secp_ge b = Some (Internal fd)) ->
  e!fid = None -> e!id1 = Some (b1,ty1) -> e!id2 = Some (b2,ty2) ->
  type_of_fundef (Internal fd) = Tfunction (Tcons (tptr ty1) (Tcons (tptr ty2) Tnil)) tvoid cc_default ->
  Clight2.eval_funcall secp_ge m (Internal fd) [Vptr b1 Ptrofs.zero;Vptr b2 Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m (rescale_local_call fid ty1 ty2 id1 id2) E0 le mf Out_normal.
Proof.
  intros (bf & HS & HF) HG H1 H2 HT HC; unfold rescale_local_call.
  eapply exec_Scall with (vf := Vptr bf Ptrofs.zero) (vargs := [Vptr b1 Ptrofs.zero;Vptr b2 Ptrofs.zero])
    (f := Internal fd) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [eapply eval_Evar_global; [exact HG|exact HS]|apply deref_loc_reference; reflexivity].
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; exact H1.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; exact H2.
      * reflexivity.
      * apply eval_Enil.
  - exact HF.
  - exact HT.
  - exact HC.
Qed.

Lemma exec_rescale_public_write le m mf bl bp bc bd dbase :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_write_gej)
    [Vptr bd (Ptrofs.repr dbase);Vptr bp Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (rescale_public_env bl bp bc) le m rescale_public_write E0 le mf Out_normal.
Proof.
  intros HD HC; destruct rescale_public_symbols as (_ & _ & _ & bf & HS & HF).
  unfold rescale_public_write.
  eapply exec_Scall with (vf := Vptr bf Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase);Vptr bp Ptrofs.zero])
    (f := Internal f_write_gej) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [eapply eval_Evar_global; [reflexivity|exact HS]|apply deref_loc_reference; reflexivity].
  - eapply eval_Econs.
    + apply eval_Etempvar; exact HD.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
      * reflexivity.
      * apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HC.
Qed.

Lemma exec_rescale_public_rest le m mr ms mn mf bl bp bc bd dbase :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_gej) [Vptr bp Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mr Vundef ->
  Clight2.eval_funcall secp_ge mr (Internal f_read_fe) [Vptr bc Ptrofs.zero;Vptr bl Ptrofs.zero] E0 ms Vundef ->
  Clight2.eval_funcall secp_ge ms (Internal f_secp256k1_gej_rescale)
    [Vptr bp Ptrofs.zero;Vptr bc Ptrofs.zero] E0 mn Vundef ->
  Clight2.eval_funcall secp_ge mn (Internal f_write_gej)
    [Vptr bd (Ptrofs.repr dbase);Vptr bp Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (rescale_public_env bl bp bc) le m rescale_public_rest E0 le mf
    (Out_return (Some (Vint Int.one,tint))).
Proof.
  intros HD HR HS HN HW; destruct rescale_public_symbols as (SR & SS & SN & SW).
  unfold rescale_public_rest, rescale_public_read_point, rescale_public_read_scale, rescale_public_helper.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le).
  - eapply exec_rescale_local_call; [exact SR|reflexivity|reflexivity|reflexivity|reflexivity|exact HR].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ms) (le1 := le).
    + eapply exec_rescale_local_call; [exact SS|reflexivity|reflexivity|reflexivity|reflexivity|exact HS].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mn) (le1 := le).
      * eapply exec_rescale_local_call; [exact SN|reflexivity|reflexivity|reflexivity|reflexivity|exact HN].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := le).
        -- eapply exec_rescale_public_write; eassumption.
        -- apply exec_Sreturn_some; constructor.
Qed.
