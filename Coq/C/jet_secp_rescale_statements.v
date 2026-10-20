(** The actual four Scall nodes of gej_rescale, including their field
    addresses, local zz argument, global linkage and caller temporaries. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values Globalenvs Errors.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_point_write_run C.jet_secp_rescale_prefix.
Require Import C.jet_secp_gej_infinity_layout.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition rescale_coordinate_id k : ident := match k with PointX => _x | PointY => _y | PointZ => _z end.
Definition rescale_coordinate_address k :=
  Eaddrof (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
    (Tstruct __6123 noattr)) (rescale_coordinate_id k) (Tstruct __5467 noattr))
    (tptr (Tstruct __5467 noattr)).
Definition rescale_factor_address (squared : bool) :=
  if squared then Eaddrof (Evar _zz (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr))
  else Etempvar _s (tptr (Tstruct __5467 noattr)).
Definition rescale_multiply_statement k squared :=
  Scall None (Evar _secp256k1_fe_mul (Tfunction
    (Tcons (tptr (Tstruct __5467 noattr)) (Tcons (tptr (Tstruct __5467 noattr))
      (Tcons (tptr (Tstruct __5467 noattr)) Tnil))) tvoid cc_default))
    [rescale_coordinate_address k;rescale_coordinate_address k;rescale_factor_address squared].

Lemma rescale_rest_source : rescale_rest =
  Ssequence (rescale_multiply_statement PointX true)
    (Ssequence (rescale_multiply_statement PointY true)
      (Ssequence (rescale_multiply_statement PointY false) (rescale_multiply_statement PointZ false))).
Proof. reflexivity. Qed.

Lemma rescale_coordinate_layout k : exists co,
  (genv_cenv secp_ge)!__6123 = Some co /\
  field_offset (genv_cenv secp_ge) (rescale_coordinate_id k) (co_members co) =
    OK (point_coordinate_offset k, Full).
Proof.
  apply gej_infinity_field_layout; destruct k; cbn; tauto.
Qed.
Lemma rescale_zero_address k :
  Ptrofs.add Ptrofs.zero (Ptrofs.repr (point_coordinate_offset k)) = Ptrofs.repr (point_coordinate_offset k).
Proof. destruct k; reflexivity. Qed.
Lemma rescale_multiply_symbol : exists b,
  Genv.find_symbol secp_ge _secp256k1_fe_mul = Some b /\
  Genv.find_funct_ptr secp_ge b = Some (Internal f_secp256k1_fe_mul).
Proof. apply secp_pure_ok; unfold secp_pure; repeat (first [left; reflexivity|right]). Qed.

Local Opaque secp_ge rescale_rest.
Lemma eval_rescale_coordinate e le m bp k : le!_r = Some (Vptr bp Ptrofs.zero) ->
  eval_expr secp_ge e le m (rescale_coordinate_address k) (Vptr bp (Ptrofs.repr (point_coordinate_offset k))).
Proof.
  intro HR; unfold rescale_coordinate_address; apply eval_Eaddrof.
  rewrite <- rescale_zero_address.
  destruct (rescale_coordinate_layout k) as (co & HC & HO).
  eapply eval_Efield_struct with (co := co) (delta := point_coordinate_offset k).
  - eapply eval_Elvalue.
    + apply eval_Ederef; apply eval_Etempvar; exact HR.
    + apply deref_loc_copy; reflexivity.
  - reflexivity.
  - exact HC.
  - exact HO.
Qed.

Lemma eval_rescale_factor squared e le m bs bz :
  le!_s = Some (Vptr bs Ptrofs.zero) -> e!_zz = Some (bz,Tstruct __5467 noattr) ->
  eval_expr secp_ge e le m (rescale_factor_address squared) (Vptr (if squared then bz else bs) Ptrofs.zero).
Proof.
  intros HS HZ; destruct squared; cbn [rescale_factor_address].
  - apply eval_Eaddrof; apply eval_Evar_local; exact HZ.
  - apply eval_Etempvar; exact HS.
Qed.

Lemma exec_rescale_multiply_from_call k (squared : bool) e le m mf bp bs bz :
  le!_r = Some (Vptr bp Ptrofs.zero) -> le!_s = Some (Vptr bs Ptrofs.zero) ->
  e!_zz = Some (bz,Tstruct __5467 noattr) -> e!_secp256k1_fe_mul = None ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bp (Ptrofs.repr (point_coordinate_offset k));
     Vptr bp (Ptrofs.repr (point_coordinate_offset k));Vptr (if squared then bz else bs) Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m (rescale_multiply_statement k squared) E0 le mf Out_normal.
Proof.
  intros HR HS HZ HGlobal HCall.
  destruct rescale_multiply_symbol as (bf & HF & HFn).
  unfold rescale_multiply_statement.
  eapply exec_Scall with (vf := Vptr bf Ptrofs.zero)
    (vargs := [Vptr bp (Ptrofs.repr (point_coordinate_offset k));
      Vptr bp (Ptrofs.repr (point_coordinate_offset k));Vptr (if squared then bz else bs) Ptrofs.zero])
    (f := Internal f_secp256k1_fe_mul) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [exact HGlobal|exact HF].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_rescale_coordinate; exact HR.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_rescale_coordinate; exact HR.
      * reflexivity.
      * eapply eval_Econs.
        -- exact (eval_rescale_factor squared e le m bs bz HS HZ).
        -- destruct squared; reflexivity.
        -- apply eval_Enil.
  - exact HFn.
  - reflexivity.
  - exact HCall.
Qed.

Theorem exec_rescale_rest_from_calls e le m m1 m2 m3 mf bp bs bz :
  le!_r = Some (Vptr bp Ptrofs.zero) -> le!_s = Some (Vptr bs Ptrofs.zero) ->
  e!_zz = Some (bz,Tstruct __5467 noattr) -> e!_secp256k1_fe_mul = None ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr bz Ptrofs.zero] E0 m1 Vundef ->
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_mul)
    [Vptr bp (Ptrofs.repr 40);Vptr bp (Ptrofs.repr 40);Vptr bz Ptrofs.zero] E0 m2 Vundef ->
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_mul)
    [Vptr bp (Ptrofs.repr 40);Vptr bp (Ptrofs.repr 40);Vptr bs Ptrofs.zero] E0 m3 Vundef ->
  Clight2.eval_funcall secp_ge m3 (Internal f_secp256k1_fe_mul)
    [Vptr bp (Ptrofs.repr 80);Vptr bp (Ptrofs.repr 80);Vptr bs Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m rescale_rest E0 le mf Out_normal.
Proof.
  intros HR HS HZ HG C1 C2 C3 C4; rewrite rescale_rest_source.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le).
  - eapply exec_rescale_multiply_from_call; eassumption.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2) (le1 := le).
    + eapply exec_rescale_multiply_from_call; eassumption.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m3) (le1 := le).
      * eapply exec_rescale_multiply_from_call; eassumption.
      * eapply exec_rescale_multiply_from_call; eassumption.
Qed.
