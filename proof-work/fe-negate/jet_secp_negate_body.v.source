(** Exact original public negation statement and helper call. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns.
Require Import C.jet_secp_public_copy C.jet_secp_public_body.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition secp_public_negate_stmt : statement :=
  Scall None
    (Evar jets_secp._secp256k1_fe_negate
      (Tfunction (Tcons (tptr secp_field_type)
        (Tcons (tptr secp_field_type) (Tcons tint Tnil))) tvoid cc_default))
    [Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type);
     Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type);
     Econst_int (Int.repr 1) tint].
Definition secp_fe_negate_rest : statement :=
  Ssequence secp_public_read_stmt
    (Ssequence secp_public_negate_stmt
      (Ssequence secp_public_write_stmt
        (Sreturn (Some (Econst_int (Int.repr 1) tint))))).
Lemma secp_fe_negate_body :
  fn_body f_simplicity_fe_negate =
    Ssequence (Sassign (Evar jets_secp._src secp_frame_type)
      (Etempvar jets_secp._src secp_frame_type)) secp_fe_negate_rest.
Proof. reflexivity. Qed.
Lemma secp_negate_helper_symbols :
  Genv.find_symbol secp_ge jets_secp._secp256k1_fe_negate =
    Some (secp_symbol_block jets_secp._secp256k1_fe_negate) /\
  Genv.find_funct secp_ge
    (Vptr (secp_symbol_block jets_secp._secp256k1_fe_negate) Ptrofs.zero) =
    Some (Internal f_secp256k1_fe_negate).
Proof. vm_compute; split; reflexivity. Qed.
Lemma exec_secp_public_negate le m mf bl ba :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
    [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vint Int.one] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (secp_public_env bl ba) le m
    secp_public_negate_stmt E0 le mf Out_normal.
Proof.
  intro HCall; destruct secp_negate_helper_symbols as [HPS HPF].
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block jets_secp._secp256k1_fe_negate) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vint Int.one])
    (f := Internal f_secp256k1_fe_negate) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HPS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
      * reflexivity.
      * eapply eval_Econs.
        -- constructor.
        -- reflexivity.
        -- apply eval_Enil.
  - exact HPF.
  - reflexivity.
  - exact HCall.
Qed.
Print Assumptions exec_secp_public_negate.
