(** Original fe_is_zero statements and their Clight call composition. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events Globalenvs.
Require Import C.jet_exec C.jet_readBit_layout C.jet_secp_linkage C.jets_secp C.jet_secp_fns.
Require Import C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_odd_body.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition secp_public_zero_stmt : statement :=
  Scall (Some jets_secp._t'1)
    (Evar jets_secp._secp256k1_fe_is_zero
      (Tfunction (Tcons (tptr secp_field_type) Tnil) tint cc_default))
    [Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type)].
Definition secp_fe_zero_rest : statement :=
  Ssequence secp_public_read_stmt
    (Ssequence (Ssequence secp_public_zero_stmt secp_public_bit_write_stmt)
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))).
Lemma secp_fe_zero_body :
  fn_body f_simplicity_fe_is_zero =
    Ssequence (Sassign (Evar jets_secp._src secp_frame_type)
      (Etempvar jets_secp._src secp_frame_type)) secp_fe_zero_rest.
Proof. reflexivity. Qed.
Lemma secp_zero_helper_symbols :
  Genv.find_symbol secp_ge jets_secp._secp256k1_fe_is_zero =
    Some (secp_symbol_block jets_secp._secp256k1_fe_is_zero) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block jets_secp._secp256k1_fe_is_zero) Ptrofs.zero) =
    Some (Internal f_secp256k1_fe_is_zero).
Proof. vm_compute; split; reflexivity. Qed.
Lemma exec_secp_public_zero le m mf bl ba (bit : bool) :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_zero)
    [Vptr ba Ptrofs.zero] E0 mf (Vint (bit_int bit)) ->
  Clight2.exec_stmt secp_ge (secp_public_env bl ba) le m secp_public_zero_stmt E0
    (PTree.set jets_secp._t'1 (Vint (bit_int bit)) le) mf Out_normal.
Proof.
  intro HCall; destruct secp_zero_helper_symbols as [HPS HPF].
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block jets_secp._secp256k1_fe_is_zero) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero]) (f := Internal f_secp256k1_fe_is_zero) (vres := Vint (bit_int bit)).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HPS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - exact HPF.
  - reflexivity.
  - exact HCall.
Qed.
