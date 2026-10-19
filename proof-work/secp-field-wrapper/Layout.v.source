(** Exact original field-wrapper AST, member layout and inner-function linkage. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Cop Clight Clightdefs ClightBigstep Integers Values Maps Memory Events Globalenvs.
Require Import C.jet_sx_state C.jet_sx_eval C.jet_secp_linkage C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fe_type := Tstruct __5467 noattr.
Definition fe_array_expr id := Efield (Ederef (Etempvar id (tptr fe_type)) fe_type) _n (tarray tulong 5).
Definition inner_call_type := Tfunction (Tcons (tptr tulong) (Tcons (tptr tulong) (Tcons (tptr tulong) Tnil))) tvoid cc_default.
Lemma wrapper_body_source : fn_body f_secp256k1_fe_mul =
  Scall None (Evar _secp256k1_fe_mul_inner inner_call_type) [fe_array_expr _r; fe_array_expr _a; fe_array_expr _b].
Proof. reflexivity. Qed.
Lemma fe_members : option_map co_members ((genv_cenv secp_ge)!__5467) = Some [Member_plain _n (tarray tulong 5)].
Proof. vm_compute; reflexivity. Qed.
Lemma fe_n_layout : exists co, (genv_cenv secp_ge)!__5467 = Some co /\ field_offset secp_ge _n (co_members co) = Errors.OK (0, Full).
Proof.
  pose proof fe_members as HM; destruct ((genv_cenv secp_ge)!__5467) as [co|] eqn:HC; [|discriminate].
  inversion HM as [HMembers]; exists co; split; [reflexivity|rewrite HMembers; reflexivity].
Qed.
Lemma inner_symbols : Genv.find_symbol secp_ge _secp256k1_fe_mul_inner = Some (secp_symbol_block _secp256k1_fe_mul_inner) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block _secp256k1_fe_mul_inner) Ptrofs.zero) = Some (Internal f_secp256k1_fe_mul_inner).
Proof. vm_compute; split; reflexivity. Qed.

Local Opaque secp_ge.
Lemma eval_fe_array_expr e le m id b ofs : le!id = Some (Vptr b ofs) ->
  eval_expr secp_ge e le m (fe_array_expr id) (Vptr b ofs).
Proof.
  intro HT; destruct fe_n_layout as (co & HC & HO).
  unfold fe_array_expr, fe_type; rewrite <- (Ptrofs.add_zero ofs).
  eapply eval_Elvalue.
  - eapply eval_Efield_struct with (co := co) (delta := 0).
    + eapply eval_Elvalue.
      * apply eval_Ederef; apply eval_Etempvar; exact HT.
      * apply deref_loc_copy; reflexivity.
    + reflexivity.
    + exact HC.
    + exact HO.
  - apply deref_loc_reference; reflexivity.
Qed.
