(** Actual field reads in the Elements version jet's own global environment.
    Physical observations only; the primitive/output consumer comes later. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Maps Memory Values.
Require Import C.jets_elements C.jet_elements_linkage.
Import Ctypes Values Mem ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma eval_elements_env_tx e le m be base bt txbase :
  0 <= base <= Ptrofs.max_unsigned ->
  le!_env = Some (Vptr be (Ptrofs.repr base)) ->
  Mem.load Mptr m be base = Some (Vptr bt (Ptrofs.repr txbase)) ->
  eval_expr elements_ge e le m
    (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr)))
      (Tstruct _txEnv noattr)) _tx (tptr (Tstruct _elementsTransaction noattr)))
    (Vptr bt (Ptrofs.repr txbase)).
Proof.
  intros HB HE HM. pose proof elements_env_tx_field as HField.
  destruct ((Clight.genv_cenv elements_ge)!_txEnv) as [co|] eqn:HCo; [|contradiction].
  eapply eval_Elvalue.
  - eapply eval_Efield_struct with (co := co) (delta := 0).
    + eapply eval_Elvalue; [apply eval_Ederef, eval_Etempvar; exact HE|].
      apply deref_loc_copy; reflexivity.
    + reflexivity.
    + exact HCo.
    + exact HField.
  - apply deref_loc_value with (chunk := Mptr); [reflexivity|].
    unfold Mem.loadv. rewrite Ptrofs.add_zero, Ptrofs.unsigned_repr by exact HB.
    exact HM.
Qed.

Lemma eval_elements_tx_version e le m bt base version :
  0 <= base -> base + 760 <= Ptrofs.max_unsigned ->
  le!_t'1 = Some (Vptr bt (Ptrofs.repr base)) ->
  Mem.load Mint64 m bt (base + 720) = Some (Vlong version) ->
  eval_expr elements_ge e le m
    (Efield (Ederef (Etempvar _t'1 (tptr (Tstruct _elementsTransaction noattr)))
      (Tstruct _elementsTransaction noattr)) _version tulong) (Vlong version).
Proof.
  intros HB HMax HE HM. pose proof elements_tx_version_field as HField.
  destruct ((Clight.genv_cenv elements_ge)!_elementsTransaction) as [co|] eqn:HCo; [|contradiction].
  eapply eval_Elvalue.
  - eapply eval_Efield_struct with (co := co) (delta := 720).
    + eapply eval_Elvalue; [apply eval_Ederef, eval_Etempvar; exact HE|].
      apply deref_loc_copy; reflexivity.
    + reflexivity.
    + exact HCo.
    + exact HField.
  - apply deref_loc_value with (chunk := Mint64); [reflexivity|].
    unfold Mem.loadv, Ptrofs.add.
    rewrite (Ptrofs.unsigned_repr base) by lia.
    change (Ptrofs.unsigned (Ptrofs.repr 720)) with 720.
    rewrite Ptrofs.unsigned_repr by lia; exact HM.
Qed.
