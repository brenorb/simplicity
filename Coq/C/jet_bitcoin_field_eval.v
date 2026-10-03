(** Generic evaluation of struct-field expressions in the Bitcoin translation
    unit.  Offsets are checked by computation against the generated composite
    environment; the lemmas here only connect them to Clight expression
    evaluation, so each consumer states one [bitcoin_field_at] fact per field. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Maps Memory Values Errors.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage.
Import Ctypes Values Mem ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge.
Set Default Timeout 10.

Definition bitcoin_field_at (sid field : ident) (delta : Z) : Prop :=
  match (Clight.genv_cenv bitcoin_ge)!sid with
  | Some co => field_offset (Clight.genv_cenv bitcoin_ge) field (co_members co) = OK (delta, Full)
  | None => False
  end.

Definition bitcoin_struct t sid := t = Tstruct sid noattr.

(** [*x] for a temporary [x] of type [struct sid *] evaluates to its location. *)
Lemma eval_bitcoin_deref_struct e le m x sid b ofs :
  le!x = Some (Vptr b ofs) ->
  eval_expr bitcoin_ge e le m
    (Ederef (Etempvar x (tptr (Tstruct sid noattr))) (Tstruct sid noattr)) (Vptr b ofs).
Proof.
  intros HE. eapply eval_Elvalue.
  - apply eval_Ederef, eval_Etempvar; exact HE.
  - apply deref_loc_copy; reflexivity.
Qed.

(** Field [field] of a struct-typed expression [a]: its l-value. *)
Lemma eval_bitcoin_field_lvalue e le m a sid field delta ty b ofs :
  typeof a = Tstruct sid noattr -> bitcoin_field_at sid field delta ->
  eval_expr bitcoin_ge e le m a (Vptr b ofs) ->
  eval_lvalue bitcoin_ge e le m (Efield a field ty) b (Ptrofs.add ofs (Ptrofs.repr delta)) Full.
Proof.
  intros HT HF HA. unfold bitcoin_field_at in HF.
  destruct ((Clight.genv_cenv bitcoin_ge)!sid) as [co|] eqn:HCo; [|contradiction].
  eapply eval_Efield_struct with (co := co) (delta := delta); eauto.
Qed.

(** A scalar-valued field. *)
Lemma eval_bitcoin_field_value e le m a sid field delta ty chunk b ofs v :
  typeof a = Tstruct sid noattr -> bitcoin_field_at sid field delta ->
  access_mode ty = By_value chunk ->
  eval_expr bitcoin_ge e le m a (Vptr b ofs) ->
  Mem.loadv chunk m (Vptr b (Ptrofs.add ofs (Ptrofs.repr delta))) = Some v ->
  eval_expr bitcoin_ge e le m (Efield a field ty) v.
Proof.
  intros HT HF HM HA HL. eapply eval_Elvalue.
  - eapply eval_bitcoin_field_lvalue; eauto.
  - eapply deref_loc_value; [exact HM|exact HL].
Qed.

(** A struct-valued field evaluates to its location. *)
Lemma eval_bitcoin_field_struct e le m a sid field delta sid' b ofs :
  typeof a = Tstruct sid noattr -> bitcoin_field_at sid field delta ->
  eval_expr bitcoin_ge e le m a (Vptr b ofs) ->
  eval_expr bitcoin_ge e le m (Efield a field (Tstruct sid' noattr))
    (Vptr b (Ptrofs.add ofs (Ptrofs.repr delta))).
Proof.
  intros HT HF HA. eapply eval_Elvalue.
  - eapply eval_bitcoin_field_lvalue; eauto.
  - apply deref_loc_copy; reflexivity.
Qed.

(** An array-valued field decays to its address. *)
Lemma eval_bitcoin_field_array e le m a sid field delta ty b ofs :
  typeof a = Tstruct sid noattr -> bitcoin_field_at sid field delta ->
  (forall chunk, access_mode ty <> By_value chunk) -> access_mode ty = By_reference ->
  eval_expr bitcoin_ge e le m a (Vptr b ofs) ->
  eval_expr bitcoin_ge e le m (Efield a field ty)
    (Vptr b (Ptrofs.add ofs (Ptrofs.repr delta))).
Proof.
  intros HT HF _ HM HA. eapply eval_Elvalue.
  - eapply eval_bitcoin_field_lvalue; eauto.
  - apply deref_loc_reference; exact HM.
Qed.

(** Address arithmetic for in-range offsets. *)
Lemma bitcoin_ptr_add_repr base delta :
  0 <= base -> 0 <= delta -> base + delta <= Ptrofs.max_unsigned ->
  Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr delta) = Ptrofs.repr (base + delta).
Proof.
  intros HB HD HM. unfold Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr base) by lia.
  rewrite (Ptrofs.unsigned_repr delta) by lia. reflexivity.
Qed.

Lemma bitcoin_loadv_repr chunk m b base v :
  0 <= base <= Ptrofs.max_unsigned ->
  Mem.load chunk m b base = Some v ->
  Mem.loadv chunk m (Vptr b (Ptrofs.repr base)) = Some v.
Proof.
  intros HB HL. unfold Mem.loadv. rewrite Ptrofs.unsigned_repr by lia. exact HL.
Qed.

(** Offsets of the structures read by the Bitcoin getters. *)
Lemma bitcoin_txEnv_tx : bitcoin_field_at _txEnv _tx 0.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_txEnv_taproot : bitcoin_field_at _txEnv _taproot 8.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_txEnv_ix : bitcoin_field_at _txEnv _ix 48.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_tapEnv_scriptCMR : bitcoin_field_at _bitcoinTapEnv _scriptCMR 136.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_tapEnv_internalKey : bitcoin_field_at _bitcoinTapEnv _internalKey 104.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_midstate_s : bitcoin_field_at _sha256_midstate _s 0.
Proof. vm_compute; reflexivity. Qed.
