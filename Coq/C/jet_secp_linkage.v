(** Linkage of the secp256k1 translation unit and reuse of the verified core
    helper executions in it.  The program contains the core frame helpers
    with identical bodies; [jet_transport.v] turns any call of a checked
    helper in the core global environment into the same call here. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Clight Globalenvs ClightBigstep Memory Events Values.
Require Import C.jet_exec C.jet_transport.
Require C.jets C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 1500.

Definition secp_ge : Clight.genv := Clight.globalenv jets_secp.prog.
Definition secp_symbol_block (id : ident) : block :=
  match Genv.find_symbol (Clight.genv_genv secp_ge) id with
  | Some b => b | None => 1%positive end.

Definition secp_core_helpers : list (ident * function) :=
  [ (jets._LSBclear, jets.f_LSBclear); (jets._LSBkeep, jets.f_LSBkeep);
    (jets._simplicity_write8, jets.f_simplicity_write8);
    (jets._simplicity_write16, jets.f_simplicity_write16);
    (jets._simplicity_write32, jets.f_simplicity_write32);
    (jets._simplicity_write64, jets.f_simplicity_write64);
    (jets._simplicity_read4, jets.f_simplicity_read4);
    (jets._simplicity_read8, jets.f_simplicity_read8);
    (jets._simplicity_read16, jets.f_simplicity_read16);
    (jets._simplicity_read32, jets.f_simplicity_read32);
    (jets._simplicity_read64, jets.f_simplicity_read64);
    (jets._peekBit, jets.f_peekBit);
    (jets._readBit, jets.f_readBit);
    (jets._writeBit, jets.f_writeBit);
    (jets._forwardBits, jets.f_forwardBits);
    (jets._skipBits, jets.f_skipBits);
    (jets._write32s, jets.f_write32s);
    (jets._read32s, jets.f_read32s);
    (jets._write8s, jets.f_write8s);
    (jets._read8s, jets.f_read8s) ].

Definition secp_helper_lookup (ge : Clight.genv) (p : ident * function) : option fundef :=
  match Genv.find_symbol (Clight.genv_genv ge) (fst p) with
  | Some b => Genv.find_funct_ptr (Clight.genv_genv ge) b
  | None => None
  end.

Lemma secp_map_eq_in {A B} (F G : A -> B) l : map F l = map G l -> forall x, In x l -> F x = G x.
Proof.
  induction l as [|y l IH]; simpl; intros H x Hx; [contradiction|].
  inversion H as [[H1 H2]]. destruct Hx as [->|Hx]; [exact H1|exact (IH H2 x Hx)].
Qed.

Lemma secp_helper_lookup_core :
  map (secp_helper_lookup ge0) secp_core_helpers =
  map (fun p => Some (Internal (snd p))) secp_core_helpers.
Proof. vm_compute; reflexivity. Qed.

Lemma secp_helper_lookup_secp :
  map (secp_helper_lookup secp_ge) secp_core_helpers =
  map (fun p => Some (Internal (snd p))) secp_core_helpers.
Proof. vm_compute; reflexivity. Qed.

Lemma secp_helper_lookup_exists ge id f :
  secp_helper_lookup ge (id, f) = Some (Internal f) ->
  exists b, Genv.find_symbol (Clight.genv_genv ge) id = Some b /\
            Genv.find_funct_ptr (Clight.genv_genv ge) b = Some (Internal f).
Proof.
  unfold secp_helper_lookup; simpl. destruct (Genv.find_symbol (Clight.genv_genv ge) id) as [b|]; [|discriminate].
  intros H; exists b; auto.
Qed.

Lemma secp_core_helpers_entries : forall id f, In (id, f) secp_core_helpers ->
  exists b1 b2,
    Genv.find_symbol (Clight.genv_genv ge0) id = Some b1 /\
    Genv.find_funct_ptr (Clight.genv_genv ge0) b1 = Some (Internal f) /\
    Genv.find_symbol (Clight.genv_genv secp_ge) id = Some b2 /\
    Genv.find_funct_ptr (Clight.genv_genv secp_ge) b2 = Some (Internal f).
Proof.
  intros id f Hin.
  destruct (secp_helper_lookup_exists ge0 id f (secp_map_eq_in _ _ _ secp_helper_lookup_core (id, f) Hin))
    as (b1 & Hs1 & Hf1).
  destruct (secp_helper_lookup_exists secp_ge id f (secp_map_eq_in _ _ _ secp_helper_lookup_secp (id, f) Hin))
    as (b2 & Hs2 & Hf2).
  exists b1, b2; auto.
Qed.

Definition secp_helpers_okb : bool :=
  forallb (fun p => fundef_okb ge0 secp_ge (map fst secp_core_helpers) (Internal (snd p)))
    secp_core_helpers.

Lemma secp_helpers_okb_true : secp_helpers_okb = true.
Proof. vm_compute; reflexivity. Qed.

Lemma secp_core_helpers_ok : forall id f, In (id, f) secp_core_helpers ->
  fundef_okb ge0 secp_ge (map fst secp_core_helpers) (Internal f) = true.
Proof.
  intros id f Hin. pose proof secp_helpers_okb_true as H. unfold secp_helpers_okb in H.
  rewrite forallb_forall in H. exact (H (id, f) Hin).
Qed.

Local Opaque secp_ge ge0.

(** A call of a core helper in the core environment is the same call in the
    secp256k1 environment. *)
Theorem secp_transport_call id f (Hin : In (id, f) secp_core_helpers) m args t m' res :
  Clight2.eval_funcall ge0 m (Internal f) args t m' res ->
  Clight2.eval_funcall secp_ge m (Internal f) args t m' res.
Proof.
  exact (transport_funcall ge0 secp_ge secp_core_helpers
    secp_core_helpers_entries secp_core_helpers_ok id f Hin m args t m' res).
Qed.
