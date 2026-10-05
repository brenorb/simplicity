(** Transport of [sha256_iv] and [sha256_init] (a separate list, so that the
    main helper list and its dependents need not be rebuilt).
    Reuse of the verified core helper executions in the SHA translation unit.
    The SHA program contains the core frame helpers with identical bodies;
    [jet_transport.v] turns any call of a checked helper in the core global
    environment into the same call in the SHA one, so no helper proof needs
    to be repeated again. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Clight Globalenvs ClightBigstep Memory Events Values.
Require Import C.jet_exec C.jet_transport C.jet_sha_linkage.
Require C.jets C.jets_sha.
Import ListNotations.
Local Open Scope Z_scope.
Local Opaque sha_ge ge0.
Set Default Timeout 1500.

Definition sha_init_helpers : list (ident * function) :=
  [ (jets._sha256_iv, jets.f_sha256_iv); (jets._sha256_init, jets.f_sha256_init) ].

Local Transparent sha_ge ge0.

Definition init_helper_lookup (ge : Clight.genv) (p : ident * function) : option fundef :=
  match Genv.find_symbol (Clight.genv_genv ge) (fst p) with
  | Some b => Genv.find_funct_ptr (Clight.genv_genv ge) b
  | None => None
  end.

Lemma init_map_eq_in {A B} (F G : A -> B) l : map F l = map G l -> forall x, In x l -> F x = G x.
Proof.
  induction l as [|y l IH]; simpl; intros H x Hx; [contradiction|].
  inversion H as [[H1 H2]]. destruct Hx as [->|Hx]; [exact H1|exact (IH H2 x Hx)].
Qed.

Lemma init_helper_lookup_core :
  map (init_helper_lookup ge0) sha_init_helpers =
  map (fun p => Some (Internal (snd p))) sha_init_helpers.
Proof. vm_compute; reflexivity. Qed.

Lemma init_helper_lookup_sha :
  map (init_helper_lookup sha_ge) sha_init_helpers =
  map (fun p => Some (Internal (snd p))) sha_init_helpers.
Proof. vm_compute; reflexivity. Qed.

Lemma init_helper_lookup_exists ge id f :
  init_helper_lookup ge (id, f) = Some (Internal f) ->
  exists b, Genv.find_symbol (Clight.genv_genv ge) id = Some b /\
            Genv.find_funct_ptr (Clight.genv_genv ge) b = Some (Internal f).
Proof.
  unfold init_helper_lookup; simpl. destruct (Genv.find_symbol (Clight.genv_genv ge) id) as [b|]; [|discriminate].
  intros H; exists b; auto.
Qed.

Lemma sha_init_helpers_entries : forall id f, In (id, f) sha_init_helpers ->
  exists b1 b2,
    Genv.find_symbol (Clight.genv_genv ge0) id = Some b1 /\
    Genv.find_funct_ptr (Clight.genv_genv ge0) b1 = Some (Internal f) /\
    Genv.find_symbol (Clight.genv_genv sha_ge) id = Some b2 /\
    Genv.find_funct_ptr (Clight.genv_genv sha_ge) b2 = Some (Internal f).
Proof.
  intros id f Hin.
  destruct (init_helper_lookup_exists ge0 id f (init_map_eq_in _ _ _ init_helper_lookup_core (id, f) Hin))
    as (b1 & Hs1 & Hf1).
  destruct (init_helper_lookup_exists sha_ge id f (init_map_eq_in _ _ _ init_helper_lookup_sha (id, f) Hin))
    as (b2 & Hs2 & Hf2).
  exists b1, b2; auto.
Qed.

Definition init_helpers_okb : bool :=
  forallb (fun p => fundef_okb ge0 sha_ge (map fst sha_init_helpers) (Internal (snd p)))
    sha_init_helpers.

Lemma init_helpers_okb_true : init_helpers_okb = true.
Proof. vm_compute; reflexivity. Qed.

Lemma sha_init_helpers_ok : forall id f, In (id, f) sha_init_helpers ->
  fundef_okb ge0 sha_ge (map fst sha_init_helpers) (Internal f) = true.
Proof.
  intros id f [E|[E|[]]]; injection E as <- <-; vm_compute; reflexivity.
Qed.

Local Opaque sha_ge ge0.

(** A call of a core helper in the core environment is the same call in the
    SHA environment. *)
Theorem init_sha_transport_call id f (Hin : In (id, f) sha_init_helpers) m args t m' res :
  Clight2.eval_funcall ge0 m (Internal f) args t m' res ->
  Clight2.eval_funcall sha_ge m (Internal f) args t m' res.
Proof.
  exact (transport_funcall ge0 sha_ge sha_init_helpers
    sha_init_helpers_entries sha_init_helpers_ok id f Hin m args t m' res).
Qed.
