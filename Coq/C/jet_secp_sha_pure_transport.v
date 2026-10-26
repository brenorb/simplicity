(** Reuse checked SHA initialization and byte I/O executions in the frozen
    secp program. The existing transport checker verifies all helper bodies,
    named calls and layouts; compression/dispatch are not covered here. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Clight ClightBigstep Globalenvs Memory Values Events.
Require Import C.jet_exec C.jet_transport C.jet_secp_linkage C.jet_sha_linkage.
Require Import C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Require C.jets_sha C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition secp_sha_pure_helpers : list (ident*function) :=
  [(jets_sha._sha256_iv,jets_sha.f_sha256_iv);(jets_sha._sha256_init,jets_sha.f_sha256_init);
   (jets_sha._ReadBE32,jets_sha.f_ReadBE32);(jets_sha._WriteBE32,jets_sha.f_WriteBE32);
   (jets_sha._WriteBE64,jets_sha.f_WriteBE64);(jets_sha._sha256_fromMidstate,jets_sha.f_sha256_fromMidstate)].
Definition secp_sha_source ge := ge=ge0 \/ ge=sha_ge.

Lemma secp_sha_lookup_core : map (secp_helper_lookup ge0) secp_sha_pure_helpers=
  map (fun p=>Some (Internal (snd p))) secp_sha_pure_helpers.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_lookup_sha : map (secp_helper_lookup sha_ge) secp_sha_pure_helpers=
  map (fun p=>Some (Internal (snd p))) secp_sha_pure_helpers.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_lookup_secp : map (secp_helper_lookup secp_ge) secp_sha_pure_helpers=
  map (fun p=>Some (Internal (snd p))) secp_sha_pure_helpers.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_helpers_checked_core :
  forallb (fun p=>fundef_okb ge0 secp_ge (map fst secp_sha_pure_helpers) (Internal (snd p)))
    secp_sha_pure_helpers=true.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_helpers_checked_sha :
  forallb (fun p=>fundef_okb sha_ge secp_ge (map fst secp_sha_pure_helpers) (Internal (snd p)))
    secp_sha_pure_helpers=true.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_helpers_closed_checked : forallb (fun p=>andb
  (closed_stmtb secp_sha_pure_helpers (fn_body (snd p)))
  (forallb (fun local=>nonfunction_type (snd local)) (fn_vars (snd p)))) secp_sha_pure_helpers=true.
Proof. vm_compute;reflexivity. Qed.

Local Opaque ge0 sha_ge secp_ge.
Lemma secp_sha_helpers_entries ge : secp_sha_source ge -> forall id f,In (id,f) secp_sha_pure_helpers ->
  exists b1 b2,
  Genv.find_symbol (genv_genv ge) id=Some b1 /\ Genv.find_funct_ptr (genv_genv ge) b1=Some (Internal f) /\
  Genv.find_symbol (genv_genv secp_ge) id=Some b2 /\ Genv.find_funct_ptr (genv_genv secp_ge) b2=Some (Internal f).
Proof.
  intros Source id f Member.
  assert (Lookup:secp_helper_lookup ge (id,f)=Some (Internal f)).
  { destruct Source as [Core|Sha];subst ge.
    - exact (secp_map_eq_in _ _ _ secp_sha_lookup_core (id,f) Member).
    - exact (secp_map_eq_in _ _ _ secp_sha_lookup_sha (id,f) Member). }
  destruct (secp_helper_lookup_exists ge id f Lookup) as (b1 & S1 & F1).
  destruct (secp_helper_lookup_exists secp_ge id f
    (secp_map_eq_in _ _ _ secp_sha_lookup_secp (id,f) Member)) as (b2 & S2 & F2).
  exists b1,b2;repeat split;assumption.
Qed.
Lemma secp_sha_helpers_ok ge : secp_sha_source ge -> forall id f,In (id,f) secp_sha_pure_helpers ->
  fundef_okb ge secp_ge (map fst secp_sha_pure_helpers) (Internal f)=true.
Proof.
  intros Source id f Member.
  assert (Checked:forallb (fun p=>fundef_okb ge secp_ge (map fst secp_sha_pure_helpers) (Internal (snd p)))
    secp_sha_pure_helpers=true) by (destruct Source as [Core|Sha];subst ge;
      [exact secp_sha_helpers_checked_core|exact secp_sha_helpers_checked_sha]).
  rewrite forallb_forall in Checked;exact (Checked (id,f) Member).
Qed.
Theorem secp_sha_transport_call ge id f m args trace mf result :
  secp_sha_source ge -> In (id,f) secp_sha_pure_helpers ->
  Clight2.eval_funcall ge m (Internal f) args trace mf result ->
  Clight2.eval_funcall secp_ge m (Internal f) args trace mf result.
Proof.
  intros Source Member Run;exact (transport_funcall ge secp_ge secp_sha_pure_helpers
    (secp_sha_helpers_entries ge Source) (secp_sha_helpers_ok ge Source) id f Member m args trace mf result Run).
Qed.

Lemma secp_sha_pure_table_ok : internal_table_ok secp_ge secp_sha_pure_helpers.
Proof.
  intros id f Lookup;pose proof (internal_lookup_in _ _ _ Lookup) as Member.
  destruct (secp_sha_helpers_entries ge0 (or_introl eq_refl) id f Member)
    as (b1 & b2 & S1 & F1 & S2 & F2).
  pose proof secp_sha_helpers_closed_checked as Checked;rewrite forallb_forall in Checked.
  specialize (Checked (id,f) Member);apply Bool.andb_true_iff in Checked;destruct Checked as [Body Vars].
  split;[exists b2;split;assumption|split;assumption].
Qed.
Lemma secp_sha_pure_lookup id f : In (id,f) secp_sha_pure_helpers ->
  internal_lookup secp_sha_pure_helpers id=Some f.
Proof.
  intros [Same|[Same|[Same|[Same|[Same|[Same|[]]]]]]];injection Same as <- <-;reflexivity.
Qed.
Theorem secp_sha_pure_preserved id f m args trace mf result :
  In (id,f) secp_sha_pure_helpers ->
  Clight2.eval_funcall secp_ge m (Internal f) args trace mf result -> readonly_preserved m mf.
Proof.
  intros Member Run;eapply (proj2 (internal_exec_preserved _ _ secp_sha_pure_table_ok));[exact Run|].
  exists id,f;split;[apply secp_sha_pure_lookup;exact Member|reflexivity].
Qed.
