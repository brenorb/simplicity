(** The symbolic executor without oracles: tables of internal functions and
    the soundness statement for runs that log no event. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

Definition int_table (l : list (ident * function)) : list (ident * fentry) :=
  map (fun p => (fst p, FInt (snd p))) l.

Lemma int_table_lookup l id ent :
  flookup (int_table l) id = Some ent -> exists f, ent = FInt f /\ In (id, f) l.
Proof.
  induction l as [|[i f] t IH]; simpl; [discriminate|].
  destruct (Pos.eqb i id) eqn:E.
  - apply Pos.eqb_eq in E. intros H; inversion H; subst. exists f. split; [reflexivity|left; reflexivity].
  - intros H. destruct (IH H) as (f' & E' & Hin). exists f'. split; [exact E'|right; exact Hin].
Qed.

Fixpoint leaves_log_nil (r : res) : bool :=
  match r with
  | RDone Σ _ => match slog Σ with [] => true | _ => false end
  | RIf _ a b => leaves_log_nil a && leaves_log_nil b
  end.

Lemma leaves_log_nil_sel ρ β r : leaves_log_nil r = true -> slog (fst (rsel ρ β r)) = [].
Proof.
  induction r; simpl; intros H.
  - destruct (slog Σ); [reflexivity|discriminate].
  - apply andb_true_iff in H. destruct H. destruct (truth ρ β c); auto.
Qed.

Definition symbol_lookup (ge : genv) (p : ident * function) : option fundef :=
  match Genv.find_symbol ge (fst p) with
  | Some b => Genv.find_funct_ptr ge b
  | None => None
  end.

Lemma symbol_lookup_table ge l :
  map (symbol_lookup ge) l = map (fun p => Some (Internal (snd p))) l ->
  forall id f, In (id, f) l ->
    exists b, Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some (Internal f).
Proof.
  induction l as [|p t IH]; simpl; intros H id f Hin; [contradiction|].
  inversion H as [[H1 H2]]. destruct Hin as [->|Hin]; [|exact (IH H2 id f Hin)].
  unfold symbol_lookup in H1. simpl in H1.
  destruct (Genv.find_symbol ge id) as [b|]; [|discriminate]. exists b. auto.
Qed.

Section PURE.
Variable ge : genv.
Variable l : list (ident * function).
Hypothesis Hl : forall id f, In (id, f) l ->
  exists b, Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some (Internal f).

Theorem xfun_pure n fd xs regs nv rr :
  xfun (genv_cenv ge) [] (int_table l) n fd xs regs [] nv = Some rr ->
  leaves_log_nil rr = true ->
  forall ρ β m, rep ρ β regs m ->
  exists m' vres,
    ClightBigstep.eval_funcall function_entry2 ge m (Internal fd) (map (den ρ (lay β)) xs) E0 m' vres /\
    rep ρ β (sregs (fst (rsel ρ (lay β) rr))) m' /\
    match (stemps (fst (rsel ρ (lay β) rr)))!1%positive with
    | Some x => vres = den ρ (lay β) x
    | None => vres = Vundef
    end /\
    map rshape (sregs (fst (rsel ρ (lay β) rr))) = map rshape regs /\
    lframe (fun b o => ~ foot β (map rshape regs) b o) m m'.
Proof.
  intros H Hnil ρ β m Hrep.
  destruct (xfun_top_sound ge [] (int_table l) (fun _ _ => True) (fun _ _ _ => True) (fun _ => False)
              ltac:(auto) ltac:(intros; contradiction)) with (n := n) (fd := fd) (xs := xs) (regs := regs)
              (log := @nil event) (nv := nv) (rr := rr) (ρ := ρ) (β := β) (m := m)
    as (m' & vres & Hev & Hrep' & Hret & Hsh & _ & Hun).
  - intros id ent Hlk. destruct (int_table_lookup _ _ _ Hlk) as (f & -> & Hin). split; [|exact I].
    exact (Hl id f Hin).
  - exact H.
  - exact Hrep.
  - split; [intros id r ty V; discriminate|intros id r ty V; discriminate].
  - intros r _ [].
  - exact I.
  - rewrite (leaves_log_nil_sel _ _ _ Hnil). constructor.
  - exists m', vres. split; [exact Hev|]. split; [exact Hrep'|]. split; [exact Hret|]. split; [exact Hsh|].
    eapply lframe_implies; [exact Hun|]. intros b o Hf Hv. split; [exact Hv|]. split; [exact Hf|tauto].
Qed.
End PURE.
