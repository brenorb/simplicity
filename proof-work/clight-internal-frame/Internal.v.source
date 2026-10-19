(** Readonly preservation for a checked closed set of original internal C
    functions. No external-call-properties assumption is needed. *)
From Coq Require Import ZArith List Bool Lia.
From compcert Require Import Coqlib AST Ctypes Cop Clight ClightBigstep Maps
  Integers Values Memory Events Globalenvs.
Require Import C.jet_clight_readonly C.jet_clight_readonly_frame C.jet_sx_mem.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition nonfunction_type (ty : type) : bool :=
  match ty with Tfunction _ _ _ => false | _ => true end.
Definition plain_env (e : env) : Prop :=
  forall id b ty, e!id = Some (b,ty) -> nonfunction_type ty = true.

Fixpoint internal_lookup (table : list (ident * function)) id : option function :=
  match table with
  | [] => None
  | (key,fd)::rest => if Pos.eqb key id then Some fd else internal_lookup rest id
  end.
Definition closed_callb table (a : expr) : bool :=
  match a with
  | Evar id (Tfunction _ _ _) =>
      match internal_lookup table id with Some _ => true | None => false end
  | _ => false
  end.
Fixpoint closed_stmtb table (s : statement) : bool :=
  match s with
  | Scall _ a _ => closed_callb table a
  | Ssequence s1 s2 | Sifthenelse _ s1 s2 | Sloop s1 s2 =>
      closed_stmtb table s1 && closed_stmtb table s2
  | Sskip | Sassign _ _ | Sset _ _ | Sbreak | Scontinue | Sreturn _ => true
  | _ => false
  end.
Definition allowed_call table (f : fundef) : Prop :=
  exists id fd, internal_lookup table id = Some fd /\ f = Internal fd.
Definition internal_table_ok (ge : genv) table : Prop :=
  forall id fd, internal_lookup table id = Some fd ->
    (exists b, Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some (Internal fd)) /\
    closed_stmtb table (fn_body fd) = true /\
    forallb (fun it => nonfunction_type (snd it)) (fn_vars fd) = true.

Lemma internal_lookup_in table id fd : internal_lookup table id = Some fd -> In (id,fd) table.
Proof.
  induction table as [|[key f] rest IH]; [discriminate|].
  cbn [internal_lookup]; destruct (Pos.eqb key id) eqn:HE.
  - apply Pos.eqb_eq in HE; subst key; intro H; injection H as ->; left; reflexivity.
  - intro H; right; exact (IH H).
Qed.

Lemma plain_empty : plain_env empty_env.
Proof. intros id b ty HE; rewrite PTree.gempty in HE; discriminate. Qed.
Lemma plain_set e id b ty : plain_env e -> nonfunction_type ty = true ->
  plain_env (PTree.set id (b,ty) e).
Proof.
  intros HE HT key b' ty' HK; rewrite PTree.gsspec in HK.
  destruct (peq key id); [injection HK as -> ->; exact HT|eapply HE; exact HK].
Qed.
Lemma alloc_plain ge e m vars e' m' :
  alloc_variables ge e m vars e' m' -> plain_env e ->
  forallb (fun it => nonfunction_type (snd it)) vars = true -> plain_env e'.
Proof.
  intro HA; induction HA; intros HE HV; [exact HE|].
  apply andb_true_iff in HV; destruct HV as [HT HR].
  apply IHHA; [apply plain_set; assumption|exact HR].
Qed.
Lemma entry_plain ge fd args m e le m' :
  function_entry2 ge fd args m e le m' ->
  forallb (fun it => nonfunction_type (snd it)) (fn_vars fd) = true -> plain_env e.
Proof. intros HE HV; inversion HE; subst; eapply alloc_plain; eauto using plain_empty. Qed.

Lemma direct_internal_call ge table e le m a vf f :
  internal_table_ok ge table -> plain_env e -> closed_callb table a = true ->
  eval_expr ge e le m a vf -> Genv.find_funct ge vf = Some f -> allowed_call table f.
Proof.
  intros HT HE HS HX HF.
  destruct a; try discriminate HS; destruct t; try discriminate HS.
  cbn [closed_callb] in HS.
  destruct (internal_lookup table i) as [fd|] eqn:HL; [|discriminate].
  destruct (HT i fd HL) as ((b & HSymbol & HFun) & _).
  inversion HX; subst.
  match goal with H : eval_lvalue _ _ _ _ (Evar _ _) _ _ _ |- _ => inversion H; subst end.
  - exfalso; match goal with HLocal : e!i = Some (?bl, Tfunction ?ts ?ty ?cc) |- _ =>
      pose proof (HE i bl (Tfunction ts ty cc) HLocal) as HBad; discriminate HBad
    end.
  - match goal with HD : deref_loc _ _ _ _ _ _ |- _ => inversion HD; subst; try discriminate end.
    assert (loc = b) by congruence; subst loc.
    cbn [Genv.find_funct] in HF.
    destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero); [|contradiction].
    rewrite HFun in HF; injection HF as <-; exists i, fd; auto.
Qed.

Theorem internal_exec_readback ge table : internal_table_ok ge table ->
  (forall e le m stmt t le' m' out,
    Clight2.exec_stmt ge e le m stmt t le' m' out ->
    plain_env e -> closed_stmtb table stmt = true -> readonly_readback m m') /\
  (forall m f args t m' result,
    Clight2.eval_funcall ge m f args t m' result ->
    allowed_call table f -> readonly_readback m m').
Proof.
  intro HT.
  apply (exec_stmt_funcall_ind function_entry2 ge
    (fun e le m stmt t le' m' out =>
      plain_env e -> closed_stmtb table stmt = true -> readonly_readback m m')
    (fun m f args t m' result => allowed_call table f -> readonly_readback m m')).
  all: intros.
  all: try solve [apply readonly_readback_refl].
  all: try solve [eapply assign_readonly_readback; eassumption].
  all: try solve [discriminate].
  all: try match goal with HS : closed_stmtb _ (Ssequence _ _) = true |- _ =>
    apply andb_true_iff in HS; destruct HS as [HS1 HS2]
  end.
  all: try solve [eauto 6 using readonly_readback_trans].
  - match goal with IH : allowed_call _ _ -> readonly_readback _ _ |- _ => apply IH end.
    eapply direct_internal_call; eassumption.
  - match goal with HS : closed_stmtb _ (Sifthenelse _ _ _) = true |- _ =>
      apply andb_true_iff in HS; destruct HS as [HS1 HS2]
    end; destruct b; eauto.
  - match goal with HS : closed_stmtb _ (Sloop _ _) = true |- _ =>
      apply andb_true_iff in HS; destruct HS as [HS1 HS2]
    end; eauto 8 using readonly_readback_trans.
  - match goal with HS : closed_stmtb _ (Sloop _ _) = true |- _ =>
      apply andb_true_iff in HS; destruct HS as [HS1 HS2]
    end; eauto 8 using readonly_readback_trans.
  - match goal with HS : closed_stmtb _ (Sloop _ _) = true |- _ =>
      pose proof HS as HLoop; apply andb_true_iff in HS; destruct HS as [HS1 HS2]
    end.
    eapply readonly_readback_trans; [apply H0; assumption|].
    eapply readonly_readback_trans; [apply H3; assumption|apply H5; assumption].
  - match goal with HA : allowed_call _ (Internal _) |- _ =>
      destruct HA as (id & fd & HL & HE); injection HE as HE; subst fd
    end.
    destruct (HT _ _ HL) as (_ & HS & HV).
    eapply readonly_readback_trans; [eapply entry2_readonly_readback; eassumption|].
    eapply readonly_readback_trans; [|eapply freelist_readonly_readback; eassumption].
    eauto using entry_plain.
  - match goal with HA : allowed_call _ (External _ _ _ _) |- _ =>
      destruct HA as (id & fd & HL & HE); discriminate HE
    end.
Qed.

Theorem internal_funcall_readonly_lframe ge table m f args t mf result b lo hi :
  internal_table_ok ge table -> allowed_call table f ->
  Clight2.eval_funcall ge m f args t mf result ->
  Mem.valid_block m b -> readonly_region_bounds m b lo hi ->
  Mem.range_perm mf b lo hi Cur Readable -> lframe (fun block _ => block = b) m mf.
Proof.
  intros HT HA HC HV HB HP; apply (readonly_region_lframe m mf b lo hi HV HB HP).
  exact (proj2 (internal_exec_readback ge table HT) m f args t mf result HC HA).
Qed.
