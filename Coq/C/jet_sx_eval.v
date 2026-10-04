(** Symbolic evaluation of Clight expressions and its soundness. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Globalenvs Errors Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Record sstate := mkst { stemps : PTree.t sx; sregs : list region }.
Definition venv := list (ident * (nat * type)).

Fixpoint vlookup (ve : venv) (id : ident) : option (nat * type) :=
  match ve with
  | [] => None
  | (i, v) :: t => if Pos.eqb i id then Some v else vlookup t id
  end.

Definition lv_var (ve gv : venv) (id : ident) (ty : type) : option (nat * Z) :=
  match vlookup ve id with
  | Some (r, ty') => if type_eq ty ty' then Some (r, 0) else None
  | None => match vlookup gv id with Some (r, _) => Some (r, 0) | None => None end
  end.
Definition lv_deref (xa : option sx) : option (nat * Z) :=
  match xa with Some (XP r d) => Some (r, d) | _ => None end.
Definition lv_field (ce : composite_env) (xa : option sx) (ta : type) (f : ident) : option (nat * Z) :=
  match xa, ta with
  | Some (XP r d), Tstruct id _ =>
      match ce!id with
      | Some co =>
          match field_offset ce f (co_members co) with
          | OK (delta, Full) => Some (r, d + delta)
          | _ => None
          end
      | None => None
      end
  | _, _ => None
  end.

Definition xptradd (ce : composite_env) (xa : sx) (ta : type) (xb : sx) (tb : type) : option sx :=
  match xa with
  | XP r d =>
      match ta with
      | Tpointer ty _ | Tarray ty _ _ =>
          match xb, tb with
          | XIc n, Tint _ _ _ =>
              Some (XP r (d + sizeof ce ty *
                 match isg tb with Signed => Int.signed n | Unsigned => Int.unsigned n end))
          | XLc n, Tlong _ _ => Some (XP r (d + sizeof ce ty * Int64.unsigned n))
          | _, _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition xbinop (ce : composite_env) (op : binary_operation) (xa : sx) (ta : type) (xb : sx) (tb : type) :=
  match op, xa with
  | Oadd, XP _ _ => xptradd ce xa ta xb tb
  | _, _ => xbin op xa ta xb tb
  end.

Section XEXPR.
Variable ce : composite_env.
Variables ve gv : venv.

Definition xlv_of (rec : expr -> option sx) (a : expr) : option (nat * Z) :=
  match a with
  | Evar id ty => lv_var ve gv id ty
  | Ederef b _ => lv_deref (rec b)
  | Efield b f _ => lv_field ce (rec b) (typeof b) f
  | _ => None
  end.

Definition load_lv (Σ : sstate) (lv : option (nat * Z)) (ty : type) : option sx :=
  match lv with Some (r, d) => xload (sregs Σ) r d ty | None => None end.

Fixpoint xexpr (Σ : sstate) (a : expr) : option sx :=
  match a with
  | Econst_int i _ => Some (XIc i)
  | Econst_long l _ => Some (XLc l)
  | Etempvar id _ => (stemps Σ)!id
  | Eaddrof b _ => match xlv_of (xexpr Σ) b with Some (r, d) => Some (XP r d) | None => None end
  | Evar id ty => load_lv Σ (lv_var ve gv id ty) ty
  | Ederef b ty => load_lv Σ (lv_deref (xexpr Σ b)) ty
  | Efield b f ty => load_lv Σ (lv_field ce (xexpr Σ b) (typeof b) f) ty
  | Eunop op b _ => match xexpr Σ b with Some xb => xun op xb (typeof b) | None => None end
  | Ebinop op b c _ =>
      match xexpr Σ b, xexpr Σ c with
      | Some xb, Some xc => xbinop ce op xb (typeof b) xc (typeof c)
      | _, _ => None
      end
  | Ecast b ty => match xexpr Σ b with Some xb => xcast xb (typeof b) ty | None => None end
  | _ => None
  end.

Definition xlval (Σ : sstate) (a : expr) : option (nat * Z) := xlv_of (xexpr Σ) a.

Fixpoint xargs (Σ : sstate) (al : list expr) (tys : typelist) : option (list sx) :=
  match al, tys with
  | [], Tnil => Some []
  | a :: al, Tcons ty tys =>
      match xexpr Σ a with
      | Some x =>
          match xcast x (typeof a) ty, xargs Σ al tys with
          | Some x', Some xs => Some (x' :: xs)
          | _, _ => None
          end
      | None => None
      end
  | _, _ => None
  end.
End XEXPR.

Definition tmatch (β : layout) (ts : PTree.t sx) (le : temp_env) : Prop :=
  forall id x, ts!id = Some x -> le!id = Some (den (lay β) x).
Definition ematch (β : layout) (ve : venv) (e : env) : Prop :=
  forall id, e!id = match vlookup ve id with Some (r, ty) => Some (blk β r, ty) | None => None end /\
             (forall r ty, vlookup ve id = Some (r, ty) -> bas β r = 0).
Definition gmatch (ge : genv) (β : layout) (gv : venv) : Prop :=
  forall id r ty, vlookup gv id = Some (r, ty) ->
    Genv.find_symbol ge id = Some (blk β r) /\ bas β r = 0.

Lemma ptr_add_repr B d sz k :
  Ptrofs.add (Ptrofs.repr (B + d)) (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.repr k)) =
  Ptrofs.repr (B + (d + sz * k)).
Proof.
  unfold Ptrofs.add, Ptrofs.mul. apply Ptrofs.eqm_samerepr.
  replace (B + (d + sz * k)) with ((B + d) + sz * k) by lia.
  apply Ptrofs.eqm_add.
  - apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
  - eapply Ptrofs.eqm_trans; [apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr|].
    apply Ptrofs.eqm_mult; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

Lemma ptr_add_repr1 B d k :
  Ptrofs.add (Ptrofs.repr (B + d)) (Ptrofs.repr k) = Ptrofs.repr (B + (d + k)).
Proof.
  unfold Ptrofs.add. apply Ptrofs.eqm_samerepr.
  replace (B + (d + k)) with ((B + d) + k) by lia.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

Section SOUND.
Variable ge : genv.
Variables ve gv : venv.
Variable β : layout.
Variable Σ : sstate.
Variable m : mem.
Variable e : env.
Variable le : temp_env.
Hypothesis Hrep : rep β (sregs Σ) m.
Hypothesis Htm : tmatch β (stemps Σ) le.
Hypothesis Hem : ematch β ve e.
Hypothesis Hgm : gmatch ge β gv.

Notation ce := (genv_cenv ge).

Lemma xptradd_sound xa ta xb tb x :
  xptradd ce xa ta xb tb = Some x ->
  sem_binary_operation ce Oadd (den (lay β) xa) ta (den (lay β) xb) tb m = Some (den (lay β) x).
Proof.
  unfold xptradd. intros H. destruct xa; try discriminate.
  destruct ta as [| sza sga aa | sga aa | fa aa | ta' aa | ta' na aa | targsa tresa cca | ida aa | ida aa];
    try discriminate;
  destruct xb; try discriminate;
  destruct tb as [| szb sgb ab | sgb ab | fb ab | tb' ab | tb' nb ab | targsb tresb ccb | idb ab | idb ab];
    try discriminate; inversion H; subst x; clear H; simpl; unfold sem_add.
  - destruct szb, sgb; simpl; unfold sem_add_ptr_int; simpl;
      unfold Ptrofs.of_ints, Ptrofs.of_intu, Ptrofs.of_int; rewrite ptr_add_repr; reflexivity.
  - simpl. unfold sem_add_ptr_long; simpl. unfold Ptrofs.of_int64. rewrite ptr_add_repr; reflexivity.
  - destruct szb, sgb; simpl; unfold sem_add_ptr_int; simpl;
      unfold Ptrofs.of_ints, Ptrofs.of_intu, Ptrofs.of_int; rewrite ptr_add_repr; reflexivity.
  - simpl. unfold sem_add_ptr_long; simpl. unfold Ptrofs.of_int64. rewrite ptr_add_repr; reflexivity.
Qed.

Lemma xbinop_sound op xa ta xb tb x :
  xbinop ce op xa ta xb tb = Some x ->
  sem_binary_operation ce op (den (lay β) xa) ta (den (lay β) xb) tb m = Some (den (lay β) x).
Proof.
  unfold xbinop. intros H.
  destruct op; try (apply xbin_sound; exact H).
  destruct xa; try (apply xbin_sound; exact H).
  apply xptradd_sound. exact H.
Qed.

Lemma load_lv_sound a r d x :
  eval_lvalue ge e le m a (blk β r) (Ptrofs.repr (bas β r + d)) Full ->
  xload (sregs Σ) r d (typeof a) = Some x ->
  eval_expr ge e le m a (den (lay β) x).
Proof.
  intros Hlv Hx. unfold xload in Hx.
  destruct (access_mode (typeof a)) as [ch| | |] eqn:AM; try discriminate.
  - destruct (nth_error (sregs Σ) r) as [reg|] eqn:E; [|discriminate].
    destruct (find_cell (rcells reg) d ch) as [c|] eqn:F; [|discriminate].
    destruct (xload_sound β _ m r d ch c reg x Hrep E F Hx) as [Hl Hr].
    eapply eval_Elvalue; [exact Hlv|].
    eapply deref_loc_value; [exact AM|].
    simpl. rewrite Ptrofs.unsigned_repr by exact Hr. exact Hl.
  - inversion Hx; subst x. eapply eval_Elvalue; [exact Hlv|].
    apply deref_loc_reference. exact AM.
  - inversion Hx; subst x. eapply eval_Elvalue; [exact Hlv|].
    apply deref_loc_copy. exact AM.
Qed.

Lemma lv_var_sound id ty r d :
  lv_var ve gv id ty = Some (r, d) ->
  eval_lvalue ge e le m (Evar id ty) (blk β r) (Ptrofs.repr (bas β r + d)) Full.
Proof.
  unfold lv_var. intros H. destruct (Hem id) as [He Hb].
  destruct (vlookup ve id) as [[r' ty']|] eqn:V.
  - destruct (type_eq ty ty') as [<-|]; [|discriminate]. inversion H; subst r' d.
    rewrite (Hb r ty eq_refl). apply eval_Evar_local. exact He.
  - destruct (vlookup gv id) as [[r' ty']|] eqn:G; [|discriminate]. inversion H; subst r' d.
    destruct (Hgm id r ty' G) as [Hs Hz]. rewrite Hz. apply eval_Evar_global; assumption.
Qed.

Lemma xexpr_sound_both a :
  (forall x, xexpr ce ve gv Σ a = Some x -> eval_expr ge e le m a (den (lay β) x)) /\
  (forall r d, xlval ce ve gv Σ a = Some (r, d) ->
     eval_lvalue ge e le m a (blk β r) (Ptrofs.repr (bas β r + d)) Full).
Proof.
  induction a; (split; [intros x Hx|intros r d Hl]); simpl in *; try discriminate.
  - inversion Hx; subst. apply eval_Econst_int.
  - inversion Hx; subst. apply eval_Econst_long.
  - (* Evar rvalue *)
    unfold load_lv in Hx. destruct (lv_var ve gv i t) as [[r d]|] eqn:L; [|discriminate].
    eapply load_lv_sound; [apply lv_var_sound; exact L|exact Hx].
  - apply lv_var_sound. exact Hl.
  - apply eval_Etempvar. apply Htm. exact Hx.
  - (* Ederef rvalue *)
    unfold load_lv in Hx. destruct (lv_deref (xexpr ce ve gv Σ a)) as [[r d]|] eqn:L; [|discriminate].
    unfold lv_deref in L. destruct (xexpr ce ve gv Σ a) as [xa|] eqn:Ea; [|discriminate].
    destruct xa; try discriminate. inversion L; subst.
    eapply load_lv_sound; [|exact Hx]. apply eval_Ederef. exact (proj1 IHa _ eq_refl).
  - unfold xlval, xlv_of in Hl. unfold lv_deref in Hl.
    destruct (xexpr ce ve gv Σ a) as [xa|] eqn:Ea; [|discriminate].
    destruct xa; try discriminate. inversion Hl; subst.
    apply eval_Ederef. exact (proj1 IHa _ eq_refl).
  - (* Eaddrof *)
    destruct (xlv_of ce ve gv (xexpr ce ve gv Σ) a) as [[r d]|] eqn:L; [|discriminate].
    inversion Hx; subst. apply eval_Eaddrof. exact (proj2 IHa r d L).
  - (* Eunop *)
    destruct (xexpr ce ve gv Σ a) as [xa|] eqn:Ea; [|discriminate].
    eapply eval_Eunop; [exact (proj1 IHa _ eq_refl)|]. apply xun_sound. exact Hx.
  - (* Ebinop *)
    destruct (xexpr ce ve gv Σ a1) as [xa|] eqn:Ea; [|discriminate].
    destruct (xexpr ce ve gv Σ a2) as [xb|] eqn:Eb; [|discriminate].
    eapply eval_Ebinop; [exact (proj1 IHa1 _ eq_refl)|exact (proj1 IHa2 _ eq_refl)|].
    apply xbinop_sound. exact Hx.
  - (* Ecast *)
    destruct (xexpr ce ve gv Σ a) as [xa|] eqn:Ea; [|discriminate].
    eapply eval_Ecast; [exact (proj1 IHa _ eq_refl)|]. apply xcast_sound. exact Hx.
  - (* Efield rvalue *)
    unfold load_lv in Hx.
    destruct (lv_field ce (xexpr ce ve gv Σ a) (typeof a) i) as [[r d]|] eqn:L; [|discriminate].
    eapply load_lv_sound; [|exact Hx].
    unfold lv_field in L. destruct (xexpr ce ve gv Σ a) as [xa|] eqn:Ea; [|discriminate].
    destruct xa; try discriminate. destruct (typeof a) eqn:Ta; try discriminate.
    destruct (ce!i0) as [co|] eqn:Co; [|discriminate].
    destruct (field_offset ce i (co_members co)) as [[delta bf]|] eqn:FO; [|discriminate].
    destruct bf; try discriminate. inversion L; subst.
    rewrite <- ptr_add_repr1.
    eapply eval_Efield_struct; [exact (proj1 IHa _ eq_refl)|exact Ta|exact Co|exact FO].
  - unfold xlval, xlv_of, lv_field in Hl.
    destruct (xexpr ce ve gv Σ a) as [xa|] eqn:Ea; [|discriminate].
    destruct xa; try discriminate. destruct (typeof a) eqn:Ta; try discriminate.
    destruct (ce!i0) as [co|] eqn:Co; [|discriminate].
    destruct (field_offset ce i (co_members co)) as [[delta bf]|] eqn:FO; [|discriminate].
    destruct bf; try discriminate. inversion Hl; subst.
    rewrite <- ptr_add_repr1.
    eapply eval_Efield_struct; [exact (proj1 IHa _ eq_refl)|exact Ta|exact Co|exact FO].
Qed.

Lemma xexpr_sound a x :
  xexpr ce ve gv Σ a = Some x -> eval_expr ge e le m a (den (lay β) x).
Proof. exact (proj1 (xexpr_sound_both a) x). Qed.
Lemma xlval_sound a r d :
  xlval ce ve gv Σ a = Some (r, d) ->
  eval_lvalue ge e le m a (blk β r) (Ptrofs.repr (bas β r + d)) Full.
Proof. exact (proj2 (xexpr_sound_both a) r d). Qed.

Lemma xargs_sound al tys xs :
  xargs ce ve gv Σ al tys = Some xs ->
  eval_exprlist ge e le m al tys (map (den (lay β)) xs).
Proof.
  revert tys xs. induction al as [|a al IH]; intros tys xs H; destruct tys; simpl in H; try discriminate.
  - inversion H; subst. constructor.
  - destruct (xexpr ce ve gv Σ a) as [x|] eqn:Ea; [|discriminate].
    destruct (xcast x (typeof a) t) as [x'|] eqn:Ec; [|discriminate].
    destruct (xargs ce ve gv Σ al tys) as [xs'|] eqn:Er; [|discriminate].
    inversion H; subst. simpl.
    eapply eval_Econs; [apply xexpr_sound; exact Ea|apply xcast_sound; exact Ec|apply IH; exact Er].
Qed.
End SOUND.
