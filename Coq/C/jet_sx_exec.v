(** A verified symbolic executor for Clight statements and calls.

    [xstmt] computes, for a symbolic state, a decision tree of final symbolic
    states.  Calls to internal functions are executed symbolically; calls to
    "oracle" functions, whose behaviour has been established separately,
    update the symbolic state by a given transformer, define fresh symbolic
    variables and are recorded in an event log.  [xstmt_sound] turns a
    successful run into a Clight big-step execution whose final memory
    satisfies the selected final state, for every valuation of the variables
    that satisfies the defining equations of the logged events. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Inductive xout := ONormal | OBreak | OContinue | OReturn (v : option (sx * type)).
Inductive res := RDone (Σ : sstate) (o : xout) | RIf (c : sx) (a b : res).

Fixpoint rsel (ρ : nat -> int64) (β : nat -> block * Z) (r : res) : sstate * xout :=
  match r with
  | RDone Σ o => (Σ, o)
  | RIf c a b => if truth ρ β c then rsel ρ β a else rsel ρ β b
  end.

Lemma rsel_indep ρ β β' r : rsel ρ β r = rsel ρ β' r.
Proof.
  induction r; simpl; [reflexivity|]. rewrite (truth_indep ρ β β'), IHr1, IHr2. reflexivity.
Qed.

Fixpoint tbind (r : res) (k : sstate -> xout -> option res) : option res :=
  match r with
  | RDone Σ o => k Σ o
  | RIf c a b =>
      match tbind a k, tbind b k with
      | Some a', Some b' => Some (RIf c a' b')
      | _, _ => None
      end
  end.

Lemma tbind_sel ρ β r k r' :
  tbind r k = Some r' ->
  exists rk, k (fst (rsel ρ β r)) (snd (rsel ρ β r)) = Some rk /\ rsel ρ β r' = rsel ρ β rk.
Proof.
  revert r'. induction r as [Σ o|c a IHa b IHb]; simpl; intros r' H.
  - exists r'. split; [exact H|reflexivity].
  - destruct (tbind a k) as [a'|] eqn:Ea; [|discriminate].
    destruct (tbind b k) as [b'|] eqn:Eb; [|discriminate].
    inversion H; subst r'. simpl. destruct (truth ρ β c); [apply IHa|apply IHb]; reflexivity.
Qed.

Definition is_const (c : sx) : option int := match c with XIc i => Some i | _ => None end.
Lemma is_const_eq c i : is_const c = Some i -> c = XIc i.
Proof. destruct c; simpl; congruence. Qed.

Definition set_opt (optid : option ident) (v : option sx) (ts : PTree.t sx) : PTree.t sx :=
  match optid, v with
  | None, _ => ts
  | Some id, Some x => PTree.set id x ts
  | Some id, None => PTree.remove id ts
  end.

Definition xret (ty : type) (o : xout) : option (option sx) :=
  match o with
  | ONormal | OReturn None => match ty with Tvoid => Some None | _ => None end
  | OReturn (Some (x, tx)) =>
      match ty with
      | Tvoid => None
      | _ => match xcast x tx ty with Some v => Some (Some v) | None => None end
      end
  | _ => None
  end.

(** An oracle maps the first fresh variable, the log so far, the arguments and the regions
    to the new regions, the result, and the tag, number of defined variables
    and arguments of the event to log. *)
Definition oracle : Type :=
  nat -> list event -> list sx -> list region -> option (list region * option sx * nat * nat * list sx).
Inductive fentry := FInt (fd : function) | FOra (fd : function) (o : oracle).
Definition fentry_fd (ent : fentry) : function :=
  match ent with FInt fd => fd | FOra fd _ => fd end.

Fixpoint flookup (fns : list (ident * fentry)) (id : ident) : option fentry :=
  match fns with
  | [] => None
  | (i, f) :: t => if Pos.eqb i id then Some f else flookup t id
  end.

Definition fn_okb (fd : function) : bool :=
  (if list_norepet_dec ident_eq (var_names (fn_vars fd)) then true else false) &&
  (if list_norepet_dec ident_eq (var_names (fn_params fd)) then true else false) &&
  (if list_disjoint_dec ident_eq (var_names (fn_params fd)) (var_names (fn_temps fd)) then true else false).

Lemma fn_okb_true fd :
  fn_okb fd = true ->
  list_norepet (var_names (fn_vars fd)) /\ list_norepet (var_names (fn_params fd)) /\
  list_disjoint (var_names (fn_params fd)) (var_names (fn_temps fd)).
Proof.
  unfold fn_okb. intros H. apply andb_true_iff in H. destruct H as [H H3].
  apply andb_true_iff in H. destruct H as [H1 H2].
  destruct (list_norepet_dec ident_eq (var_names (fn_vars fd))); [|discriminate].
  destruct (list_norepet_dec ident_eq (var_names (fn_params fd))); [|discriminate].
  destruct (list_disjoint_dec ident_eq (var_names (fn_params fd)) (var_names (fn_temps fd))); [|discriminate].
  auto.
Qed.

Section EXEC.
Variable ce : composite_env.
Variable gv : venv.
Variable fns : list (ident * fentry).

Definition xcall_ret (optid : option ident) (ts : PTree.t sx) (nreg : nat) (ty : type)
    (Σb : sstate) (ob : xout) : option res :=
  match xret ty ob with
  | Some v =>
      if match v with Some x => xp_lt nreg x | None => true end
      then Some (RDone (mkst (set_opt optid v ts) (firstn nreg (sregs Σb)) (slog Σb) (snv Σb)) ONormal)
      else None
  | None => None
  end.

(** Entry into, execution of, and return from an internal function, given
    an executor [rec] for its body. *)
Definition xfun_with (rec : venv -> sstate -> statement -> option res)
    (fd : function) (xs : list sx) (regs : list region) (log : list event) (nv : nat)
    (k : sstate -> xout -> option res) : option res :=
  if fn_okb fd then
    if forallb (xp_lt (length regs)) xs then
      match xalloc (std_cells ce) ce (fn_vars fd) (length regs), xbind (fn_params fd) xs (PTree.empty sx) with
      | Some (regsN, veN), Some ts0 =>
          match rec veN (mkst ts0 (regs ++ regsN) log nv) (fn_body fd) with
          | Some rb => tbind rb k
          | None => None
          end
      | _, _ => None
      end
    else None
  else None.

Fixpoint xstmt (n : nat) (ve : venv) (Σ : sstate) (s : statement) {struct n} : option res :=
  match n with
  | O => None
  | S n =>
    match s with
    | Sskip => Some (RDone Σ ONormal)
    | Sset id a =>
        match xexpr ce ve gv Σ a with
        | Some x => Some (RDone (mkst (PTree.set id x (stemps Σ)) (sregs Σ) (slog Σ) (snv Σ)) ONormal)
        | None => None
        end
    | Sassign a1 a2 =>
        match xlval ce ve gv Σ a1, xexpr ce ve gv Σ a2, access_mode (typeof a1) with
        | Some (r, d), Some x2, By_value ch =>
            match xcast x2 (typeof a2) (typeof a1) with
            | Some x =>
                match xstore (sregs Σ) r d ch x with
                | Some regs' => Some (RDone (mkst (stemps Σ) regs' (slog Σ) (snv Σ)) ONormal)
                | None => None
                end
            | None => None
            end
        | _, _, _ => None
        end
    | Ssequence s1 s2 =>
        match xstmt n ve Σ s1 with
        | Some r1 =>
            tbind r1 (fun Σ1 o => match o with
                                  | ONormal => xstmt n ve Σ1 s2
                                  | _ => Some (RDone Σ1 o)
                                  end)
        | None => None
        end
    | Sifthenelse a s1 s2 =>
        match xexpr ce ve gv Σ a with
        | Some xa =>
            match xbool xa (typeof a) with
            | Some c =>
                match is_const c with
                | Some i => xstmt n ve Σ (if negb (Int.eq i Int.zero) then s1 else s2)
                | None =>
                    match xstmt n ve Σ s1, xstmt n ve Σ s2 with
                    | Some r1, Some r2 => Some (RIf c r1 r2)
                    | _, _ => None
                    end
                end
            | None => None
            end
        | None => None
        end
    | Sreturn None => Some (RDone Σ (OReturn None))
    | Sreturn (Some a) =>
        match xexpr ce ve gv Σ a with
        | Some x => Some (RDone Σ (OReturn (Some (x, typeof a))))
        | None => None
        end
    | Sbreak => Some (RDone Σ OBreak)
    | Scontinue => Some (RDone Σ OContinue)
    | Sloop s1 s2 =>
        match xstmt n ve Σ s1 with
        | Some r1 =>
            tbind r1 (fun Σ1 o1 =>
              match o1 with
              | OBreak => Some (RDone Σ1 ONormal)
              | OReturn v => Some (RDone Σ1 (OReturn v))
              | ONormal | OContinue =>
                  match xstmt n ve Σ1 s2 with
                  | Some r2 =>
                      tbind r2 (fun Σ2 o2 =>
                        match o2 with
                        | OBreak => Some (RDone Σ2 ONormal)
                        | OReturn v => Some (RDone Σ2 (OReturn v))
                        | ONormal => xstmt n ve Σ2 (Sloop s1 s2)
                        | OContinue => None
                        end)
                  | None => None
                  end
              end)
        | None => None
        end
    | Scall optid (Evar fid fty) al =>
        match vlookup ve fid, flookup fns fid, fty with
        | None, Some ent, Tfunction tyargs tyres cc =>
            if type_eq (type_of_function (fentry_fd ent)) fty then
              match xargs ce ve gv Σ al tyargs with
              | Some xs =>
                  match ent with
                  | FInt fd =>
                      xfun_with (xstmt n) fd xs (sregs Σ) (slog Σ) (snv Σ)
                        (xcall_ret optid (stemps Σ) (length (sregs Σ)) (fn_return fd))
                  | FOra fd o =>
                      match o (snv Σ) (slog Σ) xs (sregs Σ) with
                      | Some (regs', v, tag, cnt, eargs) =>
                          Some (RDone (mkst (set_opt optid v (stemps Σ)) regs'
                                         (slog Σ ++ [mkev tag (snv Σ) cnt eargs]) (snv Σ + cnt)) ONormal)
                      | None => None
                      end
                  end
              | None => None
              end
            else None
        | _, _, _ => None
        end
    | _ => None
    end
  end.

(** A whole function call from the outside; the result is bound to
    temporary [1] of an otherwise empty temporary environment. *)
Definition xfun (n : nat) (fd : function) (xs : list sx) (regs : list region)
    (log : list event) (nv : nat) : option res :=
  xfun_with (xstmt n) fd xs regs log nv
    (xcall_ret (Some 1%positive) (PTree.empty sx) (length regs) (fn_return fd)).

(** The log only grows. *)
Definition lext (ρ : nat -> int64) (β : nat -> block * Z) (log : list event) (r : res) : Prop :=
  exists suf, slog (fst (rsel ρ β r)) = log ++ suf.

Lemma lext_refl ρ β Σ o : lext ρ β (slog Σ) (RDone Σ o).
Proof. exists []. simpl. rewrite app_nil_r. reflexivity. Qed.

Lemma lext_sel ρ β log r r' : rsel ρ β r = rsel ρ β r' -> lext ρ β log r' -> lext ρ β log r.
Proof. unfold lext. intros ->. auto. Qed.

Lemma lext_trans ρ β log r1 r2 :
  lext ρ β log r1 -> lext ρ β (slog (fst (rsel ρ β r1))) r2 -> lext ρ β log r2.
Proof.
  intros [s1 H1] [s2 H2]. exists (s1 ++ s2). rewrite H2, H1, app_assoc. reflexivity.
Qed.

Lemma xfun_lext (rec : venv -> sstate -> statement -> option res)
  (IH : forall ve Σ s r, rec ve Σ s = Some r -> forall ρ β, lext ρ β (slog Σ) r)
  fd xs regs log nv ts optid nreg ty rr :
  xfun_with rec fd xs regs log nv (xcall_ret optid ts nreg ty) = Some rr ->
  forall ρ β, lext ρ β log rr.
Proof.
  unfold xfun_with. intros H ρ β.
  destruct (fn_okb fd); [|discriminate].
  destruct (forallb (xp_lt (length regs)) xs); [|discriminate].
  destruct (xalloc (std_cells ce) ce (fn_vars fd) (length regs)) as [[regsN veN]|]; [|discriminate].
  destruct (xbind (fn_params fd) xs (PTree.empty sx)) as [ts0|]; [|discriminate].
  destruct (rec veN (mkst ts0 (regs ++ regsN) log nv) (fn_body fd)) as [rb|] eqn:Eb; [|discriminate].
  pose proof (IH _ _ _ _ Eb ρ β) as [suf Hs]. simpl in Hs.
  destruct (tbind_sel ρ β _ _ _ H) as (rk & Hk & Hsel).
  unfold xcall_ret in Hk.
  destruct (xret ty (snd (rsel ρ β rb))) as [v|]; [|discriminate].
  destruct (match v with Some x => xp_lt nreg x | None => true end); [|discriminate].
  inversion Hk; subst rk. exists suf. rewrite Hsel. simpl. exact Hs.
Qed.

Lemma xstmt_lext n : forall ve Σ s r,
  xstmt n ve Σ s = Some r -> forall ρ β, lext ρ β (slog Σ) r.
Proof.
  induction n as [|n IH]; intros ve Σ s rr H ρ β; [discriminate|].
  destruct s; cbn [xstmt] in H; try discriminate.
  - inversion H; subst rr. apply lext_refl.
  - destruct (xlval ce ve gv Σ e) as [[r0 d]|]; [|discriminate].
    destruct (xexpr ce ve gv Σ e0) as [x2|]; [|discriminate].
    destruct (access_mode (typeof e)) as [ch| | |]; try discriminate.
    destruct (xcast x2 (typeof e0) (typeof e)) as [x|]; [|discriminate].
    destruct (xstore (sregs Σ) r0 d ch x) as [regs'|]; [|discriminate].
    inversion H; subst rr. exists []. simpl. rewrite app_nil_r. reflexivity.
  - destruct (xexpr ce ve gv Σ e) as [x|]; [|discriminate].
    inversion H; subst rr. exists []. simpl. rewrite app_nil_r. reflexivity.
  - destruct e; try discriminate.
    destruct (vlookup ve i); [discriminate|].
    destruct (flookup fns i) as [ent|]; [|discriminate].
    destruct t; try discriminate.
    destruct (type_eq (type_of_function (fentry_fd ent)) (Tfunction t t0 c)); [|discriminate].
    destruct (xargs ce ve gv Σ l t) as [xs|]; [|discriminate].
    destruct ent as [fd|fd orc].
    + eapply xfun_lext; [exact IH|exact H].
    + destruct (orc (snv Σ) (slog Σ) xs (sregs Σ)) as [[[[[regs' v] tag] cnt] eargs]|]; [|discriminate].
      inversion H; subst rr. eexists. simpl. reflexivity.
  - destruct (xstmt n ve Σ s1) as [r1|] eqn:E1; [|discriminate].
    destruct (tbind_sel ρ β _ _ _ H) as (rk & Hk & Hsel).
    pose proof (IH _ _ _ _ E1 ρ β) as H1.
    eapply lext_sel; [exact Hsel|].
    destruct (rsel ρ β r1) as [Σ1 o1] eqn:Es. simpl in Hk.
    assert (H1' : lext ρ β (slog Σ) (RDone Σ1 o1)) by (unfold lext in *; simpl; rewrite Es in H1; exact H1).
    destruct o1; try (inversion Hk; subst rk; exact H1').
    eapply lext_trans; [exact H1|]. rewrite Es. simpl. exact (IH _ _ _ _ Hk ρ β).
  - destruct (xexpr ce ve gv Σ e) as [xa|]; [|discriminate].
    destruct (xbool xa (typeof e)) as [c|]; [|discriminate].
    destruct (is_const c) as [i|].
    + exact (IH _ _ _ _ H ρ β).
    + destruct (xstmt n ve Σ s1) as [r1|] eqn:E1; [|discriminate].
      destruct (xstmt n ve Σ s2) as [r2|] eqn:E2; [|discriminate].
      inversion H; subst rr. unfold lext. simpl.
      destruct (truth ρ β c); [exact (IH _ _ _ _ E1 ρ β)|exact (IH _ _ _ _ E2 ρ β)].
  - destruct (xstmt n ve Σ s1) as [r1|] eqn:E1; [|discriminate].
    destruct (tbind_sel ρ β _ _ _ H) as (rk & Hk & Hsel).
    pose proof (IH _ _ _ _ E1 ρ β) as H1.
    eapply lext_sel; [exact Hsel|].
    destruct (rsel ρ β r1) as [Σ1 o1] eqn:Es. simpl in Hk.
    assert (H1' : forall o, lext ρ β (slog Σ) (RDone Σ1 o)) by (intros o; unfold lext in *; simpl; rewrite Es in H1; exact H1).
    assert (Hcont : match xstmt n ve Σ1 s2 with
              | Some r2 =>
                  tbind r2 (fun Σ2 o2 =>
                    match o2 with
                    | OBreak => Some (RDone Σ2 ONormal)
                    | OReturn v => Some (RDone Σ2 (OReturn v))
                    | ONormal => xstmt n ve Σ2 (Sloop s1 s2)
                    | OContinue => None
                    end)
              | None => None
              end = Some rk -> lext ρ β (slog Σ) rk).
    { intros Hk2. destruct (xstmt n ve Σ1 s2) as [r2|] eqn:E2; [|discriminate].
      destruct (tbind_sel ρ β _ _ _ Hk2) as (rk2 & Hk3 & Hsel2).
      pose proof (IH _ _ _ _ E2 ρ β) as H2.
      eapply lext_sel; [exact Hsel2|].
      assert (H12 : lext ρ β (slog Σ) r2).
      { eapply lext_trans; [exact H1|]. rewrite Es. exact H2. }
      destruct (rsel ρ β r2) as [Σ2 o2] eqn:Es2. simpl in Hk3.
      assert (H2' : forall o, lext ρ β (slog Σ) (RDone Σ2 o)) by (intros o; unfold lext in *; simpl; rewrite Es2 in H12; exact H12).
      destruct o2; try discriminate; try (inversion Hk3; subst rk2; apply H2').
      eapply lext_trans; [exact H12|]. rewrite Es2. simpl. exact (IH _ _ _ _ Hk3 ρ β). }
    destruct o1; try (apply Hcont; exact Hk); inversion Hk; subst rk; apply H1'.
  - inversion H; subst rr. apply lext_refl.
  - inversion H; subst rr. apply lext_refl.
  - destruct o as [a|].
    + destruct (xexpr ce ve gv Σ a) as [x|]; [|discriminate]. inversion H; subst rr. apply lext_refl.
    + inversion H; subst rr. apply lext_refl.
Qed.
End EXEC.

(** ** Soundness *)
Definition outmatch ρ (β : layout) (o : xout) (out : outcome) : Prop :=
  match o, out with
  | ONormal, Out_normal | OBreak, Out_break | OContinue, Out_continue => True
  | OReturn None, Out_return None => True
  | OReturn (Some (x, ty)), Out_return (Some (v, ty')) => v = den ρ (lay β) x /\ ty' = ty
  | _, _ => False
  end.

Definition gmatch2 (ge : genv) (β : layout) (gv : venv) : Prop :=
  gmatch ge β gv /\ forall id r ty, vlookup gv id = Some (r, ty) -> (r < length β)%nat.

Lemma shape_nth regs regs' r reg :
  map rshape regs' = map rshape regs -> nth_error regs r = Some reg ->
  exists reg', nth_error regs' r = Some reg' /\ rshape reg' = rshape reg.
Proof.
  intros H E. assert (H1 : nth_error (map rshape regs') r = nth_error (map rshape regs) r) by congruence.
  rewrite !nth_error_map, E in H1. destruct (nth_error regs' r) as [reg'|]; [|discriminate].
  simpl in H1. exists reg'. split; [reflexivity|congruence].
Qed.

Lemma callee_env_blocks ge β' veN e' :
  list_norepet (map fst β') ->
  (forall id, e'!id = match vlookup veN id with
                      | Some (r, ty) => Some (blk β' r, ty) | None => None end) ->
  (forall id r ty, vlookup veN id = Some (r, ty) -> (r < length β')%nat) ->
  (forall id1 id2 r ty1 ty2, vlookup veN id1 = Some (r, ty1) -> vlookup veN id2 = Some (r, ty2) -> id1 = id2) ->
  (forall b lo hi, In (b, lo, hi) (blocks_of_env ge e') ->
     exists id r ty, vlookup veN id = Some (r, ty) /\ b = blk β' r /\ lo = 0 /\ hi = sizeof ge ty) /\
  list_norepet (map (fun x => fst (fst x)) (blocks_of_env ge e')).
Proof.
  intros Hnr He Hlt Hinj.
  assert (Hel : forall id b ty, In (id, (b, ty)) (PTree.elements e') ->
            exists r, vlookup veN id = Some (r, ty) /\ b = blk β' r).
  { intros id b ty Hin. apply PTree.elements_complete in Hin. rewrite He in Hin.
    destruct (vlookup veN id) as [[r ty']|]; [|discriminate]. inversion Hin; subst. eauto. }
  split.
  - intros b lo hi Hin. unfold blocks_of_env in Hin. apply in_map_iff in Hin.
    destruct Hin as ([id [b' ty]] & Heq & Hin). simpl in Heq. inversion Heq; subst.
    destruct (Hel id b ty Hin) as (r & V & Eb). exists id, r, ty. auto.
  - unfold blocks_of_env. rewrite map_map.
    apply norepet_map_keys with (f := fst); [apply PTree.elements_keys_norepet|].
    intros [id1 [b1 ty1]] [id2 [b2 ty2]] H1 H2 Eb. simpl in *.
    destruct (Hel id1 b1 ty1 H1) as (r1 & V1 & E1). destruct (Hel id2 b2 ty2 H2) as (r2 & V2 & E2).
    assert (r1 = r2) by (eapply blk_inj; eauto; congruence). subst r2.
    exact (Hinj id1 id2 r1 ty1 ty2 V1 V2).
Qed.

Lemma xret_sound ρ β ty ob out m v :
  xret ty ob = Some v -> outmatch ρ β ob out ->
  exists vres, outcome_result_value out ty vres m /\
    match v with Some x => vres = den ρ (lay β) x | None => vres = Vundef end.
Proof.
  unfold xret. intros H Hom.
  destruct ob as [| | |[[x tx]|]]; try discriminate;
    destruct out as [| | |[[v' ty']|]]; simpl in Hom; try contradiction.
  - destruct ty; try discriminate. inversion H; subst. exists Vundef. split; reflexivity.
  - destruct Hom as [-> ->].
    destruct (xcast x tx ty) as [v0|] eqn:Ec; [|destruct ty; discriminate].
    assert (ty <> Tvoid) by (destruct ty; discriminate || congruence).
    assert (v = Some v0) by (destruct ty; congruence). subst v.
    exists (den ρ (lay β) v0). split; [|reflexivity].
    simpl. split; [exact H0|]. apply xcast_sound. exact Ec.
  - destruct ty; try discriminate. inversion H; subst. exists Vundef. split; reflexivity.
Qed.

Lemma map_den_ext ρ (β β' : nat -> block * Z) n xs :
  (forall r, (r < n)%nat -> β' r = β r) -> forallb (xp_lt n) xs = true ->
  map (den ρ β') xs = map (den ρ β) xs.
Proof.
  intros H. induction xs as [|x xs IH]; simpl; intros F; [reflexivity|].
  apply andb_true_iff in F. destruct F as [F1 F2].
  rewrite (den_ext ρ x β β' n H F1), (IH F2). reflexivity.
Qed.

(** The 64-bit value of a symbolic expression. *)
Definition lv (ρ : nat -> int64) (x : sx) : int64 := il (den ρ (fun _ => (1%positive, 0)) x).

Lemma lv_den ρ β x : il (den ρ β x) = lv ρ x.
Proof. unfold lv. exact (proj2 (den_proj_indep ρ x β _)). Qed.

Section SOUND.
Variable ge : genv.
Variable gv : venv.
Variable fns : list (ident * fentry).
(** Meaning of the events (typically the defining equations of their
    variables), and the invariant maintained on the memory outside the
    regions, in the blocks satisfying [ext]. *)
Variable ev_ok : (nat -> int64) -> event -> Prop.
Variable inv : (nat -> int64) -> list event -> mem -> Prop.
Variable ext : block -> Prop.

Definition solves (ρ : nat -> int64) (log : list event) : Prop := Forall (ev_ok ρ) log.

Definition xsep (β : layout) : Prop := forall r, (r < length β)%nat -> ~ ext (blk β r).

Definition frame (β : layout) (regs : list region) (m : mem) : block -> Z -> Prop :=
  fun b o => Mem.valid_block m b /\ ~ foot β (map rshape regs) b o /\ ~ ext b.

Definition oracle_ok (fd : function) (o : oracle) : Prop :=
  forall base xs regs regs' v tag cnt eargs log ρ β m,
    o base log xs regs = Some (regs', v, tag, cnt, eargs) ->
    rep ρ β regs m -> xsep β -> inv ρ log m -> ev_ok ρ (mkev tag base cnt eargs) ->
    exists m' vres,
      ClightBigstep.eval_funcall function_entry2 ge m (Internal fd) (map (den ρ (lay β)) xs) E0 m' vres /\
      rep ρ β regs' m' /\ inv ρ (log ++ [mkev tag base cnt eargs]) m' /\
      map rshape regs' = map rshape regs /\
      match v with Some x => vres = den ρ (lay β) x | None => vres = Vundef end /\
      Mem.unchanged_on (frame β regs m) m m'.

Hypothesis Hinv_stable : forall ρ log m m',
  inv ρ log m -> Mem.unchanged_on (fun b _ => ext b) m m' -> inv ρ log m'.
Hypothesis Hext_valid : forall ρ log m b, inv ρ log m -> ext b -> Mem.valid_block m b.
Hypothesis Hfns : forall id ent, flookup fns id = Some ent ->
  (exists b, Genv.find_symbol ge id = Some b /\
             Genv.find_funct_ptr ge b = Some (Internal (fentry_fd ent))) /\
  match ent with FInt _ => True | FOra fd o => oracle_ok fd o end.

Notation ce := (genv_cenv ge).
Notation exec := (ClightBigstep.exec_stmt function_entry2 ge).

Definition post ρ (β : layout) (Σ0 : sstate) (m0 : mem) (r : res)
    (le' : temp_env) (m' : mem) (out : outcome) : Prop :=
  rep ρ β (sregs (fst (rsel ρ (lay β) r))) m' /\
  tmatch ρ β (stemps (fst (rsel ρ (lay β) r))) le' /\
  outmatch ρ β (snd (rsel ρ (lay β) r)) out /\
  map rshape (sregs (fst (rsel ρ (lay β) r))) = map rshape (sregs Σ0) /\
  inv ρ (slog (fst (rsel ρ (lay β) r))) m' /\
  Mem.unchanged_on (frame β (sregs Σ0) m0) m0 m'.

Lemma post_sel ρ β Σ m r r' le' m' out :
  rsel ρ (lay β) r = rsel ρ (lay β) r' -> post ρ β Σ m r' le' m' out -> post ρ β Σ m r le' m' out.
Proof. unfold post. intros ->. auto. Qed.

Lemma frame_shape β regs regs' m :
  map rshape regs' = map rshape regs -> frame β regs' m = frame β regs m.
Proof. unfold frame. intros ->. reflexivity. Qed.

Lemma post_trans ρ β Σ m r1 le1 m1 out1 r2 le2 m2 out2 :
  post ρ β Σ m r1 le1 m1 out1 -> post ρ β (fst (rsel ρ (lay β) r1)) m1 r2 le2 m2 out2 ->
  post ρ β Σ m r2 le2 m2 out2.
Proof.
  intros (R1 & T1 & O1 & S1 & I1 & U1) (R2 & T2 & O2 & S2 & I2 & U2).
  split; [exact R2|]. split; [exact T2|]. split; [exact O2|]. split; [congruence|]. split; [exact I2|].
  eapply Mem.unchanged_on_trans; [exact U1|].
  eapply Mem.unchanged_on_implies; [exact U2|].
  intros b o (Hv & Hf & He) _. rewrite (frame_shape _ _ _ _ S1). split; [|split; assumption].
  eapply Mem.valid_block_unchanged_on; eauto.
Qed.

Lemma ext_unchanged ρ β regs m m' :
  rep ρ β regs m -> xsep β ->
  Mem.unchanged_on (fun b o => ~ foot β (map rshape regs) b o) m m' ->
  Mem.unchanged_on (fun b _ => ext b) m m'.
Proof.
  intros (Hlen & _ & _) Hsep U. eapply Mem.unchanged_on_implies; [exact U|].
  intros b o He _ (r & s & d & ch & Hs & _ & -> & _).
  apply (Hsep r); [|exact He]. rewrite Hlen. rewrite <- (map_length rshape). apply nth_error_Some. congruence.
Qed.

Lemma solves_app ρ l1 l2 : solves ρ (l1 ++ l2) -> solves ρ l1 /\ solves ρ l2.
Proof. unfold solves. apply Forall_app. Qed.

Definition sound_rec (rec : venv -> sstate -> statement -> option res) : Prop :=
  forall ve Σ s r, rec ve Σ s = Some r ->
  forall ρ β e le m,
    rep ρ β (sregs Σ) m -> tmatch ρ β (stemps Σ) le -> ematch β ve e -> gmatch2 ge β gv ->
    xsep β -> inv ρ (slog Σ) m -> solves ρ (slog (fst (rsel ρ (lay β) r))) ->
    exists le' m' out, exec e le m s E0 le' m' out /\ post ρ β Σ m r le' m' out.

Ltac outinv Hom out :=
  destruct out as [| | |[[? ?]|]]; simpl in Hom; try contradiction.

Lemma xfun_sound (rec : venv -> sstate -> statement -> option res) (IH : sound_rec rec)
  fd xs regs log nv ts optid rr :
  xfun_with ce rec fd xs regs log nv (xcall_ret optid ts (length regs) (fn_return fd)) = Some rr ->
  forall ρ β m, rep ρ β regs m -> gmatch2 ge β gv -> xsep β -> inv ρ log m ->
  solves ρ (slog (fst (rsel ρ (lay β) rr))) ->
  exists m3 vres,
    ClightBigstep.eval_funcall function_entry2 ge m (Internal fd) (map (den ρ (lay β)) xs) E0 m3 vres /\
    rep ρ β (sregs (fst (rsel ρ (lay β) rr))) m3 /\
    (exists v, stemps (fst (rsel ρ (lay β) rr)) = set_opt optid v ts /\
       match v with Some x => vres = den ρ (lay β) x | None => vres = Vundef end) /\
    snd (rsel ρ (lay β) rr) = ONormal /\
    map rshape (sregs (fst (rsel ρ (lay β) rr))) = map rshape regs /\
    inv ρ (slog (fst (rsel ρ (lay β) rr))) m3 /\
    Mem.unchanged_on (frame β regs m) m m3.
Proof.
  unfold xfun_with. intros H ρ β m Hrep Hgm Hsep Hinv Hsol.
  destruct (fn_okb fd) eqn:Fok; [|discriminate].
  destruct (forallb (xp_lt (length regs)) xs) eqn:Fa; [|discriminate].
  destruct (xalloc (std_cells ce) ce (fn_vars fd) (length regs)) as [[regsN veN]|] eqn:Eal; [|discriminate].
  destruct (xbind (fn_params fd) xs (PTree.empty sx)) as [ts0|] eqn:Ebd; [|discriminate].
  destruct (rec veN (mkst ts0 (regs ++ regsN) log nv) (fn_body fd)) as [rb|] eqn:Eb; [|discriminate].
  destruct (fn_okb_true fd Fok) as (Hnr1 & Hnr2 & Hdj).
  assert (Hlen : length β = length regs) by (destruct Hrep as (HH & _); exact HH).
  destruct (xalloc_sound ge ρ (std_cells ce) (fn_vars fd) (length regs) regsN veN β regs m empty_env
              Eal Hrep Hlen Hnr1)
    as (e' & m1 & βN & Hav & Hrep1 & HlenN & He' & Hidx & Hinj & Hnv & Hun1).
  set (β' := β ++ βN) in *.
  assert (Hlay : forall r, (r < length regs)%nat -> lay β' r = lay β r).
  { intros r Hr. apply lay_app_l. lia. }
  assert (Hargs : map (den ρ (lay β')) xs = map (den ρ (lay β)) xs).
  { apply map_den_ext with (n := length regs); [exact Hlay|exact Fa]. }
  destruct (xbind_sound ρ β' (fn_params fd) xs (PTree.empty sx) ts0
              (create_undef_temps (fn_temps fd)) Ebd) as (le1 & Hbind & Htm0).
  { intros id x Hx. rewrite PTree.gempty in Hx. discriminate. }
  rewrite Hargs in Hbind.
  assert (Hem' : ematch β' veN e').
  { intros id. split.
    - rewrite He'. destruct (vlookup veN id) as [[r ty]|]; [reflexivity|apply PTree.gempty].
    - intros r ty V. exact (proj1 (proj2 (proj2 (Hidx id r ty V)))). }
  assert (Hgm' : gmatch2 ge β' gv).
  { destruct Hgm as [Hg1 Hg2]. split.
    - intros id r ty V. destruct (Hg1 id r ty V) as [Hs Hb]. pose proof (Hg2 id r ty V) as Hr.
      unfold blk, bas in *. rewrite Hlay by lia. auto.
    - intros id r ty V. pose proof (Hg2 id r ty V). unfold β'. rewrite app_length. lia. }
  assert (HNinv : forall b, In b (map fst βN) -> ~ Mem.valid_block m b).
  { intros b Hin. apply in_map_iff in Hin. destruct Hin as (p & <- & Hp).
    exact (proj1 (Forall_forall _ _) Hnv p Hp). }
  assert (Hsep' : xsep β').
  { intros r Hr He. destruct (lt_dec r (length regs)) as [Hlt|Hge].
    - apply (Hsep r); [lia|]. unfold blk in *. rewrite Hlay in He by exact Hlt. exact He.
    - apply (HNinv (blk β' r)); [|exact (Hext_valid _ _ _ _ Hinv He)].
      unfold blk, lay, β'. rewrite app_nth2 by lia. apply in_map. apply nth_In.
      unfold β' in Hr. rewrite app_length in Hr. lia. }
  assert (Hinv1 : inv ρ log m1).
  { eapply Hinv_stable; [exact Hinv|]. eapply Mem.unchanged_on_implies; [exact Hun1|]. intros; exact I. }
  destruct (tbind_sel ρ (lay β) _ _ _ H) as (rk & Hk & Hsel).
  assert (Hsolb : solves ρ (slog (fst (rsel ρ (lay β') rb)))).
  { rewrite (rsel_indep ρ (lay β') (lay β)). rewrite Hsel in Hsol. unfold xcall_ret in Hk.
    destruct (xret (fn_return fd) (snd (rsel ρ (lay β) rb))) as [v|]; [|discriminate].
    destruct (match v with Some x => xp_lt (length regs) x | None => true end); [|discriminate].
    inversion Hk; subst rk. exact Hsol. }
  destruct (IH veN _ _ rb Eb ρ β' e' le1 m1 Hrep1 Htm0 Hem' Hgm' Hsep' Hinv1 Hsolb)
    as (le2 & m2 & out2 & Hexb & Hrepb & Htmb & Homb & Hshb & Hinvb & Hunb).
  rewrite (rsel_indep ρ (lay β') (lay β)) in Hrepb, Htmb, Homb, Hshb, Hinvb.
  destruct (rsel ρ (lay β) rb) as [Σb ob]. simpl in Hk, Hrepb, Htmb, Homb, Hshb, Hinvb.
  unfold xcall_ret in Hk.
  destruct (xret (fn_return fd) ob) as [v|] eqn:Er; [|discriminate].
  destruct (match v with Some x => xp_lt (length regs) x | None => true end) eqn:Ev; [|discriminate].
  inversion Hk; subst rk; clear Hk.
  destruct (xret_sound ρ β' _ _ out2 m2 v Er Homb) as (vres & Hres & Hvres).
  assert (Hnrb : list_norepet (map fst β')) by (destruct Hrepb as (_ & HH & _); exact HH).
  assert (Hlenb : length β' = length (regs ++ regsN)).
  { unfold β'. rewrite !app_length. lia. }
  destruct (callee_env_blocks ge β' veN e' Hnrb) as (Hblk & Hbnr).
  { intros id. rewrite He'. destruct (vlookup veN id) as [[r ty]|]; [reflexivity|apply PTree.gempty]. }
  { intros id r ty V. destruct (Hidx id r ty V) as (_ & _ & _ & reg & Hreg & _).
    rewrite Hlenb. apply nth_error_Some. congruence. }
  { exact Hinj. }
  destruct (free_list_exists (blocks_of_env ge e') m2 Hbnr) as (m3 & Hfl & Hun3).
  { intros b lo hi Hin. destruct (Hblk b lo hi Hin) as (id & r & ty & V & -> & -> & ->).
    destruct (Hidx id r ty V) as (_ & _ & _ & reg & Hreg & Hfree).
    destruct (shape_nth _ _ r reg Hshb Hreg) as (regb & Hregb & Hsh).
    destruct Hrepb as (_ & _ & HH). pose proof (HH r regb Hregb) as (_ & _ & _ & _ & Hfr).
    assert (Ef : rfree regb = Some (sizeof ce ty)).
    { unfold rshape in Hsh. inversion Hsh. congruence. }
    rewrite Ef in Hfr. exact (proj1 (proj2 (proj2 Hfr))). }
  assert (HinN : forall b, In b (map (fun x => fst (fst x)) (blocks_of_env ge e')) -> In b (map fst βN)).
  { intros b Hin. apply in_map_iff in Hin. destruct Hin as ([[b' lo] hi] & Eq & Hin). simpl in Eq. subst b'.
    destruct (Hblk b lo hi Hin) as (id & r & ty & V & -> & _).
    destruct (Hidx id r ty V) as (_ & Hge & _ & reg & Hreg & _).
    assert (Hr : (r < length β')%nat) by (rewrite Hlenb; apply nth_error_Some; congruence).
    unfold blk, lay, β'. rewrite app_nth2 by lia. apply in_map. apply nth_In.
    unfold β' in Hr. rewrite app_length in Hr. lia. }
  assert (HβN : forall b, In b (map fst β) -> ~ In b (map fst βN)).
  { intros b H1 H2. unfold β' in Hnrb. rewrite map_app in Hnrb.
    apply list_norepet_app in Hnrb. destruct Hnrb as (_ & _ & Hd). exact (Hd b b H1 H2 eq_refl). }
  assert (Hlenb2 : length (sregs Σb) = length (regs ++ regsN)).
  { rewrite <- (map_length rshape (sregs Σb)), Hshb, map_length. reflexivity. }
  assert (Hrep3 : rep ρ β (firstn (length regs) (sregs Σb)) m3).
  { eapply rep_mem with (m := m2).
    - eapply Mem.unchanged_on_implies; [exact Hun3|]. intros b ofs Hb _ Hin.
      exact (HβN b Hb (HinN b Hin)).
    - eapply rep_prefix with (βN := βN) (regsN := skipn (length regs) (sregs Σb)).
      + rewrite firstn_skipn. exact Hrepb.
      + rewrite firstn_length, Hlenb2, app_length. lia. }
  assert (Hvr : match v with Some x => vres = den ρ (lay β) x | None => vres = Vundef end).
  { destruct v as [x|]; [|exact Hvres]. rewrite Hvres.
    apply den_ext with (n := length regs); [exact Hlay|exact Ev]. }
  assert (Hinv3 : inv ρ (slog Σb) m3).
  { eapply Hinv_stable; [exact Hinvb|]. eapply Mem.unchanged_on_implies; [exact Hun3|].
    intros b ofs He _ Hin. apply (HNinv b (HinN b Hin)). exact (Hext_valid _ _ _ _ Hinv He). }
  exists m3, vres. split.
  { eapply eval_funcall_internal.
    - constructor; [exact Hnr1|exact Hnr2|exact Hdj|exact Hav|exact Hbind].
    - exact Hexb.
    - exact Hres.
    - exact Hfl. }
  rewrite Hsel. simpl.
  split; [exact Hrep3|]. split; [exists v; split; [reflexivity|exact Hvr]|].
  split; [reflexivity|]. split.
  { rewrite <- firstn_map, Hshb, map_app, firstn_app, map_length, Nat.sub_diag.
    simpl. rewrite app_nil_r. apply firstn_all2. rewrite map_length. lia. }
  split; [exact Hinv3|].
  eapply Mem.unchanged_on_trans.
  { eapply Mem.unchanged_on_implies; [exact Hun1|]. intros; exact I. }
  eapply Mem.unchanged_on_trans.
  { eapply Mem.unchanged_on_implies; [exact Hunb|].
    intros b ofs (Hv & Hf & He) Hv1. split; [exact Hv1|]. split; [|exact He].
    intros (r & s & d & ch & Hs & Hin & Eb' & Hr).
    destruct (lt_dec r (length regs)) as [Hlt|Hge].
    - apply Hf. exists r, s, d, ch. simpl in Hs.
      rewrite map_app, nth_error_app1 in Hs by (rewrite map_length; exact Hlt).
      unfold blk, bas in *. rewrite Hlay in Eb', Hr by exact Hlt. auto.
    - apply (HNinv b); [|exact Hv]. subst b.
      assert (r < length β')%nat.
      { rewrite Hlenb. rewrite <- (map_length rshape). apply nth_error_Some. simpl in Hs. congruence. }
      unfold blk, lay, β'. rewrite app_nth2 by lia. apply in_map. apply nth_In.
      unfold β' in H0. rewrite app_length in H0. lia. }
  eapply Mem.unchanged_on_implies; [exact Hun3|].
  intros b ofs (Hv & Hf & He) _ Hin. exact (HNinv b (HinN b Hin) Hv).
Qed.

Theorem xstmt_sound n : sound_rec (xstmt ce gv fns n).
Proof.
  induction n as [|n IH]; intros ve Σ s rr H ρ β e le m Hrep Htm Hem Hgm Hsep Hinv Hsol; [discriminate|].
  destruct s; cbn [xstmt] in H; try discriminate.
  - (* Sskip *)
    inversion H; subst rr. exists le, m, Out_normal. split; [constructor|].
    split; [exact Hrep|]. split; [exact Htm|]. split; [exact I|]. split; [reflexivity|].
    split; [exact Hinv|apply Mem.unchanged_on_refl].
  - (* Sassign *)
    destruct (xlval ce ve gv Σ e0) as [[r0 d]|] eqn:El; [|discriminate].
    destruct (xexpr ce ve gv Σ e1) as [x2|] eqn:Ee; [|discriminate].
    destruct (access_mode (typeof e0)) as [ch| | |] eqn:AM; try discriminate.
    destruct (xcast x2 (typeof e1) (typeof e0)) as [x|] eqn:Ec; [|discriminate].
    destruct (xstore (sregs Σ) r0 d ch x) as [regs'|] eqn:Est; [|discriminate].
    inversion H; subst rr; clear H.
    destruct (xstore_sound ρ β _ m r0 d ch x regs' Hrep Est) as (m' & Hst & Hrange & Hrep' & Hun).
    exists le, m', Out_normal. split.
    + eapply exec_Sassign.
      * eapply xlval_sound; eauto. exact (proj1 Hgm).
      * eapply xexpr_sound; eauto. exact (proj1 Hgm).
      * apply xcast_sound. exact Ec.
      * eapply assign_loc_value; [exact AM|].
        simpl. rewrite Ptrofs.unsigned_repr by exact Hrange. exact Hst.
    + split; [exact Hrep'|]. split; [exact Htm|]. split; [exact I|].
      split; [exact (xstore_shape _ _ _ _ _ _ Est)|].
      split; [eapply Hinv_stable; [exact Hinv|eapply ext_unchanged; eauto]|].
      eapply Mem.unchanged_on_implies; [exact Hun|]. intros b o (Hv & Hf & He) _. exact Hf.
  - (* Sset *)
    destruct (xexpr ce ve gv Σ e0) as [x|] eqn:Ee; [|discriminate].
    inversion H; subst rr; clear H.
    exists (PTree.set i (den ρ (lay β) x) le), m, Out_normal. split.
    + apply exec_Sset. eapply xexpr_sound; eauto. exact (proj1 Hgm).
    + split; [exact Hrep|]. split; [apply tmatch_set; exact Htm|]. split; [exact I|].
      split; [reflexivity|]. split; [exact Hinv|apply Mem.unchanged_on_refl].
  - (* Scall *)
    destruct e0; try discriminate.
    destruct (vlookup ve i) eqn:Vl; [discriminate|].
    destruct (flookup fns i) as [ent|] eqn:Fl; [|discriminate].
    destruct t; try discriminate.
    destruct (type_eq (type_of_function (fentry_fd ent)) (Tfunction t t0 c)) as [Ety|]; [|discriminate].
    destruct (xargs ce ve gv Σ l t) as [xs|] eqn:Ea; [|discriminate].
    destruct (Hfns i ent Fl) as ((bf & Hsym & Hfp) & Hent).
    assert (Hcall : forall m3 vres,
      ClightBigstep.eval_funcall function_entry2 ge m (Internal (fentry_fd ent))
        (map (den ρ (lay β)) xs) E0 m3 vres ->
      exec e le m (Scall o (Evar i (Tfunction t t0 c)) l) E0 (set_opttemp o vres le) m3 Out_normal).
    { intros m3 vres Heval.
      eapply exec_Scall with (vf := Vptr bf Ptrofs.zero) (f := Internal (fentry_fd ent))
        (vargs := map (den ρ (lay β)) xs) (tyargs := t) (tyres := t0) (cconv := c).
      * reflexivity.
      * eapply eval_Elvalue.
        -- apply eval_Evar_global; [|exact Hsym].
           rewrite (proj1 (Hem i)), Vl. reflexivity.
        -- apply deref_loc_reference. reflexivity.
      * eapply xargs_sound; eauto. exact (proj1 Hgm).
      * simpl. destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero); [exact Hfp|congruence].
      * exact Ety.
      * exact Heval. }
    assert (Htmo : forall v vres,
      match v with Some x => vres = den ρ (lay β) x | None => vres = Vundef end ->
      tmatch ρ β (set_opt o v (stemps Σ)) (set_opttemp o vres le)).
    { intros v vres Hvr. destruct o as [id|]; simpl; [|exact Htm].
      destruct v as [x|]; simpl.
      - rewrite Hvr. apply tmatch_set. exact Htm.
      - intros id' x'. rewrite PTree.grspec. destruct (PTree.elt_eq id' id); [discriminate|].
        intros Hx. rewrite PTree.gso by assumption. apply Htm. exact Hx. }
    destruct ent as [fd|fd orc]; simpl in *.
    + destruct (xfun_sound _ IH fd xs (sregs Σ) (slog Σ) (snv Σ) (stemps Σ) o rr H ρ β m Hrep Hgm Hsep Hinv Hsol)
        as (m3 & vres & Heval & Hrep3 & (v & Hts & Hvr) & Hon & Hsh & Hinv3 & Hun).
      exists (set_opttemp o vres le), m3, Out_normal. split; [exact (Hcall m3 vres Heval)|].
      split; [exact Hrep3|]. split; [rewrite Hts; exact (Htmo v vres Hvr)|].
      split; [rewrite Hon; exact I|]. split; [exact Hsh|]. split; [exact Hinv3|exact Hun].
    + destruct (orc (snv Σ) (slog Σ) xs (sregs Σ)) as [[[[[regs' v] tag] cnt] eargs]|] eqn:Eo; [|discriminate].
      inversion H; subst rr; clear H. simpl in Hsol.
      destruct (solves_app _ _ _ Hsol) as [_ Hev]. inversion Hev as [|? ? Hev1 _]; subst.
      destruct (Hent (snv Σ) xs (sregs Σ) regs' v tag cnt eargs (slog Σ) ρ β m Eo Hrep Hsep Hinv Hev1)
        as (m3 & vres & Heval & Hrep3 & Hinv3 & Hsh & Hvr & Hun).
      exists (set_opttemp o vres le), m3, Out_normal. split; [exact (Hcall m3 vres Heval)|].
      split; [exact Hrep3|]. split; [exact (Htmo v vres Hvr)|].
      split; [exact I|]. split; [exact Hsh|]. split; [exact Hinv3|exact Hun].
  - (* Ssequence *)
    destruct (xstmt ce gv fns n ve Σ s1) as [r1|] eqn:E1; [|discriminate].
    destruct (tbind_sel ρ (lay β) _ _ _ H) as (rk & Hk & Hsel).
    rewrite Hsel in Hsol.
    assert (Hsol1 : solves ρ (slog (fst (rsel ρ (lay β) r1)))).
    { destruct (rsel ρ (lay β) r1) as [Σ1 o1]. simpl in *.
      destruct o1; try (inversion Hk; subst rk; exact Hsol).
      destruct (xstmt_lext _ _ _ _ _ _ _ _ Hk ρ (lay β)) as [suf Hs]. simpl in Hs.
      rewrite Hs in Hsol. exact (proj1 (solves_app _ _ _ Hsol)). }
    destruct (IH _ _ _ _ E1 ρ β e le m Hrep Htm Hem Hgm Hsep Hinv Hsol1) as (le1 & m1 & out1 & Hex1 & Hp1).
    pose proof Hp1 as (Hrep1 & Htm1 & Hom1 & Hsh1 & Hinv1 & Hun1).
    destruct (rsel ρ (lay β) r1) as [Σ1 o1] eqn:Es. simpl in Hk, Hrep1, Htm1, Hom1, Hsh1, Hinv1.
    destruct o1.
    + outinv Hom1 out1.
      destruct (IH _ _ _ _ Hk ρ β e le1 m1 Hrep1 Htm1 Hem Hgm Hsep Hinv1 Hsol) as (le2 & m2 & out2 & Hex2 & Hp2).
      exists le2, m2, out2. split.
      * change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto.
      * eapply post_sel; [exact Hsel|]. eapply post_trans; [exact Hp1|]. rewrite Es. exact Hp2.
    + inversion Hk; subst rk. exists le1, m1, out1. split.
      * eapply exec_Sseq_2; [exact Hex1|]. outinv Hom1 out1. discriminate.
      * eapply post_sel; [rewrite Hsel; simpl; symmetry; exact Es|exact Hp1].
    + inversion Hk; subst rk. exists le1, m1, out1. split.
      * eapply exec_Sseq_2; [exact Hex1|]. outinv Hom1 out1. discriminate.
      * eapply post_sel; [rewrite Hsel; simpl; symmetry; exact Es|exact Hp1].
    + inversion Hk; subst rk. exists le1, m1, out1. split.
      * eapply exec_Sseq_2; [exact Hex1|]. destruct v as [[? ?]|]; outinv Hom1 out1; discriminate.
      * eapply post_sel; [rewrite Hsel; simpl; symmetry; exact Es|exact Hp1].
  - (* Sifthenelse *)
    destruct (xexpr ce ve gv Σ e0) as [xa|] eqn:Ea; [|discriminate].
    destruct (xbool xa (typeof e0)) as [c|] eqn:Ebo; [|discriminate].
    assert (Hev := xexpr_sound ge ve gv ρ β Σ m e le Hrep Htm Hem (proj1 Hgm) e0 xa Ea).
    assert (Hb := xbool_sound ρ (lay β) xa (typeof e0) c m Ebo).
    destruct (is_const c) as [i|] eqn:Ec.
    + apply is_const_eq in Ec. subst c.
      destruct (IH _ _ _ _ H ρ β e le m Hrep Htm Hem Hgm Hsep Hinv Hsol) as (le1 & m1 & out1 & Hex1 & Hp1).
      exists le1, m1, out1. split; [|exact Hp1].
      eapply exec_Sifthenelse; [exact Hev|exact Hb|exact Hex1].
    + destruct (xstmt ce gv fns n ve Σ s1) as [r1|] eqn:E1; [|discriminate].
      destruct (xstmt ce gv fns n ve Σ s2) as [r2|] eqn:E2; [|discriminate].
      inversion H; subst rr; clear H. simpl in Hsol.
      destruct (truth ρ (lay β) c) eqn:T.
      * destruct (IH _ _ _ _ E1 ρ β e le m Hrep Htm Hem Hgm Hsep Hinv Hsol) as (le1 & m1 & out1 & Hex1 & Hp1).
        exists le1, m1, out1. split.
        -- eapply exec_Sifthenelse; [exact Hev|exact Hb|exact Hex1].
        -- eapply post_sel; [simpl; rewrite T; reflexivity|exact Hp1].
      * destruct (IH _ _ _ _ E2 ρ β e le m Hrep Htm Hem Hgm Hsep Hinv Hsol) as (le1 & m1 & out1 & Hex1 & Hp1).
        exists le1, m1, out1. split.
        -- eapply exec_Sifthenelse; [exact Hev|exact Hb|exact Hex1].
        -- eapply post_sel; [simpl; rewrite T; reflexivity|exact Hp1].
  - (* Sloop *)
    destruct (xstmt ce gv fns n ve Σ s1) as [r1|] eqn:E1; [|discriminate].
    destruct (tbind_sel ρ (lay β) _ _ _ H) as (rk & Hk & Hsel).
    rewrite Hsel in Hsol.
    (* log facts for the three stages *)
    assert (Hsols : solves ρ (slog (fst (rsel ρ (lay β) r1))) /\
      forall r2, xstmt ce gv fns n ve (fst (rsel ρ (lay β) r1)) s2 = Some r2 ->
        forall rk2,
        (fun Σ2 o2 =>
            match o2 with
            | OBreak => Some (RDone Σ2 ONormal)
            | OReturn v => Some (RDone Σ2 (OReturn v))
            | ONormal => xstmt ce gv fns n ve Σ2 (Sloop s1 s2)
            | OContinue => None
            end) (fst (rsel ρ (lay β) r2)) (snd (rsel ρ (lay β) r2)) = Some rk2 ->
        rsel ρ (lay β) rk = rsel ρ (lay β) rk2 ->
        solves ρ (slog (fst (rsel ρ (lay β) r2)))).
    { assert (Hin : forall r2, xstmt ce gv fns n ve (fst (rsel ρ (lay β) r1)) s2 = Some r2 ->
        forall rk2,
        (fun Σ2 o2 =>
            match o2 with
            | OBreak => Some (RDone Σ2 ONormal)
            | OReturn v => Some (RDone Σ2 (OReturn v))
            | ONormal => xstmt ce gv fns n ve Σ2 (Sloop s1 s2)
            | OContinue => None
            end) (fst (rsel ρ (lay β) r2)) (snd (rsel ρ (lay β) r2)) = Some rk2 ->
        rsel ρ (lay β) rk = rsel ρ (lay β) rk2 ->
        solves ρ (slog (fst (rsel ρ (lay β) r2)))).
      { intros r2 E2 rk2 Hk3 Hsel2. rewrite Hsel2 in Hsol.
        destruct (rsel ρ (lay β) r2) as [Σ2 o2]. simpl in *.
        destruct o2; try discriminate; try (inversion Hk3; subst rk2; exact Hsol).
        destruct (xstmt_lext _ _ _ _ _ _ _ _ Hk3 ρ (lay β)) as [suf Hs]. simpl in Hs.
        rewrite Hs in Hsol. exact (proj1 (solves_app _ _ _ Hsol)). }
      split; [|exact Hin].
      destruct (rsel ρ (lay β) r1) as [Σ1 o1]. simpl in *.
      assert (Hc : match xstmt ce gv fns n ve Σ1 s2 with
              | Some r2 =>
                  tbind r2 (fun Σ2 o2 =>
                    match o2 with
                    | OBreak => Some (RDone Σ2 ONormal)
                    | OReturn v => Some (RDone Σ2 (OReturn v))
                    | ONormal => xstmt ce gv fns n ve Σ2 (Sloop s1 s2)
                    | OContinue => None
                    end)
              | None => None
              end = Some rk -> solves ρ (slog Σ1)).
      { intros Hk2. destruct (xstmt ce gv fns n ve Σ1 s2) as [r2|] eqn:E2; [|discriminate].
        destruct (tbind_sel ρ (lay β) _ _ _ Hk2) as (rk2 & Hk3 & Hsel2).
        pose proof (Hin r2 eq_refl rk2 Hk3 Hsel2) as Hs2.
        destruct (xstmt_lext _ _ _ _ _ _ _ _ E2 ρ (lay β)) as [suf Hs]. simpl in Hs.
        rewrite Hs in Hs2. exact (proj1 (solves_app _ _ _ Hs2)). }
      destruct o1; try (apply Hc; exact Hk); inversion Hk; subst rk; exact Hsol. }
    destruct Hsols as [Hsol1 Hsol2].
    destruct (IH _ _ _ _ E1 ρ β e le m Hrep Htm Hem Hgm Hsep Hinv Hsol1) as (le1 & m1 & out1 & Hex1 & Hp1).
    pose proof Hp1 as (Hrep1 & Htm1 & Hom1 & Hsh1 & Hinv1 & Hun1).
    destruct (rsel ρ (lay β) r1) as [Σ1 o1] eqn:Es. simpl in Hk, Hrep1, Htm1, Hom1, Hsh1, Hinv1, Hsol2.
    assert (Hcont : forall (Hnc : out_normal_or_continue out1),
              match xstmt ce gv fns n ve Σ1 s2 with
              | Some r2 =>
                  tbind r2 (fun Σ2 o2 =>
                    match o2 with
                    | OBreak => Some (RDone Σ2 ONormal)
                    | OReturn v => Some (RDone Σ2 (OReturn v))
                    | ONormal => xstmt ce gv fns n ve Σ2 (Sloop s1 s2)
                    | OContinue => None
                    end)
              | None => None
              end = Some rk ->
              exists le' m' out, exec e le m (Sloop s1 s2) E0 le' m' out /\ post ρ β Σ m rr le' m' out).
    { intros Hnc Hk2.
      destruct (xstmt ce gv fns n ve Σ1 s2) as [r2|] eqn:E2; [|discriminate].
      destruct (tbind_sel ρ (lay β) _ _ _ Hk2) as (rk2 & Hk3 & Hsel2).
      pose proof (Hsol2 r2 eq_refl rk2 Hk3 Hsel2) as Hs2.
      destruct (IH _ _ _ _ E2 ρ β e le1 m1 Hrep1 Htm1 Hem Hgm Hsep Hinv1 Hs2) as (le2 & m2 & out2 & Hex2 & Hp2).
      pose proof Hp2 as (Hrep2 & Htm2 & Hom2 & Hsh2 & Hinv2 & Hun2).
      assert (Hp12 : post ρ β Σ m r2 le2 m2 out2).
      { eapply post_trans; [exact Hp1|]. rewrite Es. exact Hp2. }
      rewrite Hsel2 in Hsol.
      destruct (rsel ρ (lay β) r2) as [Σ2 o2] eqn:Es2. simpl in Hk3, Hrep2, Htm2, Hom2, Hsh2, Hinv2.
      destruct o2.
      - outinv Hom2 out2.
        destruct (IH _ _ _ _ Hk3 ρ β e le2 m2 Hrep2 Htm2 Hem Hgm Hsep Hinv2 Hsol) as (le3 & m3 & out3 & Hex3 & Hp3).
        exists le3, m3, out3. split.
        + change E0 with (E0 ** E0 ** E0). eapply exec_Sloop_loop; eauto.
        + eapply post_sel; [rewrite Hsel; exact Hsel2|].
          eapply post_trans; [exact Hp12|]. rewrite Es2. exact Hp3.
      - inversion Hk3; subst rk2. outinv Hom2 out2.
        exists le2, m2, Out_normal. split.
        + change E0 with (E0 ** E0). eapply exec_Sloop_stop2; eauto. constructor.
        + eapply post_sel; [rewrite Hsel, Hsel2; reflexivity|].
          destruct Hp12 as (A & B & C & D & E & G). rewrite Es2 in A, B, D, E.
          split; [exact A|]. split; [exact B|]. split; [exact I|]. split; [exact D|]. split; [exact E|exact G].
      - discriminate.
      - inversion Hk3; subst rk2.
        exists le2, m2, out2. split.
        + change E0 with (E0 ** E0). eapply exec_Sloop_stop2; eauto.
          destruct v as [[? ?]|]; outinv Hom2 out2; constructor.
        + eapply post_sel; [rewrite Hsel, Hsel2; simpl; symmetry; exact Es2|exact Hp12]. }
    destruct o1.
    + apply Hcont; [outinv Hom1 out1; constructor|exact Hk].
    + inversion Hk; subst rk. outinv Hom1 out1.
      exists le1, m1, Out_normal. split.
      * eapply exec_Sloop_stop1; [exact Hex1|constructor].
      * eapply post_sel; [rewrite Hsel; reflexivity|].
        destruct Hp1 as (A & B & C & D & E & G). rewrite Es in A, B, D, E.
        split; [exact A|]. split; [exact B|]. split; [exact I|]. split; [exact D|]. split; [exact E|exact G].
    + apply Hcont; [outinv Hom1 out1; constructor|exact Hk].
    + inversion Hk; subst rk.
      exists le1, m1, out1. split.
      * eapply exec_Sloop_stop1; [exact Hex1|]. destruct v as [[? ?]|]; outinv Hom1 out1; constructor.
      * eapply post_sel; [rewrite Hsel; simpl; symmetry; exact Es|exact Hp1].
  - (* Sbreak *)
    inversion H; subst rr. exists le, m, Out_break. split; [constructor|].
    split; [exact Hrep|]. split; [exact Htm|]. split; [exact I|]. split; [reflexivity|].
    split; [exact Hinv|apply Mem.unchanged_on_refl].
  - (* Scontinue *)
    inversion H; subst rr. exists le, m, Out_continue. split; [constructor|].
    split; [exact Hrep|]. split; [exact Htm|]. split; [exact I|]. split; [reflexivity|].
    split; [exact Hinv|apply Mem.unchanged_on_refl].
  - (* Sreturn *)
    destruct o as [a|].
    + destruct (xexpr ce ve gv Σ a) as [x|] eqn:Ee; [|discriminate].
      inversion H; subst rr; clear H.
      exists le, m, (Out_return (Some (den ρ (lay β) x, typeof a))). split.
      * apply exec_Sreturn_some. eapply xexpr_sound; eauto. exact (proj1 Hgm).
      * split; [exact Hrep|]. split; [exact Htm|]. split; [split; reflexivity|].
        split; [reflexivity|]. split; [exact Hinv|apply Mem.unchanged_on_refl].
    + inversion H; subst rr. exists le, m, (Out_return None). split; [constructor|].
      split; [exact Hrep|]. split; [exact Htm|]. split; [exact I|]. split; [reflexivity|].
      split; [exact Hinv|apply Mem.unchanged_on_refl].
Qed.

(** A successful symbolic run of a whole function is a big-step call. *)
Theorem xfun_top_sound n fd xs regs log nv rr :
  xfun ce gv fns n fd xs regs log nv = Some rr ->
  forall ρ β m, rep ρ β regs m -> gmatch2 ge β gv -> xsep β -> inv ρ log m ->
  solves ρ (slog (fst (rsel ρ (lay β) rr))) ->
  exists m' vres,
    ClightBigstep.eval_funcall function_entry2 ge m (Internal fd) (map (den ρ (lay β)) xs) E0 m' vres /\
    rep ρ β (sregs (fst (rsel ρ (lay β) rr))) m' /\
    match (stemps (fst (rsel ρ (lay β) rr)))!1%positive with
    | Some x => vres = den ρ (lay β) x
    | None => vres = Vundef
    end /\
    map rshape (sregs (fst (rsel ρ (lay β) rr))) = map rshape regs /\
    inv ρ (slog (fst (rsel ρ (lay β) rr))) m' /\
    Mem.unchanged_on (frame β regs m) m m'.
Proof.
  intros H ρ β m Hrep Hgm Hsep Hinv Hsol.
  destruct (xfun_sound _ (xstmt_sound n) fd xs regs log nv (PTree.empty sx) (Some 1%positive) rr H
              ρ β m Hrep Hgm Hsep Hinv Hsol)
    as (m3 & vres & Heval & Hrep3 & (v & Hts & Hvr) & Hon & Hsh & Hinv3 & Hun).
  exists m3, vres. split; [exact Heval|]. split; [exact Hrep3|]. split.
  - rewrite Hts. destruct v as [x|]; unfold set_opt.
    + rewrite PTree.gss. exact Hvr.
    + rewrite PTree.grs. exact Hvr.
  - split; [exact Hsh|]. split; [exact Hinv3|exact Hun].
Qed.
End SOUND.

Lemma flookup_In fns id ent : flookup fns id = Some ent -> In (id, ent) fns.
Proof.
  induction fns as [|[i f] t IH]; simpl; [discriminate|].
  destruct (Pos.eqb i id) eqn:E.
  - apply Pos.eqb_eq in E. intros H; inversion H; subst. left; reflexivity.
  - intros H. right. exact (IH H).
Qed.
