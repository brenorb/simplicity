(** A verified symbolic executor for Clight statements and internal calls:
    [xstmt] computes, for a symbolic state, a decision tree of final symbolic
    states; [xstmt_sound] turns a successful run into a Clight big-step
    execution whose final memory satisfies the selected final state. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Inductive xout := ONormal | OBreak | OContinue | OReturn (v : option (sx * type)).
Inductive res := RDone (Σ : sstate) (o : xout) | RIf (c : sx) (a b : res).

Fixpoint rsel (β : nat -> block * Z) (r : res) : sstate * xout :=
  match r with
  | RDone Σ o => (Σ, o)
  | RIf c a b => if truth β c then rsel β a else rsel β b
  end.

Lemma rsel_indep β β' r : rsel β r = rsel β' r.
Proof.
  induction r; simpl; [reflexivity|]. rewrite (truth_indep β β'), IHr1, IHr2. reflexivity.
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

Lemma tbind_sel β r k r' :
  tbind r k = Some r' ->
  exists rk, k (fst (rsel β r)) (snd (rsel β r)) = Some rk /\ rsel β r' = rsel β rk.
Proof.
  revert r'. induction r as [Σ o|c a IHa b IHb]; simpl; intros r' H.
  - exists r'. split; [exact H|reflexivity].
  - destruct (tbind a k) as [a'|] eqn:Ea; [|discriminate].
    destruct (tbind b k) as [b'|] eqn:Eb; [|discriminate].
    inversion H; subst r'. simpl. destruct (truth β c); [apply IHa|apply IHb]; reflexivity.
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

Fixpoint flookup (fns : list (ident * function)) (id : ident) : option function :=
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
Variable fns : list (ident * function).

Definition xcall_ret (optid : option ident) (ts : PTree.t sx) (nreg : nat) (ty : type)
    (Σb : sstate) (ob : xout) : option res :=
  match xret ty ob with
  | Some v =>
      if match v with Some x => xp_lt nreg x | None => true end
      then Some (RDone (mkst (set_opt optid v ts) (firstn nreg (sregs Σb))) ONormal)
      else None
  | None => None
  end.

(** Entry into, execution of, and return from an internal function, given
    an executor [rec] for its body. *)
Definition xfun_with (rec : venv -> sstate -> statement -> option res)
    (fd : function) (xs : list sx) (regs : list region)
    (k : sstate -> xout -> option res) : option res :=
  if fn_okb fd then
    if forallb (xp_lt (length regs)) xs then
      match xalloc ce (fn_vars fd) (length regs), xbind (fn_params fd) xs (PTree.empty sx) with
      | Some (regsN, veN), Some ts0 =>
          match rec veN (mkst ts0 (regs ++ regsN)) (fn_body fd) with
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
        | Some x => Some (RDone (mkst (PTree.set id x (stemps Σ)) (sregs Σ)) ONormal)
        | None => None
        end
    | Sassign a1 a2 =>
        match xlval ce ve gv Σ a1, xexpr ce ve gv Σ a2, access_mode (typeof a1) with
        | Some (r, d), Some x2, By_value ch =>
            match xcast x2 (typeof a2) (typeof a1) with
            | Some x =>
                match xstore (sregs Σ) r d ch x with
                | Some regs' => Some (RDone (mkst (stemps Σ) regs') ONormal)
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
        | None, Some fd, Tfunction tyargs tyres cc =>
            if type_eq (type_of_function fd) fty then
              match xargs ce ve gv Σ al tyargs with
              | Some xs =>
                  xfun_with (xstmt n) fd xs (sregs Σ)
                    (xcall_ret optid (stemps Σ) (length (sregs Σ)) (fn_return fd))
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
Definition xfun (n : nat) (fd : function) (xs : list sx) (regs : list region) : option res :=
  xfun_with (xstmt n) fd xs regs (xcall_ret (Some 1%positive) (PTree.empty sx) (length regs) (fn_return fd)).
End EXEC.

(** ** Soundness *)
Definition outmatch (β : layout) (o : xout) (out : outcome) : Prop :=
  match o, out with
  | ONormal, Out_normal | OBreak, Out_break | OContinue, Out_continue => True
  | OReturn None, Out_return None => True
  | OReturn (Some (x, ty)), Out_return (Some (v, ty')) => v = den (lay β) x /\ ty' = ty
  | _, _ => False
  end.

Definition frame (β : layout) (Σ : sstate) (m : mem) : block -> Z -> Prop :=
  fun b o => Mem.valid_block m b /\ ~ foot β (map rshape (sregs Σ)) b o.

Definition post (β : layout) (Σ0 : sstate) (m0 : mem) (r : res)
    (le' : temp_env) (m' : mem) (out : outcome) : Prop :=
  rep β (sregs (fst (rsel (lay β) r))) m' /\
  tmatch β (stemps (fst (rsel (lay β) r))) le' /\
  outmatch β (snd (rsel (lay β) r)) out /\
  map rshape (sregs (fst (rsel (lay β) r))) = map rshape (sregs Σ0) /\
  Mem.unchanged_on (frame β Σ0 m0) m0 m'.

Lemma post_sel β Σ m r r' le' m' out :
  rsel (lay β) r = rsel (lay β) r' -> post β Σ m r' le' m' out -> post β Σ m r le' m' out.
Proof. unfold post. intros ->. auto. Qed.

Lemma post_trans β Σ m r1 le1 m1 out1 r2 le2 m2 out2 :
  post β Σ m r1 le1 m1 out1 -> post β (fst (rsel (lay β) r1)) m1 r2 le2 m2 out2 ->
  post β Σ m r2 le2 m2 out2.
Proof.
  intros (R1 & T1 & O1 & S1 & U1) (R2 & T2 & O2 & S2 & U2).
  split; [exact R2|]. split; [exact T2|]. split; [exact O2|]. split; [congruence|].
  eapply Mem.unchanged_on_trans; [exact U1|].
  eapply Mem.unchanged_on_implies; [exact U2|].
  intros b o [Hv Hf] _. split.
  - eapply Mem.valid_block_unchanged_on; eauto.
  - unfold frame in *. rewrite S1. exact Hf.
Qed.

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

Lemma xret_sound β ty ob out m v :
  xret ty ob = Some v -> outmatch β ob out ->
  exists vres, outcome_result_value out ty vres m /\
    match v with Some x => vres = den (lay β) x | None => vres = Vundef end.
Proof.
  unfold xret. intros H Hom.
  destruct ob as [| | |[[x tx]|]]; try discriminate;
    destruct out as [| | |[[v' ty']|]]; simpl in Hom; try contradiction.
  - destruct ty; try discriminate. inversion H; subst. exists Vundef. split; reflexivity.
  - destruct Hom as [-> ->].
    destruct (xcast x tx ty) as [v0|] eqn:Ec; [|destruct ty; discriminate].
    assert (ty <> Tvoid) by (destruct ty; discriminate || congruence).
    assert (v = Some v0) by (destruct ty; congruence). subst v.
    exists (den (lay β) v0). split; [|reflexivity].
    simpl. split; [exact H0|]. apply xcast_sound. exact Ec.
  - destruct ty; try discriminate. inversion H; subst. exists Vundef. split; reflexivity.
Qed.

Lemma map_den_ext (β β' : nat -> block * Z) n xs :
  (forall r, (r < n)%nat -> β' r = β r) -> forallb (xp_lt n) xs = true ->
  map (den β') xs = map (den β) xs.
Proof.
  intros H. induction xs as [|x xs IH]; simpl; intros F; [reflexivity|].
  apply andb_true_iff in F. destruct F as [F1 F2].
  rewrite (den_ext x β β' n H F1), (IH F2). reflexivity.
Qed.

Section SOUND.
Variable ge : genv.
Variable gv : venv.
Variable fns : list (ident * function).
Hypothesis Hfns : forall id fd, flookup fns id = Some fd ->
  exists b, Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some (Internal fd).

Notation ce := (genv_cenv ge).
Notation exec := (ClightBigstep.exec_stmt function_entry2 ge).

Ltac outinv Hom out :=
  destruct out as [| | |[[? ?]|]]; simpl in Hom; try contradiction.

Lemma xfun_sound (rec : venv -> sstate -> statement -> option res)
  (IH : forall ve Σ s r, rec ve Σ s = Some r ->
     forall β e le m,
       rep β (sregs Σ) m -> tmatch β (stemps Σ) le -> ematch β ve e -> gmatch2 ge β gv ->
       exists le' m' out, exec e le m s E0 le' m' out /\ post β Σ m r le' m' out)
  fd xs regs ts optid rr :
  xfun_with ce rec fd xs regs (xcall_ret optid ts (length regs) (fn_return fd)) = Some rr ->
  forall β m, rep β regs m -> gmatch2 ge β gv ->
  exists m3 vres,
    ClightBigstep.eval_funcall function_entry2 ge m (Internal fd) (map (den (lay β)) xs) E0 m3 vres /\
    rep β (sregs (fst (rsel (lay β) rr))) m3 /\
    (exists v, stemps (fst (rsel (lay β) rr)) = set_opt optid v ts /\
       match v with Some x => vres = den (lay β) x | None => vres = Vundef end) /\
    snd (rsel (lay β) rr) = ONormal /\
    map rshape (sregs (fst (rsel (lay β) rr))) = map rshape regs /\
    Mem.unchanged_on (frame β (mkst ts regs) m) m m3.
Proof.
  unfold xfun_with. intros H β m Hrep Hgm.
  destruct (fn_okb fd) eqn:Fok; [|discriminate].
  destruct (forallb (xp_lt (length regs)) xs) eqn:Fa; [|discriminate].
  destruct (xalloc ce (fn_vars fd) (length regs)) as [[regsN veN]|] eqn:Eal; [|discriminate].
  destruct (xbind (fn_params fd) xs (PTree.empty sx)) as [ts0|] eqn:Ebd; [|discriminate].
  destruct (rec veN (mkst ts0 (regs ++ regsN)) (fn_body fd)) as [rb|] eqn:Eb; [|discriminate].
  destruct (fn_okb_true fd Fok) as (Hnr1 & Hnr2 & Hdj).
  assert (Hlen : length β = length regs) by (destruct Hrep as (HH & _); exact HH).
  destruct (xalloc_sound ge (fn_vars fd) (length regs) regsN veN β regs m empty_env
              Eal Hrep Hlen Hnr1)
    as (e' & m1 & βN & Hav & Hrep1 & HlenN & He' & Hidx & Hinj & Hnv & Hun1).
  set (β' := β ++ βN) in *.
  assert (Hlay : forall r, (r < length regs)%nat -> lay β' r = lay β r).
  { intros r Hr. apply lay_app_l. lia. }
  assert (Hargs : map (den (lay β')) xs = map (den (lay β)) xs).
  { apply map_den_ext with (n := length regs); [exact Hlay|exact Fa]. }
  destruct (xbind_sound β' (fn_params fd) xs (PTree.empty sx) ts0
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
  destruct (IH veN _ _ rb Eb β' e' le1 m1 Hrep1 Htm0 Hem' Hgm')
    as (le2 & m2 & out2 & Hexb & Hrepb & Htmb & Homb & Hshb & Hunb).
  destruct (tbind_sel (lay β) _ _ _ H) as (rk & Hk & Hsel).
  rewrite (rsel_indep (lay β') (lay β)) in Hrepb, Htmb, Homb, Hshb.
  destruct (rsel (lay β) rb) as [Σb ob]. simpl in Hk, Hrepb, Htmb, Homb, Hshb.
  unfold xcall_ret in Hk.
  destruct (xret (fn_return fd) ob) as [v|] eqn:Er; [|discriminate].
  destruct (match v with Some x => xp_lt (length regs) x | None => true end) eqn:Ev; [|discriminate].
  inversion Hk; subst rk; clear Hk.
  destruct (xret_sound β' _ _ out2 m2 v Er Homb) as (vres & Hres & Hvres).
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
  assert (HNinv : forall b, In b (map fst βN) -> ~ Mem.valid_block m b).
  { intros b Hin. apply in_map_iff in Hin. destruct Hin as (p & <- & Hp).
    exact (proj1 (Forall_forall _ _) Hnv p Hp). }
  assert (HβN : forall b, In b (map fst β) -> ~ In b (map fst βN)).
  { intros b H1 H2. unfold β' in Hnrb. rewrite map_app in Hnrb.
    apply list_norepet_app in Hnrb. destruct Hnrb as (_ & _ & Hd). exact (Hd b b H1 H2 eq_refl). }
  assert (Hlenb2 : length (sregs Σb) = length (regs ++ regsN)).
  { rewrite <- (map_length rshape (sregs Σb)), Hshb, map_length. reflexivity. }
  assert (Hrep3 : rep β (firstn (length regs) (sregs Σb)) m3).
  { eapply rep_mem with (m := m2).
    - eapply Mem.unchanged_on_implies; [exact Hun3|]. intros b ofs Hb _ Hin.
      exact (HβN b Hb (HinN b Hin)).
    - eapply rep_prefix with (βN := βN) (regsN := skipn (length regs) (sregs Σb)).
      + rewrite firstn_skipn. exact Hrepb.
      + rewrite firstn_length, Hlenb2, app_length. lia. }
  assert (Hvr : match v with Some x => vres = den (lay β) x | None => vres = Vundef end).
  { destruct v as [x|]; [|exact Hvres]. rewrite Hvres.
    apply den_ext with (n := length regs); [exact Hlay|exact Ev]. }
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
  eapply Mem.unchanged_on_trans.
  { eapply Mem.unchanged_on_implies; [exact Hun1|]. intros; exact I. }
  eapply Mem.unchanged_on_trans.
  { eapply Mem.unchanged_on_implies; [exact Hunb|].
    intros b ofs [Hv Hf] Hv1. split; [exact Hv1|].
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
  intros b ofs [Hv Hf] _ Hin. exact (HNinv b (HinN b Hin) Hv).
Qed.

Theorem xstmt_sound n : forall ve Σ s r,
  xstmt ce gv fns n ve Σ s = Some r ->
  forall β e le m,
    rep β (sregs Σ) m -> tmatch β (stemps Σ) le -> ematch β ve e -> gmatch2 ge β gv ->
    exists le' m' out, exec e le m s E0 le' m' out /\ post β Σ m r le' m' out.
Proof.
  induction n as [|n IH]; intros ve Σ s rr H β e le m Hrep Htm Hem Hgm; [discriminate|].
  destruct s; cbn [xstmt] in H; try discriminate.
  - (* Sskip *)
    inversion H; subst rr. exists le, m, Out_normal. split; [constructor|].
    split; [exact Hrep|]. split; [exact Htm|]. split; [exact I|]. split; [reflexivity|apply Mem.unchanged_on_refl].
  - (* Sassign *)
    destruct (xlval ce ve gv Σ e0) as [[r0 d]|] eqn:El; [|discriminate].
    destruct (xexpr ce ve gv Σ e1) as [x2|] eqn:Ee; [|discriminate].
    destruct (access_mode (typeof e0)) as [ch| | |] eqn:AM; try discriminate.
    destruct (xcast x2 (typeof e1) (typeof e0)) as [x|] eqn:Ec; [|discriminate].
    destruct (xstore (sregs Σ) r0 d ch x) as [regs'|] eqn:Est; [|discriminate].
    inversion H; subst rr; clear H.
    destruct (xstore_sound β _ m r0 d ch x regs' Hrep Est) as (m' & Hst & Hrange & Hrep' & Hun).
    exists le, m', Out_normal. split.
    + eapply exec_Sassign.
      * eapply xlval_sound; eauto. exact (proj1 Hgm).
      * eapply xexpr_sound; eauto. exact (proj1 Hgm).
      * apply xcast_sound. exact Ec.
      * eapply assign_loc_value; [exact AM|].
        simpl. rewrite Ptrofs.unsigned_repr by exact Hrange. exact Hst.
    + split; [exact Hrep'|]. split; [exact Htm|]. split; [exact I|].
      split; [exact (xstore_shape _ _ _ _ _ _ Est)|].
      eapply Mem.unchanged_on_implies; [exact Hun|]. intros b o [Hv Hf] _. exact Hf.
  - (* Sset *)
    destruct (xexpr ce ve gv Σ e0) as [x|] eqn:Ee; [|discriminate].
    inversion H; subst rr; clear H.
    exists (PTree.set i (den (lay β) x) le), m, Out_normal. split.
    + apply exec_Sset. eapply xexpr_sound; eauto. exact (proj1 Hgm).
    + split; [exact Hrep|]. split; [apply tmatch_set; exact Htm|]. split; [exact I|].
      split; [reflexivity|apply Mem.unchanged_on_refl].
  - (* Scall *)
    destruct e0; try discriminate.
    destruct (vlookup ve i) eqn:Vl; [discriminate|].
    destruct (flookup fns i) as [fd|] eqn:Fl; [|discriminate].
    destruct t; try discriminate.
    destruct (type_eq (type_of_function fd) (Tfunction t t0 c)) as [Ety|]; [|discriminate].
    destruct (xargs ce ve gv Σ l t) as [xs|] eqn:Ea; [|discriminate].
    destruct (xfun_sound _ IH fd xs (sregs Σ) (stemps Σ) o rr H β m Hrep Hgm)
      as (m3 & vres & Heval & Hrep3 & (v & Hts & Hvr) & Hon & Hsh & Hun).
    destruct (Hfns i fd Fl) as (bf & Hsym & Hfp).
    exists (set_opttemp o vres le), m3, Out_normal. split.
    + eapply exec_Scall with (vf := Vptr bf Ptrofs.zero) (f := Internal fd)
        (vargs := map (den (lay β)) xs) (tyargs := t) (tyres := t0) (cconv := c).
      * reflexivity.
      * eapply eval_Elvalue.
        -- apply eval_Evar_global; [|exact Hsym].
           rewrite (proj1 (Hem i)), Vl. reflexivity.
        -- apply deref_loc_reference. reflexivity.
      * eapply xargs_sound; eauto. exact (proj1 Hgm).
      * simpl. destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero); [exact Hfp|congruence].
      * exact Ety.
      * exact Heval.
    + split; [exact Hrep3|]. split.
      { rewrite Hts. destruct o as [id|]; simpl; [|exact Htm].
        destruct v as [x|]; simpl.
        - rewrite Hvr. apply tmatch_set. exact Htm.
        - intros id' x'. rewrite PTree.grspec. destruct (PTree.elt_eq id' id); [discriminate|].
          intros Hx. rewrite PTree.gso by assumption. apply Htm. exact Hx. }
      split; [rewrite Hon; exact I|]. split; [exact Hsh|exact Hun].
  - (* Ssequence *)
    destruct (xstmt ce gv fns n ve Σ s1) as [r1|] eqn:E1; [|discriminate].
    destruct (IH _ _ _ _ E1 β e le m Hrep Htm Hem Hgm) as (le1 & m1 & out1 & Hex1 & Hp1).
    destruct (tbind_sel (lay β) _ _ _ H) as (rk & Hk & Hsel).
    pose proof Hp1 as (Hrep1 & Htm1 & Hom1 & Hsh1 & Hun1).
    destruct (rsel (lay β) r1) as [Σ1 o1] eqn:Es. simpl in Hk, Hrep1, Htm1, Hom1, Hsh1.
    destruct o1.
    + outinv Hom1 out1.
      destruct (IH _ _ _ _ Hk β e le1 m1 Hrep1 Htm1 Hem Hgm) as (le2 & m2 & out2 & Hex2 & Hp2).
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
    assert (Hev := xexpr_sound ge ve gv β Σ m e le Hrep Htm Hem (proj1 Hgm) e0 xa Ea).
    assert (Hb := xbool_sound (lay β) xa (typeof e0) c m Ebo).
    destruct (is_const c) as [i|] eqn:Ec.
    + apply is_const_eq in Ec. subst c.
      destruct (IH _ _ _ _ H β e le m Hrep Htm Hem Hgm) as (le1 & m1 & out1 & Hex1 & Hp1).
      exists le1, m1, out1. split; [|exact Hp1].
      eapply exec_Sifthenelse; [exact Hev|exact Hb|exact Hex1].
    + destruct (xstmt ce gv fns n ve Σ s1) as [r1|] eqn:E1; [|discriminate].
      destruct (xstmt ce gv fns n ve Σ s2) as [r2|] eqn:E2; [|discriminate].
      inversion H; subst rr; clear H.
      destruct (truth (lay β) c) eqn:T.
      * destruct (IH _ _ _ _ E1 β e le m Hrep Htm Hem Hgm) as (le1 & m1 & out1 & Hex1 & Hp1).
        exists le1, m1, out1. split.
        -- eapply exec_Sifthenelse; [exact Hev|exact Hb|exact Hex1].
        -- eapply post_sel; [simpl; rewrite T; reflexivity|exact Hp1].
      * destruct (IH _ _ _ _ E2 β e le m Hrep Htm Hem Hgm) as (le1 & m1 & out1 & Hex1 & Hp1).
        exists le1, m1, out1. split.
        -- eapply exec_Sifthenelse; [exact Hev|exact Hb|exact Hex1].
        -- eapply post_sel; [simpl; rewrite T; reflexivity|exact Hp1].
  - (* Sloop *)
    destruct (xstmt ce gv fns n ve Σ s1) as [r1|] eqn:E1; [|discriminate].
    destruct (IH _ _ _ _ E1 β e le m Hrep Htm Hem Hgm) as (le1 & m1 & out1 & Hex1 & Hp1).
    destruct (tbind_sel (lay β) _ _ _ H) as (rk & Hk & Hsel).
    pose proof Hp1 as (Hrep1 & Htm1 & Hom1 & Hsh1 & Hun1).
    destruct (rsel (lay β) r1) as [Σ1 o1] eqn:Es. simpl in Hk, Hrep1, Htm1, Hom1, Hsh1.
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
              exists le' m' out, exec e le m (Sloop s1 s2) E0 le' m' out /\ post β Σ m rr le' m' out).
    { intros Hnc Hk2.
      destruct (xstmt ce gv fns n ve Σ1 s2) as [r2|] eqn:E2; [|discriminate].
      destruct (IH _ _ _ _ E2 β e le1 m1 Hrep1 Htm1 Hem Hgm) as (le2 & m2 & out2 & Hex2 & Hp2).
      destruct (tbind_sel (lay β) _ _ _ Hk2) as (rk2 & Hk3 & Hsel2).
      pose proof Hp2 as (Hrep2 & Htm2 & Hom2 & Hsh2 & Hun2).
      assert (Hp12 : post β Σ m r2 le2 m2 out2).
      { eapply post_trans; [exact Hp1|]. rewrite Es. exact Hp2. }
      destruct (rsel (lay β) r2) as [Σ2 o2] eqn:Es2. simpl in Hk3, Hrep2, Htm2, Hom2, Hsh2.
      destruct o2.
      - outinv Hom2 out2.
        destruct (IH _ _ _ _ Hk3 β e le2 m2 Hrep2 Htm2 Hem Hgm) as (le3 & m3 & out3 & Hex3 & Hp3).
        exists le3, m3, out3. split.
        + change E0 with (E0 ** E0 ** E0). eapply exec_Sloop_loop; eauto.
        + eapply post_sel; [rewrite Hsel; exact Hsel2|].
          eapply post_trans; [exact Hp12|]. rewrite Es2. exact Hp3.
      - inversion Hk3; subst rk2. outinv Hom2 out2.
        exists le2, m2, Out_normal. split.
        + change E0 with (E0 ** E0). eapply exec_Sloop_stop2; eauto. constructor.
        + eapply post_sel; [rewrite Hsel, Hsel2; reflexivity|].
          destruct Hp12 as (A & B & C & D & E). rewrite Es2 in A, B, D.
          split; [exact A|]. split; [exact B|]. split; [exact I|]. split; [exact D|exact E].
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
        destruct Hp1 as (A & B & C & D & E). rewrite Es in A, B, D.
        split; [exact A|]. split; [exact B|]. split; [exact I|]. split; [exact D|exact E].
    + apply Hcont; [outinv Hom1 out1; constructor|exact Hk].
    + inversion Hk; subst rk.
      exists le1, m1, out1. split.
      * eapply exec_Sloop_stop1; [exact Hex1|]. destruct v as [[? ?]|]; outinv Hom1 out1; constructor.
      * eapply post_sel; [rewrite Hsel; simpl; symmetry; exact Es|exact Hp1].
  - (* Sbreak *)
    inversion H; subst rr. exists le, m, Out_break. split; [constructor|].
    split; [exact Hrep|]. split; [exact Htm|]. split; [exact I|]. split; [reflexivity|apply Mem.unchanged_on_refl].
  - (* Scontinue *)
    inversion H; subst rr. exists le, m, Out_continue. split; [constructor|].
    split; [exact Hrep|]. split; [exact Htm|]. split; [exact I|]. split; [reflexivity|apply Mem.unchanged_on_refl].
  - (* Sreturn *)
    destruct o as [a|].
    + destruct (xexpr ce ve gv Σ a) as [x|] eqn:Ee; [|discriminate].
      inversion H; subst rr; clear H.
      exists le, m, (Out_return (Some (den (lay β) x, typeof a))). split.
      * apply exec_Sreturn_some. eapply xexpr_sound; eauto. exact (proj1 Hgm).
      * split; [exact Hrep|]. split; [exact Htm|]. split; [split; reflexivity|].
        split; [reflexivity|apply Mem.unchanged_on_refl].
    + inversion H; subst rr. exists le, m, (Out_return None). split; [constructor|].
      split; [exact Hrep|]. split; [exact Htm|]. split; [exact I|]. split; [reflexivity|apply Mem.unchanged_on_refl].
Qed.

(** A successful symbolic run of a whole function is a big-step call. *)
Theorem xfun_top_sound n fd xs regs rr :
  xfun ce gv fns n fd xs regs = Some rr ->
  forall β m, rep β regs m -> gmatch2 ge β gv ->
  exists m' vres,
    ClightBigstep.eval_funcall function_entry2 ge m (Internal fd) (map (den (lay β)) xs) E0 m' vres /\
    rep β (sregs (fst (rsel (lay β) rr))) m' /\
    match (stemps (fst (rsel (lay β) rr)))!1%positive with
    | Some x => vres = den (lay β) x
    | None => vres = Vundef
    end /\
    map rshape (sregs (fst (rsel (lay β) rr))) = map rshape regs /\
    Mem.unchanged_on (fun b o => Mem.valid_block m b /\ ~ foot β (map rshape regs) b o) m m'.
Proof.
  intros H β m Hrep Hgm.
  destruct (xfun_sound _ (xstmt_sound n) fd xs regs (PTree.empty sx) (Some 1%positive) rr H β m Hrep Hgm)
    as (m3 & vres & Heval & Hrep3 & (v & Hts & Hvr) & Hon & Hsh & Hun).
  exists m3, vres. split; [exact Heval|]. split; [exact Hrep3|]. split.
  - rewrite Hts. destruct v as [x|]; unfold set_opt.
    + rewrite PTree.gss. exact Hvr.
    + rewrite PTree.grs. exact Hvr.
  - split; [exact Hsh|exact Hun].
Qed.
End SOUND.

Lemma flookup_In fns id fd : flookup fns id = Some fd -> In (id, fd) fns.
Proof.
  induction fns as [|[i f] t IH]; simpl; [discriminate|].
  destruct (Pos.eqb i id) eqn:E.
  - apply Pos.eqb_eq in E. intros H; inversion H; subst. left; reflexivity.
  - intros H. right. exact (IH H).
Qed.
