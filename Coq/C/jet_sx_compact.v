(** Sharing-free execution of no-op conditionals.  Conditions are still
    evaluated and converted to C booleans; no generated AST is changed.
    General loops/calls and other statements reuse the existing executor. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_exec C.jet_sx_pure.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition both_skip (a b : statement) : bool :=
  match a,b with Sskip,Sskip => true | _,_ => false end.
Lemma both_skip_true a b : both_skip a b = true -> a = Sskip /\ b = Sskip.
Proof. destruct a,b; cbn [both_skip]; intuition discriminate. Qed.
Definition break_stmt (s : statement) : bool :=
  match s with Sbreak => true | _ => false end.
Lemma break_stmt_true s : break_stmt s = true -> s = Sbreak.
Proof. destruct s; cbn [break_stmt]; congruence. Qed.

Section COMPUTE.
Variable ce : composite_env.
Variable gv : venv.
Variable fns : list (ident * fentry).
Variable n : nat.
Fixpoint compact_stmt (ve : venv) (st : sstate) (s : statement) {struct s} : option res :=
  match s with
  | Ssequence a b =>
      match compact_stmt ve st a with
      | Some r => tbind r (fun st' o =>
          match o with ONormal => compact_stmt ve st' b | _ => Some (RDone st' o) end)
      | None => None end
  | Sifthenelse a b c =>
      if both_skip b c then
        match xexpr ce ve gv st a with
        | Some x => match xbool x (typeof a) with
                    | Some _ => Some (RDone st ONormal) | None => None end
        | None => None end
      else xstmt ce gv fns n ve st s
  | Sloop a b =>
      if break_stmt b then
        match compact_stmt ve st a with
        | Some r => tbind r (fun st' o =>
            match o with OReturn v => Some (RDone st' (OReturn v))
                       | _ => Some (RDone st' ONormal) end)
        | None => None end
      else xstmt ce gv fns n ve st s
  | _ => xstmt ce gv fns n ve st s
  end.

Lemma compact_stmt_lext s : forall ve st r,
  compact_stmt ve st s = Some r -> forall rho beta, lext rho beta (slog st) r.
Proof.
  induction s; intros ve st rr H rho beta; cbn [compact_stmt] in H;
    try solve [eapply xstmt_lext; exact H].
  - destruct (compact_stmt ve st s1) as [r1|] eqn:E1; [|discriminate].
    destruct (tbind_sel rho beta _ _ _ H) as (rk & Hk & Hsel).
    pose proof (IHs1 _ _ _ E1 rho beta) as H1.
    eapply lext_sel; [exact Hsel|].
    destruct (rsel rho beta r1) as [st1 o1] eqn:Es; simpl in Hk.
    assert (H1' : forall o, lext rho beta (slog st) (RDone st1 o)).
    { intro o; unfold lext in *; simpl; rewrite Es in H1; exact H1. }
    destruct o1; try (inversion Hk; subst rk; apply H1').
    eapply lext_trans; [exact H1|]. rewrite Es; simpl. exact (IHs2 _ _ _ Hk rho beta).
  - destruct (both_skip s1 s2) eqn:B; [|eapply xstmt_lext; exact H].
    destruct (xexpr ce ve gv st e) as [x|]; [|discriminate].
    destruct (xbool x (typeof e)); [|discriminate].
    inversion H; subst rr. apply lext_refl.
  - destruct (break_stmt s2) eqn:B; [|eapply xstmt_lext; exact H].
    destruct (compact_stmt ve st s1) as [r1|] eqn:E1; [|discriminate].
    destruct (tbind_sel rho beta _ _ _ H) as (rk & Hk & Hsel).
    pose proof (IHs1 _ _ _ E1 rho beta) as H1.
    eapply lext_sel; [exact Hsel|].
    destruct (rsel rho beta r1) as [st1 o1] eqn:Es; simpl in Hk.
    destruct o1; inversion Hk; subst rk; unfold lext in *; simpl;
      rewrite Es in H1; exact H1.
Qed.
End COMPUTE.

Section SOUND.
Variable ge : genv.
Variable gv : venv.
Variable fns : list (ident * fentry).
Variable ev_ok : (nat -> int64) -> event -> Prop.
Variable inv : (nat -> int64) -> list event -> mem -> Prop.
Variable ext : block -> Prop.
Hypothesis Hinv_stable : forall rho log m m',
  inv rho log m -> lframe (fun b _ => ext b) m m' -> inv rho log m'.
Hypothesis Hext_valid : forall rho log m b, inv rho log m -> ext b -> Mem.valid_block m b.
Hypothesis Hfns : forall id ent, flookup fns id = Some ent ->
  (exists b, Genv.find_symbol ge id = Some b /\
    Genv.find_funct_ptr ge b = Some (Internal (fentry_fd ent))) /\
  match ent with FInt _ => True | FOra fd o => oracle_ok ge ev_ok inv ext fd o end.
Notation ce := (genv_cenv ge).
Notation exec := (ClightBigstep.exec_stmt function_entry2 ge).
Local Ltac compact_outinv Hom out :=
  destruct out as [| | |[[? ?]|]]; simpl in Hom; try contradiction.

Theorem compact_stmt_sound n : sound_rec ge gv ev_ok inv ext (compact_stmt ce gv fns n).
Proof.
  intros ve st s; revert ve st.
  induction s; intros ve st rr H rho beta env0 le m Hrep Htm Hem Hgm Hsep Hinv Hsol;
    cbn [compact_stmt] in H;
    try solve [eapply (xstmt_sound ge gv fns ev_ok inv ext Hinv_stable Hext_valid Hfns n); eauto].
  - destruct (compact_stmt ce gv fns n ve st s1) as [r1|] eqn:E1; [|discriminate].
    destruct (tbind_sel rho (lay beta) _ _ _ H) as (rk & Hk & Hsel).
    rewrite Hsel in Hsol.
    assert (Hsol1 : solves ev_ok rho (slog (fst (rsel rho (lay beta) r1)))).
    { destruct (rsel rho (lay beta) r1) as [st1 o1]; simpl in *.
      destruct o1; try (inversion Hk; subst rk; exact Hsol).
      destruct (compact_stmt_lext ce gv fns n s2 _ _ _ Hk rho (lay beta)) as [suf Hs].
      simpl in Hs. rewrite Hs in Hsol. exact (proj1 (solves_app _ _ _ _ Hsol)). }
    destruct (IHs1 _ _ _ E1 rho beta env0 le m Hrep Htm Hem Hgm Hsep Hinv Hsol1)
      as (le1 & m1 & out1 & Hex1 & Hp1).
    pose proof Hp1 as (Hrep1 & Htm1 & Hom1 & Hsh1 & Hinv1 & Hun1).
    destruct (rsel rho (lay beta) r1) as [st1 o1] eqn:Es.
    simpl in Hk, Hrep1, Htm1, Hom1, Hsh1, Hinv1.
    destruct o1.
    + compact_outinv Hom1 out1.
      destruct (IHs2 _ _ _ Hk rho beta env0 le1 m1 Hrep1 Htm1 Hem Hgm Hsep Hinv1 Hsol)
        as (le2 & m2 & out2 & Hex2 & Hp2).
      exists le2,m2,out2; split.
      * change E0 with (E0 ** E0). eapply exec_Sseq_1; eauto.
      * eapply post_sel; [exact Hsel|]. eapply post_trans; [exact Hp1|]. rewrite Es; exact Hp2.
    + inversion Hk; subst rk. exists le1,m1,out1; split.
      * eapply exec_Sseq_2; [exact Hex1|]. compact_outinv Hom1 out1; discriminate.
      * eapply post_sel; [rewrite Hsel; simpl; symmetry; exact Es|exact Hp1].
    + inversion Hk; subst rk. exists le1,m1,out1; split.
      * eapply exec_Sseq_2; [exact Hex1|]. compact_outinv Hom1 out1; discriminate.
      * eapply post_sel; [rewrite Hsel; simpl; symmetry; exact Es|exact Hp1].
    + inversion Hk; subst rk. exists le1,m1,out1; split.
      * eapply exec_Sseq_2; [exact Hex1|]. destruct v as [[? ?]|]; compact_outinv Hom1 out1; discriminate.
      * eapply post_sel; [rewrite Hsel; simpl; symmetry; exact Es|exact Hp1].
  - destruct (both_skip s1 s2) eqn:B.
    2: { eapply (xstmt_sound ge gv fns ev_ok inv ext Hinv_stable Hext_valid Hfns n); eauto. }
    apply both_skip_true in B; destruct B as [-> ->].
    destruct (xexpr ce ve gv st e) as [x|] eqn:Ea; [|discriminate].
    destruct (xbool x (typeof e)) as [c|] eqn:Eb; [|discriminate].
    inversion H; subst rr; clear H.
    exists le,m,Out_normal; split.
    + eapply exec_Sifthenelse.
      * eapply xexpr_sound; eauto. exact (proj1 Hgm).
      * apply xbool_sound; exact Eb.
      * destruct (truth rho (lay beta) c); constructor.
    + split; [exact Hrep|]. split; [exact Htm|]. split; [exact I|].
      split; [reflexivity|]. split; [exact Hinv|apply lframe_refl].
  - destruct (break_stmt s2) eqn:B.
    2: { eapply (xstmt_sound ge gv fns ev_ok inv ext Hinv_stable Hext_valid Hfns n); eauto. }
    apply break_stmt_true in B; subst s2.
    destruct (compact_stmt ce gv fns n ve st s1) as [r1|] eqn:E1; [|discriminate].
    destruct (tbind_sel rho (lay beta) _ _ _ H) as (rk & Hk & Hsel).
    rewrite Hsel in Hsol.
    assert (Hsol1 : solves ev_ok rho (slog (fst (rsel rho (lay beta) r1)))).
    { destruct (rsel rho (lay beta) r1) as [st1 o1]; simpl in *;
        destruct o1; inversion Hk; subst rk; exact Hsol. }
    destruct (IHs1 _ _ _ E1 rho beta env0 le m Hrep Htm Hem Hgm Hsep Hinv Hsol1)
      as (le1 & m1 & out1 & Hex1 & Hp1).
    pose proof Hp1 as (A & B0 & C & D & E & G).
    destruct (rsel rho (lay beta) r1) as [st1 o1] eqn:Es.
    simpl in Hk,C. destruct o1; inversion Hk; subst rk.
    + compact_outinv C out1. exists le1,m1,Out_normal; split.
      * change E0 with (E0 ** E0). eapply exec_Sloop_stop2; [exact Hex1|constructor|constructor|constructor].
      * eapply post_sel; [rewrite Hsel; reflexivity|].
        split; [exact A|]. split; [exact B0|]. split; [exact I|]. split; [exact D|]. split; assumption.
    + compact_outinv C out1. exists le1,m1,Out_normal; split.
      * eapply exec_Sloop_stop1; [exact Hex1|constructor].
      * eapply post_sel; [rewrite Hsel; reflexivity|].
        split; [exact A|]. split; [exact B0|]. split; [exact I|]. split; [exact D|]. split; assumption.
    + compact_outinv C out1. exists le1,m1,Out_normal; split.
      * change E0 with (E0 ** E0). eapply exec_Sloop_stop2; [exact Hex1|constructor|constructor|constructor].
      * eapply post_sel; [rewrite Hsel; reflexivity|].
        split; [exact A|]. split; [exact B0|]. split; [exact I|]. split; [exact D|]. split; assumption.
    + exists le1,m1,out1; split.
      * eapply exec_Sloop_stop1; [exact Hex1|]. destruct v as [[? ?]|]; compact_outinv C out1; constructor.
      * eapply post_sel; [rewrite Hsel; simpl; symmetry; exact Es|exact Hp1].
Qed.
End SOUND.

Definition compact_fun ce gv fns n fd xs regs log nv : option res :=
  xfun_with ce (compact_stmt ce gv fns n) fd xs regs log nv
    (xcall_ret (Some 1%positive) (PTree.empty sx) (length regs) (fn_return fd)).

Theorem compact_fun_pure (ge : genv) (l : list (ident * function))
  (Hl : forall id f, In (id,f) l -> exists b,
    Genv.find_symbol ge id = Some b /\ Genv.find_funct_ptr ge b = Some (Internal f))
  n fd xs regs nv rr :
  compact_fun (genv_cenv ge) [] (int_table l) n fd xs regs [] nv = Some rr ->
  leaves_log_nil rr = true ->
  forall rho beta m, rep rho beta regs m ->
  exists mf vres,
    Clight2.eval_funcall ge m (Internal fd) (map (den rho (lay beta)) xs) E0 mf vres /\
    rep rho beta (sregs (fst (rsel rho (lay beta) rr))) mf /\
    match (stemps (fst (rsel rho (lay beta) rr)))!1%positive with
    | Some x => vres = den rho (lay beta) x | None => vres = Vundef end /\
    map rshape (sregs (fst (rsel rho (lay beta) rr))) = map rshape regs /\
    lframe (fun b ofs => ~ foot beta (map rshape regs) b ofs) m mf.
Proof.
  intros H Hnil rho beta m Hrep.
  assert (Hstable : forall (rho : nat -> int64) (log : list event) (m m' : mem),
    True -> lframe (fun (_ : block) (_ : Z) => False) m m' -> True) by auto.
  assert (Hvalid : forall (rho : nat -> int64) (log : list event) (m : mem) b,
    True -> False -> Mem.valid_block m b) by contradiction.
  assert (HF : forall id ent, flookup (int_table l) id = Some ent ->
    (exists b, Genv.find_symbol ge id = Some b /\
      Genv.find_funct_ptr ge b = Some (Internal (fentry_fd ent))) /\
    match ent with FInt _ => True
      | FOra fd o => oracle_ok ge (fun _ _ => True) (fun _ _ _ => True) (fun _ => False) fd o end).
  { intros id ent Hlk. destruct (int_table_lookup _ _ _ Hlk) as (f & -> & Hin).
    split; [exact (Hl id f Hin)|exact I]. }
  destruct (xfun_sound ge [] (fun _ _ => True) (fun _ _ _ => True) (fun _ => False)
    Hstable Hvalid _
    (compact_stmt_sound ge [] (int_table l) (fun _ _ => True) (fun _ _ _ => True)
      (fun _ => False) Hstable Hvalid HF n)
    fd xs regs [] nv (PTree.empty sx) (Some 1%positive) rr H rho beta m Hrep)
    as (mf & vres & Hcall & Hfinal & (v & Htemps & Hv) & Hnormal & Hshape & Hinv & Hframe).
  - split; intros id r ty V; discriminate.
  - intros r Hr [] .
  - exact I.
  - rewrite (leaves_log_nil_sel _ _ _ Hnil); constructor.
  - exists mf,vres; split; [exact Hcall|]. split; [exact Hfinal|]. split.
    + rewrite Htemps. destruct v as [x|]; unfold set_opt.
      * rewrite PTree.gss; exact Hv.
      * rewrite PTree.grs; exact Hv.
    + split; [exact Hshape|]. eapply lframe_implies; [exact Hframe|].
      intros b ofs Hf Hvblock; split; [exact Hvblock|]. split; [exact Hf|tauto].
Qed.
