(** Actual allocation/entry/freeing around a proved normal void body, with
    internal preconditions and a faithfully revalued final word state. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Globalenvs Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem owned_void_call_state (ge : genv) fd xs regs regsN veN ts0
  (pre : (nat -> int64) -> Prop) (final_rho : (nat -> int64) -> nat -> int64)
  (final_regs : (nat -> int64) -> list region) :
  fn_okb fd = true -> fn_return fd = Tvoid ->
  forallb (xp_lt (length regs)) xs = true ->
  xalloc (std_cells (genv_cenv ge)) (genv_cenv ge) (fn_vars fd) (length regs) = Some (regsN, veN) ->
  xbind (fn_params fd) xs (PTree.empty sx) = Some ts0 ->
  (forall rho, map rshape (final_regs rho) = map rshape (regs ++ regsN)) ->
  (forall rho beta e le m, pre rho ->
    rep rho beta (regs ++ regsN) m -> tmatch rho beta ts0 le -> ematch beta veN e ->
    exists le' mf,
      Clight2.exec_stmt ge e le m (fn_body fd) E0 le' mf Out_normal /\
      rep (final_rho rho) beta (final_regs rho) mf /\
      lframe (fun b ofs => ~ foot beta (map rshape (regs ++ regsN)) b ofs) m mf) ->
  forall rho beta m, pre rho -> rep rho beta regs m ->
  exists mf,
    Clight2.eval_funcall ge m (Internal fd) (map (den rho (lay beta)) xs) E0 mf Vundef /\
    rep (final_rho rho) beta (firstn (length regs) (final_regs rho)) mf /\
    lframe (fun b ofs => ~ foot beta (map rshape regs) b ofs) m mf.
Proof.
  intros Fok Rvoid Fa Eal Ebd Hshape Hbody rho beta m Hpre Hrep.
  destruct (fn_okb_true fd Fok) as (Hnr1 & Hnr2 & Hdj).
  assert (Hlen : length beta = length regs) by (destruct Hrep as (HH & _); exact HH).
  destruct (xalloc_sound ge rho (std_cells (genv_cenv ge)) (fn_vars fd) (length regs) regsN veN beta regs m empty_env Eal Hrep Hlen Hnr1)
    as (e' & m1 & betaN & Hav & Hrep1 & HlenN & He' & Hidx & Hinj & Hnv & Hun1).
  set (beta' := beta ++ betaN) in *.
  assert (Hlay : forall r, (r < length regs)%nat -> lay beta' r = lay beta r).
  { intros r Hr; apply lay_app_l; lia. }
  assert (Hargs : map (den rho (lay beta')) xs = map (den rho (lay beta)) xs).
  { apply map_den_ext with (n := length regs); [exact Hlay|exact Fa]. }
  destruct (xbind_sound rho beta' (fn_params fd) xs (PTree.empty sx) ts0
    (create_undef_temps (fn_temps fd)) Ebd) as (le1 & Hbind & Htm0).
  { intros id x Hx; rewrite PTree.gempty in Hx; discriminate. }
  rewrite Hargs in Hbind.
  assert (Hem : ematch beta' veN e').
  { intros id; split.
    - rewrite He'; destruct (vlookup veN id) as [[r ty]|]; [reflexivity|apply PTree.gempty].
    - intros r ty V; exact (proj1 (proj2 (proj2 (Hidx id r ty V)))). }
  assert (HNinv : forall b, In b (map fst betaN) -> ~ Mem.valid_block m b).
  { intros b Hin; apply in_map_iff in Hin; destruct Hin as (p & <- & Hp).
    exact (proj1 (Forall_forall _ _) Hnv p Hp). }
  destruct (Hbody rho beta' e' le1 m1 Hpre Hrep1 Htm0 Hem) as (le2 & m2 & Hexb & Hrepb & HFb).
  pose proof (Hshape rho) as Hshb.
  assert (Hlenb : length beta' = length (regs ++ regsN)).
  { unfold beta'; rewrite !app_length; lia. }
  assert (Hnrb : forall id1 id2 r1 r2 ty1 ty2, vlookup veN id1 = Some (r1, ty1) -> vlookup veN id2 = Some (r2, ty2) ->
    blk beta' r1 = blk beta' r2 -> r1 = r2).
  { intros id1 id2 r1 r2 ty1 ty2 V1 V2 Eblk; destruct (Nat.eq_dec r1 r2) as [|Hne]; [assumption|exfalso].
    destruct (Hidx id1 r1 ty1 V1) as (_ & _ & _ & reg1 & Hreg1 & Hfree1).
    destruct (Hidx id2 r2 ty2 V2) as (_ & _ & _ & reg2 & Hreg2 & Hfree2).
    destruct (shape_nth _ _ r1 reg1 Hshb Hreg1) as (regb1 & Hregb1 & Hsh1).
    destruct (shape_nth _ _ r2 reg2 Hshb Hreg2) as (regb2 & Hregb2 & Hsh2).
    destruct Hrepb as (_ & HS & _).
    destruct (HS r1 r2 regb1 regb2 Hne Hregb1 Hregb2) as [Hb|(Hf & _)]; [exact (Hb Eblk)|].
    unfold rshape in Hsh1; inversion Hsh1; congruence. }
  destruct (callee_env_blocks ge beta' veN e' Hnrb) as (Hblk & Hbnr).
  { intros id; rewrite He'; destruct (vlookup veN id) as [[r ty]|]; [reflexivity|apply PTree.gempty]. }
  { intros id r ty V; destruct (Hidx id r ty V) as (_ & _ & _ & reg & Hreg & _).
    rewrite Hlenb; apply nth_error_Some; congruence. }
  { exact Hinj. }
  destruct (free_list_exists (blocks_of_env ge e') m2 Hbnr) as (m3 & Hfl & Hun3).
  { intros b lo hi Hin; destruct (Hblk b lo hi Hin) as (id & r & ty & V & -> & -> & ->).
    destruct (Hidx id r ty V) as (_ & _ & _ & reg & Hreg & Hfree).
    destruct (shape_nth _ _ r reg Hshb Hreg) as (regb & Hregb & Hsh).
    destruct Hrepb as (_ & _ & HH); pose proof (HH r regb Hregb) as (_ & _ & _ & _ & Hfr).
    assert (Ef : rfree regb = Some (sizeof (genv_cenv ge) ty)).
    { unfold rshape in Hsh; inversion Hsh; congruence. }
    rewrite Ef in Hfr; exact (proj1 (proj2 (proj2 Hfr))). }
  assert (HinN : forall b, In b (map (fun x => fst (fst x)) (blocks_of_env ge e')) -> In b (map fst betaN)).
  { intros b Hin; apply in_map_iff in Hin; destruct Hin as ([[b' lo] hi] & Eq & Hin); simpl in Eq; subst b'.
    destruct (Hblk b lo hi Hin) as (id & r & ty & V & -> & _).
    destruct (Hidx id r ty V) as (_ & Hge & _ & reg & Hreg & _).
    assert (Hr : (r < length beta')%nat) by (rewrite Hlenb; apply nth_error_Some; congruence).
    unfold blk, lay, beta'; rewrite app_nth2 by lia; apply in_map; apply nth_In.
    unfold beta' in Hr; rewrite app_length in Hr; lia. }
  assert (HbetaN : forall b, In b (map fst beta) -> ~ In b (map fst betaN)).
  { intros b H1 H2; apply (HNinv b H2).
    apply in_map_iff in H1; destruct H1 as (p & <- & Hp).
    destruct (In_nth _ _ (1%positive, 0) Hp) as (r & Hr & Hnth).
    destruct (nth_error regs r) as [reg|] eqn:E.
    2: { apply nth_error_None in E; assert (r < length regs)%nat by (rewrite <- Hlen; exact Hr); lia. }
    destruct Hrep as (_ & _ & HR); destruct (HR r reg E) as (_ & Hv & _).
    unfold blk, lay in Hv; replace (nth r beta (1%positive, 0)) with p in Hv by (symmetry; exact Hnth); exact Hv. }
  assert (Hlenb2 : length (final_regs rho) = length (regs ++ regsN)).
  { rewrite <- (map_length rshape (final_regs rho)), Hshb, map_length; reflexivity. }
  assert (Hrep3 : rep (final_rho rho) beta (firstn (length regs) (final_regs rho)) m3).
  { eapply rep_mem with (m := m2).
    - eapply Mem.unchanged_on_implies; [exact Hun3|]; intros b ofs Hb _ Hin.
      exact (HbetaN b Hb (HinN b Hin)).
    - eapply rep_prefix with (βN := betaN) (regsN := skipn (length regs) (final_regs rho)).
      + rewrite firstn_skipn; exact Hrepb.
      + rewrite firstn_length, Hlenb2, app_length; lia. }
  exists m3; split.
  - eapply eval_funcall_internal.
    + constructor; [exact Hnr1|exact Hnr2|exact Hdj|exact Hav|exact Hbind].
    + exact Hexb.
    + rewrite Rvoid; reflexivity.
    + exact Hfl.
  - split; [exact Hrep3|].
    assert (HF : lframe (fun b ofs => Mem.valid_block m b /\ ~ foot beta (map rshape regs) b ofs) m m3).
    { eapply lframe_trans.
      { apply lframe_unchanged; eapply Mem.unchanged_on_implies; [exact Hun1|]; intros; exact I. }
      eapply lframe_trans.
      { eapply lframe_implies; [exact HFb|]; intros b ofs (Hv & Hf) Hv1.
        intros (r & sh & d & ch & Hs & Hin & Eb & Hr).
        destruct (lt_dec r (length regs)) as [Hlt|Hge].
        - apply Hf; exists r, sh, d, ch.
          rewrite map_app, nth_error_app1 in Hs by (rewrite map_length; exact Hlt).
          unfold blk, bas in *; rewrite Hlay in Eb, Hr by exact Hlt; auto.
        - apply (HNinv b); [|exact Hv]; subst b.
          assert (r < length beta')%nat by (rewrite Hlenb; rewrite <- (map_length rshape); apply nth_error_Some; congruence).
          unfold blk, lay, beta'; rewrite app_nth2 by lia; apply in_map; apply nth_In.
          unfold beta' in H; rewrite app_length in H; lia. }
      apply lframe_unchanged; eapply Mem.unchanged_on_implies; [exact Hun3|].
      intros b ofs (Hv & _) _ Hin; exact (HNinv b (HinN b Hin) Hv). }
    eapply lframe_implies; [exact HF|]; intros b ofs Houtside Hvalid; split; assumption.
Qed.

(** Original interface retained as the identity-state, unconditional case. *)
Theorem owned_void_call (ge : genv) fd xs regs regsN veN ts0 (final_regs : (nat -> int64) -> list region) :
  fn_okb fd = true -> fn_return fd = Tvoid ->
  forallb (xp_lt (length regs)) xs = true ->
  xalloc (std_cells (genv_cenv ge)) (genv_cenv ge) (fn_vars fd) (length regs) = Some (regsN, veN) ->
  xbind (fn_params fd) xs (PTree.empty sx) = Some ts0 ->
  (forall rho, map rshape (final_regs rho) = map rshape (regs ++ regsN)) ->
  (forall rho beta e le m,
    rep rho beta (regs ++ regsN) m -> tmatch rho beta ts0 le -> ematch beta veN e ->
    exists le' mf,
      Clight2.exec_stmt ge e le m (fn_body fd) E0 le' mf Out_normal /\
      rep rho beta (final_regs rho) mf /\
      lframe (fun b ofs => ~ foot beta (map rshape (regs ++ regsN)) b ofs) m mf) ->
  forall rho beta m, rep rho beta regs m ->
  exists mf,
    Clight2.eval_funcall ge m (Internal fd) (map (den rho (lay beta)) xs) E0 mf Vundef /\
    rep rho beta (firstn (length regs) (final_regs rho)) mf /\
    lframe (fun b ofs => ~ foot beta (map rshape regs) b ofs) m mf.
Proof.
  intros Fok Rvoid Fa Eal Ebd Shape Body rho beta m Rep.
  exact (owned_void_call_state ge fd xs regs regsN veN ts0 (fun _=>True) (fun r=>r)
    final_regs Fok Rvoid Fa Eal Ebd Shape (fun r b e l mm _=>Body r b e l mm) rho beta m I Rep).
Qed.
