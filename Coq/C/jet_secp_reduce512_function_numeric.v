(** Original helper call, including function entry, all local allocations and frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar.
Require Import C.jet_secp_scalar_reduce512_run C.jet_secp_reduce512_typed_stage
  C.jet_secp_reduce512_two_stages C.jet_secp_reduce512_final_stage
  C.jet_secp_reduce512_final_atomic C.jet_secp_reduce512_body_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition reduce512_numeric_owned_regs rho :=
  [mkreg (u64_cells 0 (reduce512_final_limbs (reduce512_body_digits rho) (reduce512_body_carry rho))) true (Some 32)] ++
    tl scalar_reduce512_initial_regs.
Lemma reduce512_function_ok : fn_okb f_secp256k1_scalar_reduce_512 = true.
Proof. Timeout 10 reflexivity. Qed.
Lemma reduce512_numeric_body_shape rho :
  map rshape (sregs (reduce512_final_state (reduce512_body_digits rho) (reduce512_body_carry rho))) =
    map rshape (sregs reduce512_first_initial).
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma reduce512_numeric_owned_prefix rho :
  firstn 2 (sregs (reduce512_final_state (reduce512_body_digits rho) (reduce512_body_carry rho))) =
    reduce512_numeric_owned_regs rho.
Proof. rewrite final_state_output_exact; reflexivity. Qed.
Local Opaque reduce512_allocated reduce512_final_state reduce512_final_limbs
  reduce512_body_digits reduce512_body_carry.
Theorem eval_reduce512_numeric_owned rho beta m :
  rep rho beta scalar_reduce512_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_reduce_512)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0)); Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))]
      E0 mf Vundef /\
    rep rho beta (reduce512_numeric_owned_regs rho) mf /\
    final_output_value (reduce512_body_digits rho) (reduce512_body_carry rho) rho (lay beta) =
      reduce512_input_integer rho mod canonical_group_order /\
    lframe (fun b ofs => ~ foot beta (map rshape scalar_reduce512_initial_regs) b ofs) m mf.
Proof.
  intro Hrep.
  destruct (fn_okb_true _ reduce512_function_ok) as (Hnr1 & Hnr2 & Hdj).
  assert (Hlen : length beta = 2%nat) by (destruct Hrep as (HL & _); exact HL).
  destruct (xalloc_sound secp_ge rho (std_cells (genv_cenv secp_ge))
    (fn_vars f_secp256k1_scalar_reduce_512) 2 (fst reduce512_allocated) (snd reduce512_allocated)
    beta scalar_reduce512_initial_regs m empty_env reduce512_allocated_exact Hrep Hlen Hnr1)
    as (e' & m1 & betaN & Hav & Hrep1 & HlenN & He' & Hidx & Hinj & Hnv & Hun1).
  set (beta' := beta ++ betaN) in *.
  assert (Hlay : forall r, (r < 2)%nat -> lay beta' r = lay beta r).
  { intros r Hr; apply lay_app_l; lia. }
  assert (Hargs : map (den rho (lay beta')) [XP 0 0; XP 1 0] =
      map (den rho (lay beta)) [XP 0 0; XP 1 0]).
  { apply map_den_ext with (n := 2%nat); [exact Hlay|reflexivity]. }
  destruct (xbind_sound rho beta' (fn_params f_secp256k1_scalar_reduce_512)
    [XP 0 0; XP 1 0] (PTree.empty sx) reduce512_initial_temps
    (create_undef_temps (fn_temps f_secp256k1_scalar_reduce_512)) reduce512_bound_exact)
    as (le1 & Hbind & Htm0).
  { intros id x Hx; rewrite PTree.gempty in Hx; discriminate. }
  rewrite Hargs in Hbind.
  assert (Hem : ematch beta' (snd reduce512_allocated) e').
  { intros id; split.
    - rewrite He'; destruct (vlookup (snd reduce512_allocated) id) as [[r ty]|]; [reflexivity|apply PTree.gempty].
    - intros r ty V; exact (proj1 (proj2 (proj2 (Hidx id r ty V)))). }
  destruct (exec_reduce512_body_numeric rho beta' e' le1 m1 Hrep1 Htm0 Hem)
    as (le2 & m2 & Hexb & Hrepb & Hloads & Hnumeric & Htmb & Hunb).
  pose proof (reduce512_numeric_body_shape rho) as Hshb.
  change (map rshape (sregs (reduce512_final_state (reduce512_body_digits rho) (reduce512_body_carry rho))) =
    map rshape (scalar_reduce512_initial_regs ++ fst reduce512_allocated)) in Hshb.
  set (regsN := fst reduce512_allocated) in *.
  set (regsB := sregs (reduce512_final_state (reduce512_body_digits rho) (reduce512_body_carry rho))) in *.
  assert (Hlenb : length beta' = length (scalar_reduce512_initial_regs ++ regsN)).
  { unfold beta'; rewrite !app_length,Hlen,HlenN; reflexivity. }
  assert (Hnrb : forall id1 id2 r1 r2 ty1 ty2,
    vlookup (snd reduce512_allocated) id1 = Some (r1,ty1) ->
    vlookup (snd reduce512_allocated) id2 = Some (r2,ty2) ->
    blk beta' r1 = blk beta' r2 -> r1 = r2).
  { intros id1 id2 r1 r2 ty1 ty2 V1 V2 Eblk; destruct (Nat.eq_dec r1 r2) as [Hsame|Hne]; [exact Hsame|exfalso].
    destruct (Hidx id1 r1 ty1 V1) as (_ & _ & _ & reg1 & Hreg1 & Hfree1).
    destruct (Hidx id2 r2 ty2 V2) as (_ & _ & _ & reg2 & Hreg2 & Hfree2).
    destruct (shape_nth _ _ r1 reg1 Hshb Hreg1) as (regb1 & Hregb1 & Hsh1).
    destruct (shape_nth _ _ r2 reg2 Hshb Hreg2) as (regb2 & Hregb2 & Hsh2).
    destruct Hrepb as (_ & HS & _).
    destruct (HS r1 r2 regb1 regb2 Hne Hregb1 Hregb2) as [Hb|(Hf & _)]; [exact (Hb Eblk)|].
    unfold rshape in Hsh1; inversion Hsh1; congruence. }
  destruct (callee_env_blocks secp_ge beta' (snd reduce512_allocated) e' Hnrb) as (Hblk & Hbnr).
  { intros id; rewrite He'; destruct (vlookup (snd reduce512_allocated) id) as [[r ty]|]; [reflexivity|apply PTree.gempty]. }
  { intros id r ty V; destruct (Hidx id r ty V) as (_ & _ & _ & reg & Hreg & _).
    rewrite Hlenb; apply nth_error_Some; congruence. }
  { exact Hinj. }
  destruct (free_list_exists (blocks_of_env secp_ge e') m2 Hbnr) as (m3 & Hfl & Hun3).
  { intros b lo hi Hin; destruct (Hblk b lo hi Hin) as (id & r & ty & V & -> & -> & ->).
    destruct (Hidx id r ty V) as (_ & _ & _ & reg & Hreg & Hfree).
    destruct (shape_nth _ _ r reg Hshb Hreg) as (regb & Hregb & Hsh).
    destruct Hrepb as (_ & _ & HH); pose proof (HH r regb Hregb) as (_ & _ & _ & _ & Hfr).
    assert (Ef : rfree regb = Some (sizeof (genv_cenv secp_ge) ty)).
    { unfold rshape in Hsh; inversion Hsh; congruence. }
    rewrite Ef in Hfr; exact (proj1 (proj2 (proj2 Hfr))). }
  assert (HNinv : forall b, In b (map fst betaN) -> ~ Mem.valid_block m b).
  { intros b Hin; apply in_map_iff in Hin; destruct Hin as (p & <- & Hp).
    exact (proj1 (Forall_forall _ _) Hnv p Hp). }
  assert (HinN : forall b, In b (map (fun x => fst (fst x)) (blocks_of_env secp_ge e')) ->
    In b (map fst betaN)).
  { intros b Hin; apply in_map_iff in Hin; destruct Hin as ([[b' lo] hi] & Eq & Hin); cbn [fst] in Eq; subst b'.
    destruct (Hblk b lo hi Hin) as (id & r & ty & V & -> & _).
    destruct (Hidx id r ty V) as (_ & Hge & _ & reg & Hreg & _).
    assert (Hr : (r < length beta')%nat) by (rewrite Hlenb; apply nth_error_Some; congruence).
    unfold blk,lay,beta'; rewrite app_nth2 by lia; apply in_map; apply nth_In.
    unfold beta' in Hr; rewrite app_length in Hr; lia. }
  assert (HbetaN : forall b, In b (map fst beta) -> ~ In b (map fst betaN)).
  { intros b H1 H2; apply (HNinv b H2).
    apply in_map_iff in H1; destruct H1 as (p & <- & Hp).
    destruct (In_nth _ _ (1%positive,0) Hp) as (r & Hr & Hnth).
    destruct (nth_error scalar_reduce512_initial_regs r) as [reg|] eqn:E.
    2: { apply nth_error_None in E; change (r >= 2)%nat in E.
         change (r < length beta)%nat in Hr; exfalso; clear - Hr E Hlen; lia. }
    destruct Hrep as (_ & _ & HR); destruct (HR r reg E) as (_ & Hv & _).
    unfold blk,lay in Hv; replace (nth r beta (1%positive,0)) with p in Hv by (symmetry; exact Hnth); exact Hv. }
  assert (Hlenb2 : length regsB = length (scalar_reduce512_initial_regs ++ regsN)).
  { rewrite <- (map_length rshape regsB),Hshb,map_length; reflexivity. }
  assert (Hrep3 : rep rho beta (firstn 2 regsB) m3).
  { eapply rep_mem with (m := m2).
    - eapply Mem.unchanged_on_implies; [exact Hun3|].
      intros b ofs Hb _ Hin; exact (HbetaN b Hb (HinN b Hin)).
    - eapply rep_prefix with (βN := betaN) (regsN := skipn 2 regsB).
      + rewrite firstn_skipn; exact Hrepb.
      + rewrite firstn_length,Hlenb2,app_length.
        change (length beta = Nat.min 2 (2 + length regsN)).
        rewrite Nat.min_l by lia; exact Hlen. }
  assert (Hcall : Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_reduce_512)
      (map (den rho (lay beta)) [XP 0 0; XP 1 0]) E0 m3 Vundef).
  { eapply eval_funcall_internal.
    - constructor; [exact Hnr1|exact Hnr2|exact Hdj|exact Hav|exact Hbind].
    - exact Hexb.
    - constructor.
    - exact Hfl. }
  change (map (den rho (lay beta)) [XP 0 0; XP 1 0]) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0 + 0)); Vptr (blk beta 1) (Ptrofs.repr (bas beta 1 + 0))] in Hcall.
  rewrite !Z.add_0_r in Hcall.
  exists m3; split; [exact Hcall|].
  split; [unfold regsB in Hrep3; rewrite reduce512_numeric_owned_prefix in Hrep3; exact Hrep3|].
  split; [apply reduce512_body_numeric|].
  eapply lframe_implies with (P := fun b ofs => Mem.valid_block m b /\
    ~ foot beta (map rshape scalar_reduce512_initial_regs) b ofs).
  2: { intros b ofs Hf Hv; split; assumption. }
  eapply lframe_trans.
  { apply lframe_unchanged; eapply Mem.unchanged_on_implies; [exact Hun1|]; intros; exact I. }
  eapply lframe_trans.
  { eapply lframe_implies; [exact Hunb|].
    intros b ofs (Hv & Hf) Hv1.
    intros (r & s & d & ch & Hs & Hin & Eb' & Hr).
    destruct (lt_dec r 2) as [Hlt|Hge].
    - apply Hf; exists r,s,d,ch.
      cbn [reduce512_first_initial sregs] in Hs.
      rewrite map_app,nth_error_app1 in Hs by (rewrite map_length; exact Hlt).
      unfold blk,bas in *; rewrite Hlay in Eb',Hr by exact Hlt; auto.
    - apply (HNinv b); [|exact Hv].
      subst b; assert (r < length beta')%nat.
      { rewrite Hlenb; rewrite <- (map_length rshape).
        change (nth_error (map rshape (scalar_reduce512_initial_regs ++ regsN)) r = Some s) in Hs.
        apply nth_error_Some; congruence. }
      unfold blk,lay,beta'; rewrite app_nth2 by lia; apply in_map; apply nth_In.
      unfold beta' in H; rewrite app_length in H; lia. }
  apply lframe_unchanged; eapply Mem.unchanged_on_implies; [exact Hun3|].
  intros b ofs (Hv & Hf) Hv2 Hin; exact (HNinv b (HinN b Hin) Hv).
Qed.
Theorem eval_reduce512_numeric_owned_loads rho beta m :
  rep rho beta scalar_reduce512_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_reduce_512)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0)); Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))]
      E0 mf Vundef /\
    (forall i sy, nth_error (reduce512_final_limbs (reduce512_body_digits rho) (reduce512_body_carry rho)) i = Some sy ->
      Mem.load Mint64 mf (blk beta 0) (bas beta 0 + 8 * Z.of_nat i) = Some (den rho (lay beta) sy)) /\
    rep rho beta (reduce512_numeric_owned_regs rho) mf /\
    final_output_value (reduce512_body_digits rho) (reduce512_body_carry rho) rho (lay beta) =
      reduce512_input_integer rho mod canonical_group_order /\
    lframe (fun b ofs => ~ foot beta (map rshape scalar_reduce512_initial_regs) b ofs) m mf.
Proof.
  intro HR; destruct (eval_reduce512_numeric_owned rho beta m HR) as (mf & Hcall & Hrep & Hvalue & Hframe).
  pose proof (rep_region rho beta _ mf 0 _ Hrep eq_refl) as Hregion.
  exists mf; split; [exact Hcall|]. split.
  - intros i sy HX; pose proof (u64_cells_nth _ 0 i sy HX) as Hcell; rewrite Z.add_0_l in Hcell.
    exact (region_load rho beta mf 0 _ (8 * Z.of_nat i) Mint64 sy Hregion Hcell).
  - exact (conj Hrep (conj Hvalue Hframe)).
Qed.
