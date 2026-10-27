(** Complete original reduce512 call with an uninitialized owned destination.
    Actual entry, local allocations, arithmetic stages and frees are derived.
    The numeric result and frame are the same as the existing in-place call. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep
 C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar
 C.jet_secp_scalar_reduce512_run C.jet_secp_reduce512_typed_stage
 C.jet_secp_reduce512_two_stages C.jet_secp_reduce512_final_stage
 C.jet_secp_reduce512_final_atomic C.jet_secp_reduce512_body_numeric
 C.jet_secp_reduce512_function_numeric C.jet_secp_reduce512_fresh_runs C.jet_secp_reduce512_fresh_body
 C.jet_secp_local_regions C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_mul_writer_bridge C.jet_secp_slice_permissions C.jet_secp_closed_helpers
 C.jet_clight_internal_frame C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque reduce512_allocated reduce512_final_state reduce512_final_limbs
 reduce512_body_digits reduce512_body_carry.
Theorem eval_reduce512_numeric_fresh rho beta m :
  rep rho beta reduce512_fresh_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_reduce_512)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0)); Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))]
      E0 mf Vundef /\
    rep rho beta (reduce512_numeric_owned_regs rho) mf /\
    final_output_value (reduce512_body_digits rho) (reduce512_body_carry rho) rho (lay beta) =
      reduce512_input_integer rho mod canonical_group_order /\
    lframe (fun b ofs => ~ foot beta (map rshape reduce512_fresh_initial_regs) b ofs) m mf.
Proof.
  intro Hrep.
  destruct (fn_okb_true _ reduce512_function_ok) as (Hnr1 & Hnr2 & Hdj).
  assert (Hlen : length beta = 2%nat) by (destruct Hrep as (HL & _); exact HL).
  destruct (xalloc_sound secp_ge rho (std_cells (genv_cenv secp_ge))
    (fn_vars f_secp256k1_scalar_reduce_512) 2 (fst reduce512_allocated) (snd reduce512_allocated)
    beta reduce512_fresh_initial_regs m empty_env reduce512_allocated_exact Hrep Hlen Hnr1)
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
  destruct (exec_reduce512_fresh_body rho beta' e' le1 m1 Hrep1 Htm0 Hem)
    as (le2 & m2 & Hexb & Hrepb & Hloads & Hnumeric & Htmb & Hunb).
  pose proof (reduce512_numeric_body_shape rho) as Hshb.
  change (map rshape (sregs (reduce512_final_state (reduce512_body_digits rho) (reduce512_body_carry rho))) =
    map rshape (reduce512_fresh_initial_regs ++ fst reduce512_allocated)) in Hshb.
  set (regsN := fst reduce512_allocated) in *.
  set (regsB := sregs (reduce512_final_state (reduce512_body_digits rho) (reduce512_body_carry rho))) in *.
  assert (Hlenb : length beta' = length (reduce512_fresh_initial_regs ++ regsN)).
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
    destruct (nth_error reduce512_fresh_initial_regs r) as [reg|] eqn:E.
    2: { apply nth_error_None in E; change (r >= 2)%nat in E.
         change (r < length beta)%nat in Hr; exfalso; clear - Hr E Hlen; lia. }
    destruct Hrep as (_ & _ & HR); destruct (HR r reg E) as (_ & Hv & _).
    unfold blk,lay in Hv; replace (nth r beta (1%positive,0)) with p in Hv by (symmetry; exact Hnth); exact Hv. }
  assert (Hlenb2 : length regsB = length (reduce512_fresh_initial_regs ++ regsN)).
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
    ~ foot beta (map rshape reduce512_fresh_initial_regs) b ofs).
  2: { intros b ofs Hf Hv; split; assumption. }
  eapply lframe_trans.
  { apply lframe_unchanged; eapply Mem.unchanged_on_implies; [exact Hun1|]; intros; exact I. }
  eapply lframe_trans.
  { eapply lframe_implies; [exact Hunb|].
    intros b ofs (Hv & Hf) Hv1.
    intros (r & s & d & ch & Hs & Hin & Eb' & Hr).
    destruct (lt_dec r 2) as [Hlt|Hge].
    - apply Hf; exists r,s,d,ch.
      change (nth_error (map rshape (reduce512_fresh_initial_regs ++ regsN)) r=Some s) in Hs.
      rewrite map_app,nth_error_app1 in Hs by (rewrite map_length; exact Hlt).
      unfold blk,bas in *; rewrite Hlay in Eb',Hr by exact Hlt; auto.
    - apply (HNinv b); [|exact Hv].
      subst b; assert (r < length beta')%nat.
      { rewrite Hlenb; rewrite <- (map_length rshape).
        change (nth_error (map rshape (reduce512_fresh_initial_regs ++ regsN)) r = Some s) in Hs.
        apply nth_error_Some; congruence. }
      unfold blk,lay,beta'; rewrite app_nth2 by lia; apply in_map; apply nth_In.
      unfold beta' in H; rewrite app_length in H; lia. }
  apply lframe_unchanged; eapply Mem.unchanged_on_implies; [exact Hun3|].
  intros b ofs (Hv & Hf) Hv2 Hin; exact (HNinv b (HinN b Hin) Hv).
Qed.

Lemma reduce512_closed : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_scalar_reduce_512)=true.
Proof. timeout 10 (vm_compute;reflexivity). Qed.

Theorem eval_reduce512_fresh_storage rho br bl m :
 rep rho [(br,0);(bl,0)] reduce512_fresh_initial_regs m ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_reduce_512)
 [Vptr br Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf br 0 (map Int64.repr (scalar_limbs_of (reduce512_input_integer rho mod canonical_group_order))) /\
 rep rho [(br,0);(bl,0)] (reduce512_numeric_owned_regs rho) mf /\
 Mem.range_perm mf br 0 32 Cur Freeable /\ Mem.range_perm mf bl 0 64 Cur Freeable /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun b ofs=>~foot [(br,0);(bl,0)] (map rshape reduce512_fresh_initial_regs) b ofs) m mf.
Proof.
 intro Input;destruct (eval_reduce512_numeric_fresh rho [(br,0);(bl,0)] m Input)
  as (mf & Call & Output & Value & Frame).
 set (limbs:=reduce512_final_limbs (reduce512_body_digits rho) (reduce512_body_carry rho)).
 set (words:=map (fun sy=>il (den rho (lay [(br,0);(bl,0)]) sy)) limbs).
 assert (Length:length words=4%nat).
 { unfold words,limbs;rewrite map_length,final_symbolic_source;reflexivity. }
 destruct (rep_free_region _ _ _ _ 0 32 Output ltac:(cbn;lia) eq_refl) as [_ FreeR].
 destruct (rep_free_region _ _ _ _ 1 64 Output ltac:(cbn;lia) eq_refl) as [_ FreeL].
 assert (Stored:scalar_at mf br 0 (map Int64.repr (scalar_limbs_of (reduce512_input_integer rho mod canonical_group_order)))).
 { rewrite <-Value;change (scalar_at mf br 0 (map Int64.repr (scalar_limbs_of (C.jet_secp_scalar_mul512_accumulate.column_words_value words)))).
   apply four_words_scalar_at;[exact Length|exact FreeR|].
   intros i word Nth;unfold words in Nth;rewrite nth_error_map in Nth.
   destruct (nth_error limbs i) as [sy|] eqn:SY;[|discriminate];injection Nth as <-.
   pose proof (u64_cells_nth limbs 0 i sy SY) as Cell;rewrite Z.add_0_l in Cell.
   pose proof (region_load rho [(br,0);(bl,0)] mf 0 _ _ _ _ (rep_region _ _ _ _ 0 _ Output eq_refl) Cell) as Load.
   change (Mem.load Mint64 mf br (8*Z.of_nat i)=Some (den rho (lay [(br,0);(bl,0)]) sy)) in Load.
   rewrite Load,den_KL;[reflexivity|].
   apply (proj1 (forallb_forall _ _) (reduce512_final_limb_kinds (reduce512_body_digits rho) (reduce512_body_carry rho))).
   exact (nth_error_In _ _ SY). }
 exists mf;split;[exact Call|];split;[exact Stored|];split;[exact Output|];split;[exact FreeR|];split;
 [exact FreeL|];split.
 - eapply secp_internal_keeps_permissions;[exact reduce512_closed|reflexivity|exact Call].
 - split;[eapply (secp_closed_function_preserved f_secp256k1_scalar_reduce_512);
   [exact reduce512_closed|reflexivity|exact Call]|exact Frame].
Qed.
