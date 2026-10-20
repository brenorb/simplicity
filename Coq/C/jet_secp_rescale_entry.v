(** Actual entry/allocation for the original rescale helper.  No allocation,
    initialized square destination, or helper execution is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_square_separate_layout C.jet_secp_square_separate_caller C.jet_secp_rescale_prefix.
Require Import C.jet_secp_b32_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition rescale_input_regs := [rescale_point_storage; separate_input true (Some 40)].
Lemma rescale_function_ok : fn_okb f_secp256k1_gej_rescale = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma rescale_allocation_model :
  xalloc (std_cells (genv_cenv secp_ge)) (genv_cenv secp_ge)
    (fn_vars f_secp256k1_gej_rescale) 2 = Some (fst rescale_allocated, snd rescale_allocated).
Proof. reflexivity. Qed.
Lemma rescale_initial_regs : rescale_input_regs ++ fst rescale_allocated = rescale_prefix_regs.
Proof. reflexivity. Qed.
Lemma rescale_binding_model : xbind (fn_params f_secp256k1_gej_rescale)
  [XP 0 0;XP 1 0] (PTree.empty sx) = Some rescale_prefix_temps.
Proof. reflexivity. Qed.

Theorem rescale_inputs_from_storage rho m bp bs :
  Mem.range_perm m bp 0 128 Cur Freeable ->
  fe_at m bs 0 (words5 rho) -> Mem.range_perm m bs 0 40 Cur Freeable -> bp <> bs ->
  rep rho [(bp,0);(bs,0)] rescale_input_regs m.
Proof.
  intros HP HS HF HNe; apply two_region_rep_separate; [reflexivity|exact HNe| |].
  - unfold rescale_point_storage, region_ok; cbn [bas blk lay nth fst snd rcells rw rfree].
    split; [lia|]; split.
    + eapply Mem.perm_valid_block; apply (HP 0); lia.
    + split; [reflexivity|]; split; [constructor|].
      split; [reflexivity|]; split; [reflexivity|]; split; [exact HP|constructor].
  - apply field_words_region; [reflexivity|exact HS|exact HF].
Qed.

Local Opaque secp_ge xalloc rescale_allocated rescale_prefix_regs.
Theorem rescale_actual_entry rho beta m : rep rho beta rescale_input_regs m ->
  exists betaN e le mi,
    function_entry2 secp_ge f_secp256k1_gej_rescale
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] m e le mi /\
    rep rho (beta ++ betaN) rescale_prefix_regs mi /\
    tmatch rho (beta ++ betaN) rescale_prefix_temps le /\
    ematch (beta ++ betaN) (snd rescale_allocated) e /\
    length betaN = length (fst rescale_allocated) /\
    Forall (fun p => ~ Mem.valid_block m (fst p)) betaN /\
    Mem.unchanged_on (fun _ _ => True) m mi.
Proof.
  intro HR.
  destruct (fn_okb_true _ rescale_function_ok) as (HN1 & HN2 & HD).
  assert (HL : length beta = 2%nat) by (destruct HR as [HL _]; exact HL).
  destruct (xalloc_sound secp_ge rho (std_cells (genv_cenv secp_ge))
    (fn_vars f_secp256k1_gej_rescale) 2 (fst rescale_allocated) (snd rescale_allocated)
    beta rescale_input_regs m empty_env rescale_allocation_model HR HL HN1)
    as (e & mi & betaN & HA & HRi & HLN & HE & HIdx & HInj & HFresh & HU).
  assert (HB : map (den rho (lay (beta ++ betaN))) [XP 0 0;XP 1 0] =
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
     Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))]).
  { transitivity (map (den rho (lay beta)) [XP 0 0;XP 1 0]).
    - apply map_den_ext with (n := 2%nat).
      + intros r Hr; apply lay_app_l; lia.
      + reflexivity.
    - cbn [map den]; rewrite !Z.add_0_r; reflexivity. }
  destruct (xbind_sound rho (beta ++ betaN) (fn_params f_secp256k1_gej_rescale)
    [XP 0 0;XP 1 0] (PTree.empty sx) rescale_prefix_temps
    (create_undef_temps (fn_temps f_secp256k1_gej_rescale)) rescale_binding_model)
    as (le & HBind & HT).
  { intros id x HX; rewrite PTree.gempty in HX; discriminate. }
  rewrite HB in HBind.
  assert (HEnv : ematch (beta ++ betaN) (snd rescale_allocated) e).
  { intros id; split.
    - rewrite HE; destruct (vlookup (snd rescale_allocated) id) as [[r ty]|];
        [reflexivity|apply PTree.gempty].
    - intros r ty HV; exact (proj1 (proj2 (proj2 (HIdx id r ty HV)))). }
  rewrite rescale_initial_regs in HRi.
  exists betaN, e, le, mi; split.
  - constructor; assumption.
  - split; [exact HRi|]; split; [exact HT|]; split; [exact HEnv|].
    split; [exact HLN|]; split; assumption.
Qed.

Local Transparent rescale_prefix_regs.
Lemma rescale_prefix_point_outside rho beta m : rep rho beta rescale_prefix_regs m ->
  forall ofs, ~ foot beta (map rshape rescale_prefix_regs) (blk beta 0) ofs.
Proof.
  intros (_ & HS & _) ofs (r & sh & d & ch & HN & HC & HB & HO).
  destruct r as [|[|[|r]]].
  - inversion HN; subst sh; contradiction.
  - destruct (HS 0%nat 1%nat rescale_point_storage (separate_input true (Some 40))
      ltac:(discriminate) eq_refl eq_refl) as [HNe|(HF & _)]; [exact (HNe HB)|discriminate HF].
  - destruct (HS 0%nat 2%nat rescale_point_storage
      (mkreg (map (fun ofs => mkcell ofs Mint64 None) [0;8;16;24;32]) true (Some 40))
      ltac:(discriminate) eq_refl eq_refl) as [HNe|(HF & _)]; [exact (HNe HB)|discriminate HF].
  - destruct r; discriminate HN.
Qed.

Lemma rescale_prefix_point_frame rho beta m mf : rep rho beta rescale_prefix_regs m ->
  lframe (fun b ofs => ~ foot beta (map rshape rescale_prefix_regs) b ofs) m mf ->
  lframe (fun b _ => b = blk beta 0) m mf.
Proof.
  intros HR HF; eapply lframe_implies; [exact HF|].
  intros b ofs -> _; exact (rescale_prefix_point_outside rho beta m HR ofs).
Qed.
