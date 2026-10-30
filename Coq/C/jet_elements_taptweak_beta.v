(** Actual original beta constant: symbol, initialized words, permissions,
    field-radix value and existence of a real initialized program memory. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Integers Memory Values Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_program_initialization.
Require Import C.jet_secp_multiply_finish_product.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Require Import C.jet_secp_beta_global C.jet_sx_mem C.jet_clight_readonly_frame
 C.jet_clight_internal_preserve C.jet_elements_taptweak_program C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_globals C.jet_elements_taptweak_startup.
Definition elements_taptweak_beta_block : block := elements_taptweak_symbol_block _secp256k1_const_beta.
Definition elements_taptweak_beta_global_rep (m : mem) : Prop :=
  Mem.valid_block m elements_taptweak_beta_block /\ Mem.range_perm m elements_taptweak_beta_block 0 40 Cur Readable /\
  forall i w, nth_error beta_words i = Some w -> Mem.load Mint64 m elements_taptweak_beta_block (8 * Z.of_nat i) = Some (Vlong w).
Definition elements_taptweak_beta_readonly_bounds (m : mem) : Prop :=
  forall ofs k p, Mem.perm m elements_taptweak_beta_block ofs k p <-> 0 <= ofs < 40 /\ perm_order Readable p.
Definition elements_taptweak_beta_initialized m := elements_taptweak_beta_global_rep m /\ elements_taptweak_beta_readonly_bounds m.

Lemma elements_taptweak_beta_symbol : Genv.find_symbol (Clight.genv_genv elements_taptweak_ge) _secp256k1_const_beta = Some elements_taptweak_beta_block.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_taptweak_beta_var_info : Genv.find_var_info (Clight.genv_genv elements_taptweak_ge) elements_taptweak_beta_block = Some v_secp256k1_const_beta.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_taptweak_beta_genv_projection : Clight.genv_genv elements_taptweak_ge = Genv.globalenv elements_taptweak_linked_program.
Proof. reflexivity. Qed.
Local Opaque elements_taptweak_beta_block elements_taptweak_ge.
Theorem elements_taptweak_beta_global_initializes m : Genv.init_mem elements_taptweak_linked_program = Some m -> elements_taptweak_beta_global_rep m.
Proof.
  intro HI; pose proof elements_taptweak_beta_var_info as HG; rewrite elements_taptweak_beta_genv_projection in HG.
  destruct (Genv.init_mem_characterization elements_taptweak_linked_program elements_taptweak_beta_block HG HI) as (HP & HB & HL & Hbytes).
  assert (HV : Mem.valid_block m elements_taptweak_beta_block) by (eapply Genv.find_var_info_not_fresh; eauto).
  change (Mem.range_perm m elements_taptweak_beta_block 0 40 Cur Readable) in HP.
  specialize (HL eq_refl).
  change (Mem.load Mint64 m elements_taptweak_beta_block 0 = Some (Vlong (Int64.repr 2652195750478318)) /\
    Mem.load Mint64 m elements_taptweak_beta_block 8 = Some (Vlong (Int64.repr 2059588628732947)) /\
    Mem.load Mint64 m elements_taptweak_beta_block 16 = Some (Vlong (Int64.repr 3435101582848073)) /\
    Mem.load Mint64 m elements_taptweak_beta_block 24 = Some (Vlong (Int64.repr 124274446989802)) /\
    Mem.load Mint64 m elements_taptweak_beta_block 32 = Some (Vlong (Int64.repr 135142927197564)) /\ True) in HL.
  split; [exact HV|]; split; [exact HP|].
  intros i w Hnth; destruct i as [|[|[|[|[|i]]]]]; cbn [beta_words nth_error] in Hnth;
    try (destruct i; discriminate Hnth); injection Hnth as E; subst w; cbn [Z.of_nat Z.mul]; tauto.
Qed.

Theorem elements_taptweak_beta_initial_bounds m : Genv.init_mem elements_taptweak_linked_program = Some m -> elements_taptweak_beta_readonly_bounds m.
Proof.
  intro HI; pose proof elements_taptweak_beta_var_info as HG; rewrite elements_taptweak_beta_genv_projection in HG.
  destruct (Genv.init_mem_characterization elements_taptweak_linked_program elements_taptweak_beta_block HG HI) as (HP & HB & _).
  change (Mem.range_perm m elements_taptweak_beta_block 0 40 Cur Readable) in HP.
  unfold elements_taptweak_beta_readonly_bounds; intros ofs k p; split.
  - intro H; exact (HB ofs k p H).
  - intros (HRange & HOrder); eapply Mem.perm_implies; [|exact HOrder].
    destruct k; [apply Mem.perm_cur_max; exact (HP ofs HRange)|exact (HP ofs HRange)].
Qed.

Theorem elements_taptweak_beta_initialized_from_init m : Genv.init_mem elements_taptweak_linked_program = Some m -> elements_taptweak_beta_initialized m.
Proof. intro HI; split; [apply elements_taptweak_beta_global_initializes|apply elements_taptweak_beta_initial_bounds]; exact HI. Qed.

Theorem elements_taptweak_beta_initial_memory:
 exists m,Genv.init_mem elements_taptweak_linked_program=Some m /\elements_taptweak_beta_initialized m.
Proof.
 destruct elements_taptweak_initial_memory_exists as(m & Init);exists m;split;
 [exact Init|apply elements_taptweak_beta_initialized_from_init;exact Init].
Qed.
Theorem elements_taptweak_beta_initialized_preserved m mf :
  elements_taptweak_beta_initialized m -> readonly_preserved m mf -> elements_taptweak_beta_initialized mf.
Proof.
  intros [[HV [HP HL]] HB] [HForward HU].
  assert (HG : Mem.unchanged_on (fun b _ => b = elements_taptweak_beta_block) m mf).
  { eapply Mem.unchanged_on_implies; [exact HU|].
    intros b ofs -> HValid; split; [exact HV|].
    intro HW; destruct (proj1 (HB ofs Max Writable) HW) as [_ HO]; inversion HO. }
  pose proof (lframe_unchanged _ _ _ HG) as [HLoads [HPerms HValid]].
  split; [|].
  - split; [exact (HValid elements_taptweak_beta_block HV)|]; split.
    + intros ofs HOfs; eapply HPerms; [exact HV|reflexivity|apply HP; exact HOfs].
    + intros i w HNth; rewrite HLoads; [exact (HL i w HNth)|exact HV|intros; reflexivity].
  - intros ofs k p; split.
    + intro HF; apply (proj1 (HB ofs k p)).
      eapply Mem.perm_unchanged_on_2; [exact HG|reflexivity|exact HV|exact HF].
    + intro HI; eapply Mem.perm_unchanged_on; [exact HG|reflexivity|apply (proj2 (HB ofs k p)); exact HI].
Qed.

