(** Shared maximum-permission monotonicity for real Clight2 executions. *)
From Coq Require Import List.
From compcert Require Import Coqlib Ctypes Cop Clight ClightBigstep Memory Events.
Set Default Timeout 10.

(** The standard forward-memory property, proved from installed CompCert
    lemmas directly; no additional unbuilt VST modules are required. *)
Definition mem_forward (m mf : Mem.mem) : Prop :=
  forall b, Mem.valid_block m b ->
    Mem.valid_block mf b /\
    (forall ofs p, Mem.perm mf b ofs Max p -> Mem.perm m b ofs Max p).

Lemma mem_forward_refl m : mem_forward m m.
Proof. intros b HB; split; auto. Qed.

Lemma mem_forward_trans m mi mf :
  mem_forward m mi -> mem_forward mi mf -> mem_forward m mf.
Proof.
  intros H1 H2 b HB; destruct (H1 b HB) as [HI HP1].
  destruct (H2 b HI) as [HF HP2]; split; [exact HF|].
  intros; apply HP1, HP2; assumption.
Qed.

Lemma store_forward chunk m b ofs v mf :
  Mem.store chunk m b ofs v = Some mf -> mem_forward m mf.
Proof.
  intros HS block HB; split.
  - eapply Mem.store_valid_block_1; eassumption.
  - intros; eapply Mem.perm_store_2; eassumption.
Qed.

Lemma storebytes_forward m b ofs bytes mf :
  Mem.storebytes m b ofs bytes = Some mf -> mem_forward m mf.
Proof.
  intros HS block HB; split.
  - eapply Mem.storebytes_valid_block_1; eassumption.
  - intros; eapply Mem.perm_storebytes_2; eassumption.
Qed.

Lemma alloc_forward m lo hi mf fresh :
  Mem.alloc m lo hi = (mf, fresh) -> mem_forward m mf.
Proof.
  intros HA block HB; split.
  - eapply Mem.valid_block_alloc; eassumption.
  - intros; eapply Mem.perm_alloc_4; [exact HA|eassumption|].
    intro HE; subst block; exact (Mem.fresh_block_alloc _ _ _ _ _ HA HB).
Qed.

Lemma free_forward m b lo hi mf :
  Mem.free m b lo hi = Some mf -> mem_forward m mf.
Proof.
  intros HF block HB; split.
  - eapply Mem.valid_block_free_1; eassumption.
  - intros; eapply Mem.perm_free_3; eassumption.
Qed.

Lemma freelist_forward blocks m mf :
  Mem.free_list m blocks = Some mf -> mem_forward m mf.
Proof.
  revert m mf; induction blocks as [|[[b lo] hi] rest IH]; intros m mf HF.
  - cbn in HF; inversion HF; subst; apply mem_forward_refl.
  - cbn in HF; destruct (Mem.free m b lo hi) as [mi|] eqn:HE; [|discriminate].
    eapply mem_forward_trans; [eapply free_forward; exact HE|apply IH; exact HF].
Qed.

Lemma external_call_mem_forward ef ge args m t result mf :
  external_call ef ge args m t result mf -> mem_forward m mf.
Proof.
  intros HE b HB; split.
  - eapply external_call_valid_block; eassumption.
  - intros; eapply external_call_max_perm; eassumption.
Qed.

Lemma clight_alloc_variables_forward ge e m vars e' m' :
  alloc_variables ge e m vars e' m' -> mem_forward m m'.
Proof.
  intro H; induction H; eauto using mem_forward_refl, mem_forward_trans, alloc_forward.
Qed.

Lemma clight_entry2_forward ge f args m e le m' :
  function_entry2 ge f args m e le m' -> mem_forward m m'.
Proof.
  intro H; inversion H; subst; eapply clight_alloc_variables_forward; eassumption.
Qed.

Lemma clight_assign_forward ce ty m b ofs bf v m' :
  assign_loc ce ty m b ofs bf v m' -> mem_forward m m'.
Proof.
  intro H; inversion H; subst.
  - eapply store_forward; cbn [Mem.storev] in *; eassumption.
  - eapply storebytes_forward; eassumption.
  - match goal with HBits : store_bitfield _ _ _ _ _ _ _ _ _ _ |- _ =>
      inversion HBits; subst end.
    eapply store_forward; cbn [Mem.storev] in *; eassumption.
Qed.

Theorem clight_exec_forward ge :
  (forall e le m s t le' m' out,
    Clight2.exec_stmt ge e le m s t le' m' out -> mem_forward m m') /\
  (forall m f args t m' result,
    Clight2.eval_funcall ge m f args t m' result -> mem_forward m m').
Proof.
  apply (exec_stmt_funcall_ind function_entry2 ge
    (fun e le m s t le' m' out => mem_forward m m')
    (fun m f args t m' result => mem_forward m m'));
    intros; eauto 8 using mem_forward_refl, mem_forward_trans,
      clight_assign_forward, clight_entry2_forward, external_call_mem_forward,
      freelist_forward.
Qed.
