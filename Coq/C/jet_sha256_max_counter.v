(** The actual pinned readonly max-counter initializer and store protection.
    The load follows from CompCert global initialization, not an assumed
    execution or an added axiom about SHA behavior. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_readonly_int64.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma sha256_max_counter_symbol : Genv.find_symbol (Clight.genv_genv ge0) _sha256_max_counter =
  Some (jet_symbol_block _sha256_max_counter).
Proof. vm_compute; reflexivity. Qed.
Lemma sha256_max_counter_var_info : Genv.find_var_info (Genv.globalenv prog)
  (jet_symbol_block _sha256_max_counter) = Some v_sha256_max_counter.
Proof. vm_compute; reflexivity. Qed.
Lemma sha256_max_counter_threshold :
  Int64.shru (Int64.repr 2305843009213693952) (Int64.repr 6) = Int64.repr 36028797018963968.
Proof. vm_compute; reflexivity. Qed.

Definition sha256_max_counter_at m : Prop :=
  Mem.load Mint64 m (jet_symbol_block _sha256_max_counter) 0 =
    Some (Vlong (Int64.repr 2305843009213693952)) /\
  (forall ofs, ~ Mem.perm m (jet_symbol_block _sha256_max_counter) ofs Cur Writable).

Theorem sha256_max_counter_initialized m :
  Genv.init_mem prog = Some m -> sha256_max_counter_at m.
Proof.
  intro HInit.
  exact (@readonly_int64_global_initialized Clight.fundef type prog
    (jet_symbol_block _sha256_max_counter) (Tlong Unsigned noattr)
    (Int64.repr 2305843009213693952) m sha256_max_counter_var_info HInit).
Qed.

Lemma sha256_max_counter_valid_block m :
  sha256_max_counter_at m -> Mem.valid_block m (jet_symbol_block _sha256_max_counter).
Proof.
  intros [HL _]. eapply Mem.perm_valid_block.
  eapply (Mem.valid_access_perm m Mint64 _ 0 Cur Readable).
  eapply Mem.load_valid_access; exact HL.
Qed.

Theorem sha256_max_counter_alloc m mf lo hi fresh :
  sha256_max_counter_at m -> Mem.alloc m lo hi = (mf, fresh) ->
  sha256_max_counter_at mf /\ fresh <> jet_symbol_block _sha256_max_counter.
Proof.
  intros HGlobal HA.
  assert (HOther : jet_symbol_block _sha256_max_counter <> fresh).
  { intro Heq. pose proof (sha256_max_counter_valid_block m HGlobal) as HV.
    rewrite Heq in HV. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
  split; [|congruence]. destruct HGlobal as [HL HNoWrite]. split.
  - eapply Mem.load_alloc_other; eauto.
  - intros pos HP; apply (HNoWrite pos).
    eapply Mem.perm_alloc_4; eauto.
Qed.

Theorem sha256_max_counter_free m mf b lo hi :
  sha256_max_counter_at m -> b <> jet_symbol_block _sha256_max_counter ->
  Mem.free m b lo hi = Some mf -> sha256_max_counter_at mf.
Proof.
  intros [HL HNoWrite] HOther HF. split.
  - erewrite Mem.load_free; [exact HL|exact HF|left; congruence].
  - intros pos HP; apply (HNoWrite pos); eapply Mem.perm_free_3; eauto.
Qed.

Lemma sha256_max_counter_writable_other m chunk b ofs :
  sha256_max_counter_at m -> Mem.valid_access m chunk b ofs Writable ->
  b <> jet_symbol_block _sha256_max_counter.
Proof.
  intros [_ HNoWrite] HW Heq; subst b.
  apply (HNoWrite ofs). eapply Mem.valid_access_perm; exact HW.
Qed.

Theorem sha256_max_counter_store m mf chunk b ofs v :
  sha256_max_counter_at m -> Mem.store chunk m b ofs v = Some mf -> sha256_max_counter_at mf.
Proof.
  intros HGlobal HS. pose proof (Mem.store_valid_access_3 _ _ _ _ _ _ HS) as HW.
  pose proof (sha256_max_counter_writable_other m chunk b ofs HGlobal HW) as HOther.
  destruct HGlobal as [HL HNoWrite]. split.
  - erewrite Mem.load_store_other; [exact HL|exact HS|left; congruence].
  - intros pos HP; apply (HNoWrite pos); eapply Mem.perm_store_2; eauto.
Qed.

Lemma eval_sha256_max_counter e le m :
  e!_sha256_max_counter = None -> sha256_max_counter_at m ->
  eval_expr ge0 e le m (Evar _sha256_max_counter (Tlong Unsigned noattr))
    (Vlong (Int64.repr 2305843009213693952)).
Proof.
  intros HE [HL _]. eapply eval_Elvalue.
  - apply eval_Evar_global; [exact HE|exact sha256_max_counter_symbol].
  - apply deref_loc_value with (chunk := Mint64); [reflexivity|exact HL].
Qed.
