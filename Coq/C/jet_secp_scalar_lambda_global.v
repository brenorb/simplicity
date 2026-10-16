(** Original readonly lambda global: actual initialization and concrete value. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Values Integers Memory Globalenvs Clight Ctypes.
Require Import C.jet_secp_linkage C.jets_secp C.jet_sx_mem
  C.jet_secp_scalar_mul512_accumulate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_lambda_words : list int64 :=
  [Int64.repr (-2377172193522762382); Int64.repr 1310022930574435960;
   Int64.repr (-6546514211138018214); Int64.repr 6008836872998760672].
Definition canonical_lambda_value : Z :=
  37718080363155996902926221483475020450927657555482586988616620542887997980018.
Definition scalar_lambda_block : block := secp_symbol_block _secp256k1_const_lambda.
Definition scalar_lambda_global_rep (m : mem) : Prop :=
  Mem.valid_block m scalar_lambda_block /\
  Mem.range_perm m scalar_lambda_block 0 32 Cur Readable /\
  forall i w, nth_error scalar_lambda_words i = Some w ->
    Mem.load Mint64 m scalar_lambda_block (8 * Z.of_nat i) = Some (Vlong w).

Lemma scalar_lambda_global_symbol :
  Genv.find_symbol (Clight.genv_genv secp_ge) _secp256k1_const_lambda =
    Some scalar_lambda_block.
Proof. vm_compute; reflexivity. Qed.
Lemma scalar_lambda_global_info :
  Genv.find_var_info (Clight.genv_genv secp_ge) scalar_lambda_block =
    Some v_secp256k1_const_lambda.
Proof. vm_compute; reflexivity. Qed.
Lemma scalar_lambda_words_value :
  column_words_value scalar_lambda_words = canonical_lambda_value.
Proof. vm_compute; reflexivity. Qed.
Lemma scalar_lambda_words_count : length scalar_lambda_words = 4%nat.
Proof. reflexivity. Qed.
Lemma scalar_lambda_genv_projection :
  Clight.genv_genv secp_ge = Genv.globalenv jets_secp.prog.
Proof. reflexivity. Qed.
Local Opaque secp_ge scalar_lambda_block.

Theorem scalar_lambda_global_initializes m :
  Genv.init_mem jets_secp.prog = Some m -> scalar_lambda_global_rep m.
Proof.
  intro HI.
  pose proof scalar_lambda_global_info as HG.
  rewrite scalar_lambda_genv_projection in HG.
  pose proof (Genv.init_mem_characterization jets_secp.prog scalar_lambda_block HG HI)
    as (HP & HB & HL & Hbytes).
  assert (HV : Mem.valid_block m scalar_lambda_block).
  { eapply Genv.find_var_info_not_fresh; [exact HI|exact HG]. }
  change (Mem.range_perm m scalar_lambda_block 0 32 Cur Readable) in HP.
  specialize (HL eq_refl).
  change (Mem.load Mint64 m scalar_lambda_block 0 = Some (Vlong (Int64.repr (-2377172193522762382))) /\
    Mem.load Mint64 m scalar_lambda_block 8 = Some (Vlong (Int64.repr 1310022930574435960)) /\
    Mem.load Mint64 m scalar_lambda_block 16 = Some (Vlong (Int64.repr (-6546514211138018214))) /\
    Mem.load Mint64 m scalar_lambda_block 24 = Some (Vlong (Int64.repr 6008836872998760672)) /\ True) in HL.
  unfold scalar_lambda_global_rep; split; [exact HV|]. split; [exact HP|].
  intros i w Hnth; destruct i as [|[|[|[|i]]]];
    cbn [scalar_lambda_words nth_error] in Hnth;
    try (destruct i; discriminate Hnth); injection Hnth as E; subst w;
    cbn [Z.of_nat Z.mul]; tauto.
Qed.

Theorem scalar_lambda_global_readonly_initial m :
  Genv.init_mem jets_secp.prog = Some m ->
  forall ofs, ~ Mem.perm m scalar_lambda_block ofs Max Writable.
Proof.
  intros HI ofs HW.
  pose proof scalar_lambda_global_info as HG.
  rewrite scalar_lambda_genv_projection in HG.
  pose proof (Genv.init_mem_characterization jets_secp.prog scalar_lambda_block HG HI)
    as (_ & HB & _).
  destruct (HB ofs Max Writable HW) as (_ & HO).
  change (perm_order Readable Writable) in HO; inversion HO.
Qed.

Lemma scalar_lambda_global_unchanged m m' :
  Mem.unchanged_on (fun b _ => b = scalar_lambda_block) m m' ->
  scalar_lambda_global_rep m -> scalar_lambda_global_rep m'.
Proof.
  intros HU (HV & HP & HL); unfold scalar_lambda_global_rep.
  split; [eapply Mem.valid_block_unchanged_on; eauto|]. split.
  - intros ofs Ho; eapply Mem.perm_unchanged_on; eauto; reflexivity.
  - intros i w Hnth; eapply Mem.load_unchanged_on; [exact HU| |exact (HL i w Hnth)].
    intros ofs Ho; reflexivity.
Qed.
