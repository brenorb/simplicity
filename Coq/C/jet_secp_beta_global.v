(** Actual original beta constant: symbol, initialized words, permissions,
    field-radix value and existence of a real initialized program memory. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Integers Memory Values Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_program_initialization.
Require Import C.jet_secp_multiply_finish_product.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition beta_words : list int64 :=
  [Int64.repr 2652195750478318; Int64.repr 2059588628732947;
   Int64.repr 3435101582848073; Int64.repr 124274446989802; Int64.repr 135142927197564].
Definition beta_value : Z :=
  55594575648329892869085402983802832744385952214688224221778511981742606582254.
Definition beta_digits i := nth i beta_words Int64.zero.
Definition beta_block : block := secp_symbol_block _secp256k1_const_beta.
Definition beta_global_rep (m : mem) : Prop :=
  Mem.valid_block m beta_block /\ Mem.range_perm m beta_block 0 40 Cur Readable /\
  forall i w, nth_error beta_words i = Some w -> Mem.load Mint64 m beta_block (8 * Z.of_nat i) = Some (Vlong w).
Definition beta_readonly_bounds (m : mem) : Prop :=
  forall ofs k p, Mem.perm m beta_block ofs k p <-> 0 <= ofs < 40 /\ perm_order Readable p.
Definition beta_initialized m := beta_global_rep m /\ beta_readonly_bounds m.

Lemma beta_symbol : Genv.find_symbol (Clight.genv_genv secp_ge) _secp256k1_const_beta = Some beta_block.
Proof. vm_compute; reflexivity. Qed.
Lemma beta_var_info : Genv.find_var_info (Clight.genv_genv secp_ge) beta_block = Some v_secp256k1_const_beta.
Proof. vm_compute; reflexivity. Qed.
Lemma beta_genv_projection : Clight.genv_genv secp_ge = Genv.globalenv jets_secp.prog.
Proof. reflexivity. Qed.
Lemma beta_words_count : length beta_words = 5%nat.
Proof. reflexivity. Qed.
Lemma beta_radix_value : radix_value beta_digits = beta_value.
Proof. vm_compute; reflexivity. Qed.
Lemma beta_limb_bounds i : (i < 5)%nat ->
  0 <= Int64.unsigned (beta_digits i) <= if Nat.eqb i 4 then 281474976710655 else 4503599627370495.
Proof.
  intro H; destruct i as [|[|[|[|[|i]]]]]; cbn [Nat.lt] in H; try lia;
    vm_compute; intuition discriminate.
Qed.

Local Opaque beta_block secp_ge.
Theorem beta_global_initializes m : Genv.init_mem jets_secp.prog = Some m -> beta_global_rep m.
Proof.
  intro HI; pose proof beta_var_info as HG; rewrite beta_genv_projection in HG.
  destruct (Genv.init_mem_characterization jets_secp.prog beta_block HG HI) as (HP & HB & HL & Hbytes).
  assert (HV : Mem.valid_block m beta_block) by (eapply Genv.find_var_info_not_fresh; eauto).
  change (Mem.range_perm m beta_block 0 40 Cur Readable) in HP.
  specialize (HL eq_refl).
  change (Mem.load Mint64 m beta_block 0 = Some (Vlong (Int64.repr 2652195750478318)) /\
    Mem.load Mint64 m beta_block 8 = Some (Vlong (Int64.repr 2059588628732947)) /\
    Mem.load Mint64 m beta_block 16 = Some (Vlong (Int64.repr 3435101582848073)) /\
    Mem.load Mint64 m beta_block 24 = Some (Vlong (Int64.repr 124274446989802)) /\
    Mem.load Mint64 m beta_block 32 = Some (Vlong (Int64.repr 135142927197564)) /\ True) in HL.
  split; [exact HV|]; split; [exact HP|].
  intros i w Hnth; destruct i as [|[|[|[|[|i]]]]]; cbn [beta_words nth_error] in Hnth;
    try (destruct i; discriminate Hnth); injection Hnth as E; subst w; cbn [Z.of_nat Z.mul]; tauto.
Qed.

Theorem beta_initial_bounds m : Genv.init_mem jets_secp.prog = Some m -> beta_readonly_bounds m.
Proof.
  intro HI; pose proof beta_var_info as HG; rewrite beta_genv_projection in HG.
  destruct (Genv.init_mem_characterization jets_secp.prog beta_block HG HI) as (HP & HB & _).
  change (Mem.range_perm m beta_block 0 40 Cur Readable) in HP.
  unfold beta_readonly_bounds; intros ofs k p; split.
  - intro H; exact (HB ofs k p H).
  - intros (HRange & HOrder); eapply Mem.perm_implies; [|exact HOrder].
    destruct k; [apply Mem.perm_cur_max; exact (HP ofs HRange)|exact (HP ofs HRange)].
Qed.

Theorem beta_initialized_from_init m : Genv.init_mem jets_secp.prog = Some m -> beta_initialized m.
Proof. intro HI; split; [apply beta_global_initializes|apply beta_initial_bounds]; exact HI. Qed.

Definition beta_program_initialization_ok := program_initialization_okb jets_secp.prog.
Lemma beta_program_initialization_ok_true : beta_program_initialization_ok = true.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Local Opaque Genv.init_mem program_initialization_okb jets_secp.prog.
Theorem beta_initialized_memory_exists :
  exists m, Genv.init_mem jets_secp.prog = Some m /\ beta_initialized m.
Proof.
  destruct (program_initialization_checked (Ctypes.program_of_program jets_secp.prog)
    beta_program_initialization_ok_true) as (m & HI).
  exists m; split; [exact HI|apply beta_initialized_from_init; exact HI].
Qed.
