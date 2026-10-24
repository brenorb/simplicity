(** Actual divstep setup for every inverse batch, not only the initial
    modulus/input pair. Old matrix values are unnecessary; ownership remains.
    No complete divstep call or external CTZ behavior is assumed here. *)
From Coq Require Import ZArith Znumtheory List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_eval C.jet_sx_mem C.jet_sx_forget_cells.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions C.jet_secp_u128_shift64_rep.
Require Import C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_seed C.jet_secp_modinv_var_first_batch.
Require Import C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg C.jet_secp_modinv_var_invariant.
Require Import C.jet_secp_modinv_normalize62_words C.jet_secp_signed62_ranges.
Require Import C.jet_secp_div62_invariant C.jet_secp_div62_entry C.divstep.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma inv_pre_batch_regs : inv_seed_regs=forget_after 6 inv_loop_regs.
Proof. reflexivity. Qed.
Lemma inv_pre_batch_forget rho beta m : rep rho beta inv_loop_regs m -> rep rho beta inv_seed_regs m.
Proof. intro Rep;rewrite inv_pre_batch_regs;apply rep_forget_after;exact Rep. Qed.

Lemma inv_batch_low_load rho beta m (high : bool) : rep rho beta inv_seed_regs m ->
  Mem.load Mint64 m (blk beta (if high then 5 else 4)) 0=
    Some (Vlong (rho (if high then 20 else 15)%nat)).
Proof.
  intro Rep.
  assert (Base : bas beta (if high then 5 else 4)=0).
  { destruct high;eapply rep_owned_region_base_zero;[exact Rep|reflexivity|reflexivity|
      exact Rep|reflexivity|reflexivity]. }
  assert (Load : xload inv_seed_regs (if high then 5 else 4) 0 tulong=
    Some (XLv (if high then 20 else 15))) by (destruct high;reflexivity).
  pose proof (xload_u64_defined_sound _ _ _ _ _ _ _ Rep Load) as Word.
  rewrite Base,Z.add_0_l in Word;destruct high;exact Word.
Qed.

Lemma inv_batch_low_modulo len rho (high : bool) :
  eqm (2^62) (Int64.unsigned (rho (if high then 20 else 15)%nat))
    (inv_fg_active_value len rho high).
Proof.
  unfold eqm,inv_fg_active_value;rewrite s62_value_mod_low.
  destruct high;apply norm62_unsigned_signed_mod.
Qed.

Theorem exec_inv_batch_loads rho beta e le m : rep rho beta inv_seed_regs m ->
  ematch beta (snd inv_start_alloc) e ->
  Clight2.exec_stmt secp_ge e le m inv_divstep_loads E0
    (inv_divstep_loaded_values (rho 15%nat) (rho 20%nat) le) m Out_normal.
Proof.
  intros Rep Env;eapply exec_inv_divstep_load_values with (bf:=blk beta 4) (bg:=blk beta 5).
  - exact (proj1 (Env _f)).
  - exact (proj1 (Env _g)).
  - exact (inv_batch_low_load rho beta m false Rep).
  - exact (inv_batch_low_load rho beta m true Rep).
Qed.

Theorem inv_batch_setup len rho st beta e le m : (0<len<=5)%nat ->
  rep rho beta inv_seed_regs m -> ematch beta (snd inv_start_alloc) e ->
  le!_eta=Some (Vlong (Int64.repr (eta st))) -> inv_state_matches len rho st -> exists le0 le1,
  Clight2.exec_stmt secp_ge e le m inv_divstep_loads E0
    (inv_divstep_loaded_values (rho 15%nat) (rho 20%nat) le) m Out_normal /\
  eval_exprlist secp_ge e (inv_divstep_loaded_values (rho 15%nat) (rho 20%nat) le) m
    [Etempvar _eta tlong;Etempvar _t'7 tlong;Etempvar _t'8 tlong;inv_matrix_address]
    (type_of_params (fn_params f_secp256k1_modinv64_divsteps_62_var))
    [Vlong (Int64.repr (eta st));Vlong (rho 15%nat);Vlong (rho 20%nat);Vptr (blk beta 6) Ptrofs.zero] /\
  function_entry2 secp_ge f_secp256k1_modinv64_divsteps_62_var
    [Vlong (Int64.repr (eta st));Vlong (rho 15%nat);Vlong (rho 20%nat);Vptr (blk beta 6) Ptrofs.zero]
    m empty_env le0 m /\
  Clight2.exec_stmt secp_ge empty_env le0 m div62_initializers E0 le1 m Out_normal /\
  div62_loop_invariant st 62 0 0 (blk beta 6) le1 /\
  Mem.range_perm m (blk beta 6) 0 32 Cur Freeable.
Proof.
  intros Len Rep Env Eta State.
  pose proof (exec_inv_batch_loads rho beta e le m Rep Env) as Loads.
  pose proof (inv_divstep_arguments_values beta e le m (Int64.repr (eta st)) (rho 15%nat) (rho 20%nat) Env Eta) as Args.
  destruct (div62_entry_invariant m st 62 (rho 15%nat) (rho 20%nat) (blk beta 6))
    as (le0 & le1 & Entry & Init & Inv).
  - lia.
  - rewrite (proj1 State);exact (inv_batch_low_modulo len rho false).
  - rewrite (proj2 State);exact (inv_batch_low_modulo len rho true).
  - destruct (rep_free_region rho beta inv_seed_regs m 6 32 Rep
      ltac:(change (6<7)%nat;lia) eq_refl) as (Base & Free).
    exists le0,le1;repeat first [assumption|split].
Qed.
