(** Original first divstep call setup: caller loads and argument evaluation,
    followed by callee entry/initialization. This is not a complete call or
    loop theorem, and makes no assumption about the CTZ builtin. *)
From Coq Require Import ZArith Znumtheory List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_eval C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements.
Require Import C.jet_secp_modinv_var_seed C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_copies.
Require Import C.jet_secp_modinv_var_de C.jet_secp_modinv_var_zero C.jet_secp_modinv_var_shorten.
Require Import C.jet_secp_modinv_fg_index C.jet_secp_modinfo_fe_copy C.jet_secp_modinfo_fe_global.
Require Import C.jet_secp_local_regions C.jet_secp_u128_shift64_rep C.jet_secp_statement_prefix.
Require Import C.jet_secp_signed62_numeric C.jet_secp_fe_math C.jet_secp_div62_invariant C.jet_secp_div62_entry C.divstep.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition inv_divstep_load (high : bool) :=
  Sset (if high then _t'8 else _t'7)
    (inv_local_index (if high then _g else _f) (Econst_int Int.zero tint)).
Definition inv_divstep_call := curve_call _secp256k1_modinv64_divsteps_62_var
  f_secp256k1_modinv64_divsteps_62_var (Some _t'1)
  [Etempvar _eta tlong;Etempvar _t'7 tlong;Etempvar _t'8 tlong;inv_matrix_address].
Definition inv_divstep_loads := statement_sequence [inv_divstep_load false;inv_divstep_load true] Sskip.
Definition inv_divstep_loaded_values f0 g0 le :=
  PTree.set _t'8 (Vlong g0) (PTree.set _t'7 (Vlong f0) le).
Definition inv_divstep_loaded (w : nat->int64) le :=
  inv_divstep_loaded_values (modinfo_fe_limb 0) (w 0%nat) le.
Lemma inv_divstep_statement_source : nth 1 (fst inv_caller_loop_parts) Sskip=
  Ssequence (statement_sequence [inv_divstep_load false;inv_divstep_load true] inv_divstep_call)
    (Sset _eta (Etempvar _t'1 tlong)).
Proof. reflexivity. Qed.

Lemma inv_seed_f0_matches : eqm (2^62) (Int64.unsigned (modinfo_fe_limb 0)) feP.
Proof. vm_compute;reflexivity. Qed.
Lemma inv_seed_g0_matches w : eqm (2^62) (Int64.unsigned (w 0%nat)) (signed62_unsigned_value w).
Proof.
  unfold eqm.
  replace (signed62_unsigned_value w) with
    (Int64.unsigned (w 0%nat)+(Int64.unsigned (w 1%nat)+2^62*Int64.unsigned (w 2%nat)+
      2^124*Int64.unsigned (w 3%nat)+2^186*Int64.unsigned (w 4%nat))*2^62)
    by (unfold signed62_unsigned_value;ring).
  rewrite Z_mod_plus_full;reflexivity.
Qed.

Lemma inv_seed_first_load w beta m (high : bool) : rep (inv_seed_rho w) beta inv_seed_regs m ->
  Mem.load Mint64 m (blk beta (if high then 5 else 4)) 0=
    Some (Vlong (if high then w 0%nat else modinfo_fe_limb 0)).
Proof.
  intro Rep.
  assert (Base : bas beta (if high then 5 else 4)=0).
  { destruct high; eapply rep_owned_region_base_zero;[exact Rep|reflexivity|reflexivity|
      exact Rep|reflexivity|reflexivity]. }
  assert (Load : xload inv_seed_regs (if high then 5 else 4) 0 tulong=
    Some (XLv (if high then 20 else 15))) by (destruct high;reflexivity).
  pose proof (xload_u64_defined_sound _ _ _ _ _ _ _ Rep Load) as Value.
  rewrite Base,Z.add_0_l in Value;destruct high;exact Value.
Qed.

Lemma exec_inv_divstep_load_values e le m bf bg f0 g0 :
  e!_f=Some (bf,fg_s62_type) -> e!_g=Some (bg,fg_s62_type) ->
  Mem.load Mint64 m bf 0=Some (Vlong f0) -> Mem.load Mint64 m bg 0=Some (Vlong g0) ->
  Clight2.exec_stmt secp_ge e le m inv_divstep_loads E0 (inv_divstep_loaded_values f0 g0 le) m Out_normal.
Proof.
  intros F G LF LG;unfold inv_divstep_loads,inv_divstep_loaded_values;cbn [statement_sequence].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _t'7 (Vlong f0) le).
  - apply exec_Sset;unfold inv_divstep_load.
    eapply eval_inv_local_load with (j:=0%nat) (b:=bf).
    + lia.
    + reflexivity.
    + exact F.
    + constructor.
    + exact LF.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m).
    + apply exec_Sset;unfold inv_divstep_load.
      eapply eval_inv_local_load with (j:=0%nat) (b:=bg).
      * lia.
      * reflexivity.
      * exact G.
      * constructor.
      * exact LG.
    + constructor.
Qed.

Theorem exec_inv_first_loads w beta e le m : rep (inv_seed_rho w) beta inv_seed_regs m ->
  ematch beta (snd inv_start_alloc) e ->
  Clight2.exec_stmt secp_ge e le m inv_divstep_loads E0 (inv_divstep_loaded w le) m Out_normal.
Proof.
  intros Rep Env;eapply exec_inv_divstep_load_values with (bf:=blk beta 4) (bg:=blk beta 5).
  - exact (proj1 (Env _f)).
  - exact (proj1 (Env _g)).
  - exact (inv_seed_first_load w beta m false Rep).
  - exact (inv_seed_first_load w beta m true Rep).
Qed.

Lemma inv_divstep_arguments_values beta e le m eta0 f0 g0 :
  ematch beta (snd inv_start_alloc) e -> le!_eta=Some (Vlong eta0) ->
  eval_exprlist secp_ge e (inv_divstep_loaded_values f0 g0 le) m
    [Etempvar _eta tlong;Etempvar _t'7 tlong;Etempvar _t'8 tlong;inv_matrix_address]
    (type_of_params (fn_params f_secp256k1_modinv64_divsteps_62_var))
    [Vlong eta0;Vlong f0;Vlong g0;Vptr (blk beta 6) Ptrofs.zero].
Proof.
  intros Env Eta.
  unfold inv_divstep_loaded_values.
  eapply eval_Econs.
  - apply eval_Etempvar;rewrite !PTree.gso by discriminate;exact Eta.
  - reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar;rewrite PTree.gso by discriminate;apply PTree.gss.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Etempvar;apply PTree.gss.
      * reflexivity.
      * eapply eval_Econs with (v1:=Vptr (blk beta 6) Ptrofs.zero).
        -- unfold inv_matrix_address;apply eval_Eaddrof;apply eval_Evar_local.
           exact (proj1 (Env _t)).
        -- reflexivity.
        -- constructor.
Qed.

Lemma inv_first_divstep_arguments w beta e le m :
  ematch beta (snd inv_start_alloc) e -> le!_eta=Some (Vlong (Int64.repr (-1))) ->
  eval_exprlist secp_ge e (inv_divstep_loaded w le) m
    [Etempvar _eta tlong;Etempvar _t'7 tlong;Etempvar _t'8 tlong;inv_matrix_address]
    (type_of_params (fn_params f_secp256k1_modinv64_divsteps_62_var))
    [Vlong (Int64.repr (-1));Vlong (modinfo_fe_limb 0);Vlong (w 0%nat);Vptr (blk beta 6) Ptrofs.zero].
Proof. apply inv_divstep_arguments_values. Qed.

Theorem inv_first_divstep_entry w m b : exists le0 le1,
  function_entry2 secp_ge f_secp256k1_modinv64_divsteps_62_var
    [Vlong (Int64.repr (-1));Vlong (modinfo_fe_limb 0);Vlong (w 0%nat);Vptr b Ptrofs.zero]
    m empty_env le0 m /\
  Clight2.exec_stmt secp_ge empty_env le0 m div62_initializers E0 le1 m Out_normal /\
  div62_loop_invariant (inv_seed_state w) 62 0 0 b le1.
Proof.
  apply (div62_entry_invariant m (inv_seed_state w) 62 (modinfo_fe_limb 0) (w 0%nat) b).
  - lia.
  - exact inv_seed_f0_matches.
  - exact (inv_seed_g0_matches w).
Qed.

Theorem inv_first_batch_setup w beta e le m : rep (inv_seed_rho w) beta inv_seed_regs m ->
  ematch beta (snd inv_start_alloc) e -> le!_eta=Some (Vlong (Int64.repr (-1))) -> exists le0 le1,
  Clight2.exec_stmt secp_ge e le m inv_divstep_loads E0 (inv_divstep_loaded w le) m Out_normal /\
  eval_exprlist secp_ge e (inv_divstep_loaded w le) m
    [Etempvar _eta tlong;Etempvar _t'7 tlong;Etempvar _t'8 tlong;inv_matrix_address]
    (type_of_params (fn_params f_secp256k1_modinv64_divsteps_62_var))
    [Vlong (Int64.repr (-1));Vlong (modinfo_fe_limb 0);Vlong (w 0%nat);Vptr (blk beta 6) Ptrofs.zero] /\
  function_entry2 secp_ge f_secp256k1_modinv64_divsteps_62_var
    [Vlong (Int64.repr (-1));Vlong (modinfo_fe_limb 0);Vlong (w 0%nat);Vptr (blk beta 6) Ptrofs.zero]
    m empty_env le0 m /\
  Clight2.exec_stmt secp_ge empty_env le0 m div62_initializers E0 le1 m Out_normal /\
  div62_loop_invariant (inv_seed_state w) 62 0 0 (blk beta 6) le1 /\
  Mem.range_perm m (blk beta 6) 0 32 Cur Freeable.
Proof.
  intros Rep Env Eta.
  pose proof (exec_inv_first_loads w beta e le m Rep Env) as Loads.
  pose proof (inv_first_divstep_arguments w beta e le m Env Eta) as Args.
  destruct (inv_first_divstep_entry w m (blk beta 6)) as (le0 & le1 & Entry & Init & State).
  destruct (rep_free_region (inv_seed_rho w) beta inv_seed_regs m 6 32 Rep
    ltac:(change (6<7)%nat;lia) eq_refl) as (Base & Free).
  exists le0,le1;repeat first [assumption|split].
Qed.
