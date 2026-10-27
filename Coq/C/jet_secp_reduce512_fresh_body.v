(** Original reduce512 body from uninitialized destination cells. The stage
    computations agree with the checked arithmetic checkpoints. Only actual
    third-fold writes establish the destination's initialized representation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep
 C.jet_sx_forget_cells C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar
 C.jet_secp_statement_prefix C.jet_secp_compact_stmt_shift64
 C.jet_secp_reduce512_fresh_runs C.jet_secp_reduce512_first_run C.jet_secp_reduce512_second_run
 C.jet_secp_reduce512_typed_stage C.jet_secp_reduce512_two_stages
 C.jet_secp_reduce512_checkpoint C.jet_secp_reduce512_third_stage
 C.jet_secp_reduce512_third_checkpoint C.jet_secp_reduce512_final_stage
 C.jet_secp_reduce512_final_checkpoint C.jet_secp_reduce512_final_exec
 C.jet_secp_reduce512_final_atomic C.jet_secp_reduce512_final_value
 C.jet_secp_reduce512_body_numeric C.jet_secp_reduce512_first_symbolic
 C.jet_secp_reduce512_wide C.jet_secp_scalar_mul512_symbolic.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque reduce512_allocated reduce512_first_state reduce512_typed_stage_state
 reduce512_third_state reduce512_final_state reduce512_first_prefix
 reduce512_typed_stage reduce512_third_stage reduce512_final_suffix.

Lemma reduce512_fresh_checkpoint rho beta le :
 tmatch rho beta (stemps reduce512_fresh_first_state) le ->
 tmatch rho beta (reduce512_typed_stage_temps (first_checkpoint_digits rho) (first_checkpoint_m6 rho)) le.
Proof.
 intro Temps.
 destruct reduce512_fresh_first_sources as (SR & SL & S0 & S1 & S2 & S3 & S4 & S5 & S6).
 destruct (first_columns_rep rho (lay beta)) as [[D0 _] [[D1 _] [[D2 _] [[D3 _] [[D4 _] [D5 [DH _]]]]]]].
 pose proof (Temps _ _ SR) as LR;pose proof (Temps _ _ SL) as LL.
 pose proof (Temps _ _ S0) as L0;rewrite D0 in L0.
 pose proof (Temps _ _ S1) as L1;rewrite D1 in L1.
 pose proof (Temps _ _ S2) as L2;rewrite D2 in L2.
 pose proof (Temps _ _ S3) as L3;rewrite D3 in L3.
 pose proof (Temps _ _ S4) as L4;rewrite D4 in L4.
 pose proof (Temps _ _ S5) as L5;rewrite D5 in L5.
 pose proof (Temps _ _ S6) as L6.
 change (le!_m6=Some (Vint (Int64.loword (il (den rho (lay beta) (sc_hi first_sy5)))))) in L6.
 rewrite DH in L6;unfold reduce512_typed_stage_temps.
 apply tmatch_checkpoint_set;[|exact L6];apply tmatch_checkpoint_set;[|exact L5];
 apply tmatch_checkpoint_set;[|exact L4];apply tmatch_checkpoint_set;[|exact L3];
 apply tmatch_checkpoint_set;[|exact L2];apply tmatch_checkpoint_set;[|exact L1];
 apply tmatch_checkpoint_set;[|exact L0];apply tmatch_checkpoint_set;[|exact LL];
 apply tmatch_checkpoint_set;[|exact LR];intros id x X;rewrite PTree.gempty in X;discriminate.
Qed.

Theorem exec_reduce512_fresh_body rho beta e le m :
 rep rho beta (sregs reduce512_fresh_first) m ->
 tmatch rho beta reduce512_initial_temps le -> ematch beta (snd reduce512_allocated) e ->
 exists lef mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_scalar_reduce_512) E0 lef mf Out_normal /\
 rep rho beta (sregs (reduce512_final_state (reduce512_body_digits rho) (reduce512_body_carry rho))) mf /\
 (forall i sy,nth_error (reduce512_final_limbs (reduce512_body_digits rho) (reduce512_body_carry rho)) i=Some sy ->
  Mem.load Mint64 mf (blk beta 0) (bas beta 0+8*Z.of_nat i)=Some (den rho (lay beta) sy)) /\
 final_output_value (reduce512_body_digits rho) (reduce512_body_carry rho) rho (lay beta)=
  reduce512_input_integer rho mod canonical_group_order /\
 tmatch rho beta (stemps (reduce512_final_state (reduce512_body_digits rho) (reduce512_body_carry rho))) lef /\
 lframe (fun b ofs=>~foot beta (map rshape (sregs reduce512_fresh_first)) b ofs) m mf.
Proof.
 intros Rep Temps Env.
 destruct (compact_stmt_shift64_normal 300 (snd reduce512_allocated) reduce512_fresh_first
  reduce512_first_prefix reduce512_fresh_first_state reduce512_fresh_first_run
  rho beta e le m Rep Temps Env) as (le1 & m1 & Run1 & Rep1 & Temps1 & Shape1 & Frame1).
 pose proof (rep_forget_after rho beta _ m1 2 Rep1) as Next1.
 rewrite reduce512_fresh_first_stack in Next1.
 pose proof (reduce512_fresh_checkpoint rho beta le1 Temps1) as Check1.
 destruct (compact_stmt_shift64_normal 300 (snd reduce512_allocated)
  (reduce512_fresh_second (first_checkpoint_digits rho) (first_checkpoint_m6 rho))
  reduce512_typed_stage (reduce512_fresh_second_state (first_checkpoint_digits rho) (first_checkpoint_m6 rho))
  (reduce512_fresh_second_run _ _) rho beta e le1 m1 Next1 Check1 Env)
  as (le2 & m2 & Run2 & Rep2 & Temps2 & Shape2 & Frame2).
 pose proof (rep_forget_after rho beta _ m2 2 Rep2) as Next2.
 rewrite reduce512_fresh_second_stack in Next2.
 pose proof (second_checkpoint_tmatch rho beta le2 Temps2) as Check2.
 destruct (compact_stmt_shift64_normal 300 (snd reduce512_allocated)
  (reduce512_fresh_third (second_checkpoint_digits rho) (second_checkpoint_p4 rho))
  reduce512_third_stage (reduce512_third_state (second_checkpoint_digits rho) (second_checkpoint_p4 rho))
  (reduce512_fresh_third_run _ _) rho beta e le2 m2 Next2 Check2 Env)
  as (le3 & m3 & Run3 & Rep3 & Temps3 & Shape3 & Frame3).
 pose proof (third_checkpoint_rep _ _ rho beta m3 Rep3) as Next3.
 pose proof (third_checkpoint_tmatch _ _ rho beta le3 Temps3) as Check3.
 destruct (exec_typed_final_suffix (reduce512_body_digits rho) (reduce512_body_carry rho)
  rho beta e le3 m3 Next3 Check3 Env) as (lef & mf & Run4 & Final & Loads & FinalTemps & Frame4).
 assert (Run12:Clight2.exec_stmt secp_ge e le m reduce512_second_prefix E0 le2 m2 Out_normal).
 { rewrite <-reduce512_typed_stage_source;eapply exec_statement_prefix_then_last;[exact Run1|exact Run2]. }
 assert (Run123:Clight2.exec_stmt secp_ge e le m reduce512_third_prefix E0 le3 m3 Out_normal).
 { rewrite <-reduce512_third_source;eapply exec_statement_prefix_then_last;[exact Run12|exact Run3]. }
 exists lef,mf;split.
 - rewrite <-reduce512_final_source;eapply exec_statement_prefix_then_last;[exact Run123|exact Run4].
 - split;[exact Final|];split;[exact Loads|];split;[apply reduce512_body_numeric|];split;[exact FinalTemps|].
   change (lframe (fun b ofs=>~foot beta (map rshape (sregs reduce512_fresh_first)) b ofs) m1 m2) in Frame2.
   change (lframe (fun b ofs=>~foot beta (map rshape (sregs reduce512_fresh_first)) b ofs) m2 m3) in Frame3.
   cbn [reduce512_final_initial sregs] in Frame4;rewrite final_shape_same_entry in Frame4.
   rewrite <-(reduce512_fresh_shape reduce512_first_initial) in Frame4.
   eapply lframe_trans;[exact Frame1|];eapply lframe_trans;[exact Frame2|];
   eapply lframe_trans;[exact Frame3|exact Frame4].
Qed.
