(** Execute the original scalar_cadd_bit(r,0,flag) statement tree. Selector
    arguments are evaluated from the actual C expressions; the other original
    slices reuse the existing verified symbolic executor and shift oracle. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep C.jet_sx_pure
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements C.jet_secp_statement_prefix
 C.jet_secp_scalar_cadd_control C.jet_secp_scalar_cadd_run C.jet_secp_u128_mul_exec.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge cadd_checkpoint cadd_called_state cadd_selected_state cadd_prefix_state cadd_final_state.

Lemma cadd_stmt_normal fuel ve st stmt st' :
 xstmt (genv_cenv secp_ge) [] cadd_table fuel ve st stmt=Some (RDone st' ONormal) ->
 forall rho beta e le m,
 rep rho beta (sregs st) m -> tmatch rho beta (stemps st) le -> ematch beta ve e ->
 exists le' mf, Clight2.exec_stmt secp_ge e le m stmt E0 le' mf Out_normal /\
 rep rho beta (sregs st') mf /\ tmatch rho beta (stemps st') le' /\
 lframe (fun b ofs=>~foot beta (map rshape (sregs st)) b ofs) m mf.
Proof.
 intros H rho beta e le m Rep Temps Env.
 destruct (xstmt_sound secp_ge [] cadd_table (fun _ _=>True) (fun _ _ _=>True) (fun _=>False)
  ltac:(auto) ltac:(intros;contradiction) cadd_table_ok fuel ve st stmt (RDone st' ONormal)
  H rho beta e le m Rep Temps Env) as (le' & mf & out & Run & Post).
 - split;intros;discriminate.
 - intros r _ [].
 - exact I.
 - apply Forall_forall;intros;exact I.
 - destruct Post as (Rep' & Temps' & Outcome & Shape & _ & Frame).
   cbn [rsel fst snd] in Rep',Temps',Outcome,Shape.
   destruct out;cbn [outmatch] in Outcome;try contradiction.
   exists le',mf;split;[exact Run|];split;[exact Rep'|];split;[exact Temps'|].
   eapply lframe_implies;[exact Frame|].
   intros b ofs Outside Valid;split;[exact Valid|];split;[exact Outside|tauto].
Qed.

Local Opaque xstmt cadd_table cadd_allocated.

Theorem exec_cadd_selector flag j rho beta e le m : (j<4)%nat ->
 rep rho beta (sregs (cadd_checkpoint flag j)) m ->
 tmatch rho beta (stemps (cadd_checkpoint flag j)) le -> ematch beta (snd cadd_allocated) e ->
 exists mf, Clight2.exec_stmt secp_ge e le m (cadd_selector_statement j) E0 le mf Out_normal /\
 rep rho beta (sregs (cadd_selected_state flag j)) mf /\
 tmatch rho beta (stemps (cadd_selected_state flag j)) le /\
 lframe (fun b ofs=>~foot beta (map rshape (cadd_initial_regs++fst cadd_allocated)) b ofs) m mf.
Proof.
 intros J Rep Temps Env.
 pose proof (cadd_selector_run_eq flag j J) as Computed;unfold cadd_selector_run in Computed.
 destruct (xfun_pure secp_ge u128_mul_functions u128_mul_functions_ok 100
  f_secp256k1_u128_accum_u64 [XP 1 0;XLc (cadd_selector_value flag j)]
  (sregs (cadd_checkpoint flag j)) 0 (RDone (cadd_called_state flag j) ONormal)
  Computed ltac:(cbn [leaves_log_nil];rewrite (cadd_selector_log_nil flag j J);reflexivity)
  rho beta m Rep) as (mf & result & Call & Rep' & Return & Shape & Frame).
 cbn [rsel fst] in Rep',Return,Shape.
 assert (Var:vlookup (snd cadd_allocated) _t=Some (1%nat,Tstruct _secp256k1_uint128 noattr)).
 { rewrite cadd_local_lookup;reflexivity. }
 assert (Base:bas beta 1=0) by exact (proj2 (Env _t) _ _ Var).
 assert (Local:e!_t=Some (blk beta 1,Tstruct _secp256k1_uint128 noattr)).
 { rewrite (proj1 (Env _t)),Var;reflexivity. }
 assert (Bit:le!_bit=Some (Vint (cadd_bit_setting flag))).
 { rewrite <- (cadd_bit_expression_value rho (lay beta) flag);apply Temps;apply cadd_checkpoint_bit;lia. }
 change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_u128_accum_u64)
  [Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0));Vlong (cadd_selector_value flag j)] E0 mf result) in Call.
 rewrite Base in Call;change (Ptrofs.repr (0+0)) with Ptrofs.zero in Call.
 exists mf;split.
 - rewrite cadd_selector_source by exact J.
   eapply (exec_curve_call _secp256k1_u128_accum_u64 f_secp256k1_u128_accum_u64 None
    [cadd_t_address;cadd_selector_expr j]
    [Vptr (blk beta 1) Ptrofs.zero;Vlong (cadd_selector_value flag j)] result e le m mf).
   + unfold secp_pure;repeat (first [left;reflexivity|right]).
   + rewrite (proj1 (Env _secp256k1_u128_accum_u64)),cadd_local_lookup;reflexivity.
   + eapply eval_Econs;[apply eval_cadd_t_address;exact Local|reflexivity|].
     eapply eval_Econs with (v1:=Vlong (cadd_selector_value flag j));
      [exact (eval_cadd_selector_expr e le m flag j J Bit)|reflexivity|constructor].
   + exact Call.
 - split;[change (rep rho beta (sregs (cadd_called_state flag j)) mf);exact Rep'|].
   split;[rewrite cadd_selected_temps;exact Temps|].
   rewrite (cadd_checkpoint_shape flag j ltac:(lia)) in Frame;exact Frame.
Qed.

Theorem exec_cadd_gap flag j rho beta e le m : (j<4)%nat ->
 rep rho beta (sregs (cadd_selected_state flag j)) m ->
 tmatch rho beta (stemps (cadd_selected_state flag j)) le -> ematch beta (snd cadd_allocated) e ->
 exists le' mf, Clight2.exec_stmt secp_ge e le m
  (if Nat.ltb j 3 then cadd_gap_statement j else cadd_tail) E0 le' mf Out_normal /\
 rep rho beta (sregs (cadd_checkpoint flag (S j))) mf /\
 tmatch rho beta (stemps (cadd_checkpoint flag (S j))) le' /\
 lframe (fun b ofs=>~foot beta (map rshape (cadd_initial_regs++fst cadd_allocated)) b ofs) m mf.
Proof.
 intros J Rep Temps Env.
 pose proof (cadd_gap_run_eq flag j J) as Computed;unfold cadd_gap_run in Computed.
 destruct (cadd_stmt_normal 200 (snd cadd_allocated) (cadd_selected_state flag j)
  (if Nat.ltb j 3 then cadd_gap_statement j else cadd_tail) (cadd_checkpoint flag (S j))
  Computed rho beta e le m Rep Temps Env) as (le' & mf & Run & Rep' & Temps' & Frame).
 exists le',mf;split;[exact Run|];split;[exact Rep'|];split;[exact Temps'|].
 rewrite (cadd_selected_shape flag j J) in Frame;exact Frame.
Qed.

Fixpoint cadd_remaining (j count:nat) : statement :=
 match count with
 | O=>Ssequence (cadd_selector_statement j) cadd_tail
 | S n=>Ssequence (cadd_selector_statement j)
   (statement_sequence (cadd_gap_spine j) (cadd_remaining (S j) n))
 end.
Lemma cadd_body_remaining_source : fn_body f_secp256k1_scalar_cadd_bit=
 statement_sequence cadd_prefix_spine (cadd_remaining 0 3).
Proof. symmetry;exact cadd_body_source. Qed.

Theorem exec_cadd_remaining count : forall j flag rho beta e le m, (j+count=3)%nat ->
 rep rho beta (sregs (cadd_checkpoint flag j)) m ->
 tmatch rho beta (stemps (cadd_checkpoint flag j)) le -> ematch beta (snd cadd_allocated) e ->
 exists le' mf, Clight2.exec_stmt secp_ge e le m (cadd_remaining j count) E0 le' mf Out_normal /\
 rep rho beta (sregs (cadd_checkpoint flag 4)) mf /\
 lframe (fun b ofs=>~foot beta (map rshape (cadd_initial_regs++fst cadd_allocated)) b ofs) m mf.
Proof.
 induction count as [|count IH];intros j flag rho beta e le m Range Rep Temps Env.
 - assert (Index:j=3%nat) by lia;subst j.
   destruct (exec_cadd_selector flag 3 rho beta e le m ltac:(lia) Rep Temps Env)
    as (m1 & Selector & Rep1 & Temps1 & Frame1).
   destruct (exec_cadd_gap flag 3 rho beta e le m1 ltac:(lia) Rep1 Temps1 Env)
    as (le' & mf & Tail & Rep' & Temps' & Frame2).
   exists le',mf;split.
   + cbn [cadd_remaining];eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);
     [exact Selector|exact Tail].
   + split;[exact Rep'|];eapply lframe_trans;[exact Frame1|exact Frame2].
 - assert (J:(j<3)%nat) by lia.
   destruct (exec_cadd_selector flag j rho beta e le m ltac:(lia) Rep Temps Env)
    as (m1 & Selector & Rep1 & Temps1 & Frame1).
   destruct (exec_cadd_gap flag j rho beta e le m1 ltac:(lia) Rep1 Temps1 Env)
    as (le2 & m2 & Gap & Rep2 & Temps2 & Frame2).
   assert (Test:Nat.ltb j 3=true) by (apply Nat.ltb_lt;exact J);rewrite Test in Gap.
   destruct (IH (S j) flag rho beta e le2 m2 ltac:(lia) Rep2 Temps2 Env)
    as (le' & mf & Rest & Rep' & Frame3).
   exists le',mf;split.
   + cbn [cadd_remaining];eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
     * exact Selector.
     * eapply exec_statement_prefix_then_last;[exact Gap|exact Rest].
   + split;[exact Rep'|];eapply lframe_trans;[exact Frame1|].
     eapply lframe_trans;[exact Frame2|exact Frame3].
Qed.

Theorem exec_cadd_body flag rho beta e le m :
 rep rho beta (cadd_initial_regs++fst cadd_allocated) m ->
 tmatch rho beta (cadd_initial_temps flag) le -> ematch beta (snd cadd_allocated) e ->
 exists le' mf, Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_scalar_cadd_bit) E0 le' mf Out_normal /\
 rep rho beta (sregs (cadd_final_state flag)) mf /\
 lframe (fun b ofs=>~foot beta (map rshape (cadd_initial_regs++fst cadd_allocated)) b ofs) m mf.
Proof.
 intros Rep Temps Env.
 destruct (cadd_stmt_normal 200 (snd cadd_allocated) (cadd_initial_state flag)
  cadd_prefix_statement (cadd_prefix_state flag) (cadd_prefix_run_eq flag)
  rho beta e le m Rep Temps Env) as (le1 & m1 & Prefix & Rep1 & Temps1 & Frame1).
 rewrite <-cadd_checkpoint_first in Rep1,Temps1.
 destruct (exec_cadd_remaining 3 0 flag rho beta e le1 m1 eq_refl Rep1 Temps1 Env)
  as (le' & mf & Rest & Rep' & Frame2).
 exists le',mf;split.
 - rewrite cadd_body_remaining_source;eapply exec_statement_prefix_then_last;[exact Prefix|exact Rest].
 - split;[rewrite <-cadd_checkpoint_last;exact Rep'|].
   eapply lframe_trans;[exact Frame1|exact Frame2].
Qed.
