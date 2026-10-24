(** Termination and complete execution of the original scalar inverse loop.
    The original CTZ helper's execution remains an explicit INTERNAL premise
    at each memory. No new external model or public acceptance is introduced. *)
From Coq Require Import ZArith List Lia Arith.Wf_nat.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.extraMath C.divstep C.jet_sx_state C.jet_sx_eval C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_divstep_bounds C.jet_secp_divstep_termination
 C.jet_secp_scalar_inverse_result C.jet_secp_scalar_inverse_batch C.jet_secp_scalar_inverse_seed
 C.jet_secp_signed62_numeric
 C.jet_secp_modinv_loop_modulus C.jet_secp_modinv_seed_modulus C.jet_secp_modinv_batch_modulus
 C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg
 C.jet_secp_modinv_var_zero C.jet_secp_modinv_var_shorten C.jet_secp_modinv_var_post
 C.jet_secp_modinv_var_tail C.jet_secp_modinv_var_invariant C.jet_secp_modinv_var_ranges
 C.jet_secp_scalar_de_ranges C.jet_secp_scalar_de_invariant C.jet_secp_scalar_normalize62
 C.jet_secp_modinv_de_numeric C.jet_secp_canonical_scalar.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition scalar_inv_trajectory value n :=
 fst(stepN n (init canonical_group_order value scalar_inv_modulus_odd)).
Definition scalar_inv_loop_temps (le lef : temp_env) := forall id,
 id<>_eta -> id<>_t'1 -> id<>_t'7 -> id<>_t'8 -> ~In id inv_post_modified -> lef!id=le!id.
Definition scalar_inv_loop_ready value n beta e le m len rho :=
 (0<len<=5)%nat /\ rep rho beta (inv_mod_seed_regs modinfo_scalar_limb) m /\
 ematch beta (snd inv_start_alloc) e /\
 le!_eta=Some(Vlong(Int64.repr(eta(scalar_inv_trajectory value n)))) /\
 le!_modinfo=Some(Vptr(blk beta 1)(Ptrofs.repr(bas beta 1))) /\
 le!_len=Some(Vint(Int.repr(Z.of_nat len))) /\
 scalar_de62_state_bounds(inv_de_rho rho) /\ inv_state_matches len rho (scalar_inv_trajectory value n) /\
 scalar_de62_coefficient_link value (inv_de_rho rho) (scalar_inv_trajectory value n) /\
 inv_fg_limb_bounds rho /\ inv_fg_value_capacity len rho /\
 (value=0 -> de62_input_value(inv_de_rho rho) false mod canonical_group_order=0) /\
 (n=0%nat \/ g(scalar_inv_trajectory value n)<>0).
Definition scalar_inv_loop_done value n beta le m len rho :=
 (0<len<=5)%nat /\ rep rho beta (inv_mod_loop_regs modinfo_scalar_limb) m /\
 le!_eta=Some(Vlong(Int64.repr(eta(scalar_inv_trajectory value n)))) /\
 le!_len=Some(Vint(Int.repr(Z.of_nat len))) /\
 scalar_de62_state_bounds(inv_de_rho rho) /\ inv_state_matches len rho (scalar_inv_trajectory value n) /\
 scalar_de62_coefficient_link value (inv_de_rho rho) (scalar_inv_trajectory value n) /\
 inv_fg_limb_bounds rho /\ inv_fg_value_capacity len rho /\ inv_tail_low_bounds len rho /\
 (value=0 -> de62_input_value(inv_de_rho rho) false mod canonical_group_order=0) /\
 g(scalar_inv_trajectory value n)=0.

Lemma scalar_inv_trajectory_batch value n :
 fst(stepN 62 (scalar_inv_trajectory value n))=scalar_inv_trajectory value (62+n)%nat.
Proof. symmetry;apply stepN_app_fst. Qed.
Lemma scalar_inv_trajectory_zero value n : value=0 -> g(scalar_inv_trajectory value n)=0.
Proof. intros ->;apply fixed_g;reflexivity. Qed.
Lemma scalar_inv_loop_eta value n : 0<=value<canonical_group_order ->
 (n=0%nat \/ g(scalar_inv_trajectory value n)<>0) ->
 -683<=eta(scalar_inv_trajectory value n)<683.
Proof.
 intros Range Live.
 pose proof(inv_256_batch_eta_safe (init canonical_group_order value scalar_inv_modulus_odd)
  n 0 eq_refl
  ltac:(change(Z.abs canonical_group_order<=2^256);rewrite Z.abs_eq by(unfold canonical_group_order;lia);
    unfold canonical_group_order;lia)
  ltac:(change(Z.abs value<=2^256);rewrite Z.abs_eq by lia;unfold canonical_group_order in *;lia)
  Live ltac:(lia)) as Bounds.
 change(-320<=eta(scalar_inv_trajectory value n)<320) in Bounds;lia.
Qed.

Section COUNT_CALL_BOUNDARY.
Hypothesis CountCall : forall m x,Int64.unsigned x<>0 ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ctz64_var) [Vlong x]
  E0 m (Vint(Int.repr(Z_ctz(Int64.unsigned x)))).

Theorem exec_scalar_inv_loop_fuel fuel : forall value n beta e le m len rho,
 0<=value<canonical_group_order -> scalar_inv_loop_ready value n beta e le m len rho ->
 g(scalar_inv_trajectory value (62*fuel+n)%nat)=0 -> exists nf lenf rhof lef mf,
 Clight2.exec_stmt secp_ge e le m inv_caller_loop E0 lef mf Out_normal /\
 (n+62<=nf)%nat /\ scalar_inv_loop_done value nf beta lef mf lenf rhof /\
 scalar_inv_loop_temps le lef /\ lframe(scalar_inv_batch_frame beta) m mf.
Proof.
 induction fuel using lt_wf_ind;intros value n beta e le m len rho Range
  (Length & Rep & Env & Eta & Modinfo & Len & DE & State & Link & Limbs & Capacity & Zero & Live) Terminal.
 destruct(exec_scalar_inv_batch value len rho (scalar_inv_trajectory value n) beta e le m
  (CountCall m) (scalar_inv_loop_eta value n Range Live) Length Rep Env Eta Modinfo Len DE State Link Limbs Capacity)
  as(le1 & m1 & out & Body & Post & NewLen & NewEta & NewDE & NewLink & NewState & NewLimbs & NewCapacity &
   Low & BatchZero & Stop & Outcomes & NewLength & Temps & Frame).
 rewrite scalar_inv_trajectory_batch in NewEta,NewLink,NewState,Stop.
 set (r:=scalar_inv_batch_rho len (scalar_inv_trajectory value n) rho) in *.
 set (l:=scalar_inv_batch_length len (scalar_inv_trajectory value n) rho) in *.
 assert(NextZero:value=0 -> de62_input_value(inv_de_rho r) false mod canonical_group_order=0).
 { intro Z;destruct(BatchZero (scalar_inv_trajectory_zero value n Z)) as(_ & D);rewrite D;apply Zero;exact Z. }
 destruct Outcomes as[Break|Normal];subst out.
 - exists (62+n)%nat,l,r,le1,m1;split.
   + rewrite inv_caller_loop_source;eapply exec_Sloop_stop1;[exact Body|constructor].
   + split;[lia|];split.
     * unfold scalar_inv_loop_done;split;[exact NewLength|];split;[exact Post|];split;[exact NewEta|];
       split;[exact NewLen|];split;[exact NewDE|];split;[exact NewState|];split;[exact NewLink|];
       split;[exact NewLimbs|];split;[exact NewCapacity|];split;[exact Low|];split;[exact NextZero|].
       apply Stop;reflexivity.
     * split;[exact Temps|exact Frame].
 - assert(NextLive:g(scalar_inv_trajectory value (62+n)%nat)<>0).
   { intro Z;apply Stop in Z;discriminate Z. }
   destruct fuel as[|fuel].
   + change(g(scalar_inv_trajectory value n)=0) in Terminal.
     destruct(BatchZero Terminal) as[Impossible _];discriminate Impossible.
   + assert(Next:scalar_inv_loop_ready value (62+n)%nat beta e le1 m1 l r).
     { unfold scalar_inv_loop_ready;split;[exact NewLength|];split;[apply inv_mod_pre_batch_forget;exact Post|];
       split;[exact Env|];split;[exact NewEta|];split.
       - rewrite(Temps _modinfo) by(unfold inv_post_modified,inv_test_modified,inv_shorten_modified;
         cbn [app In];intuition discriminate);exact Modinfo.
       - split;[exact NewLen|];split;[exact NewDE|];split;[exact NewState|];split;[exact NewLink|];
         split;[exact NewLimbs|];split;[exact NewCapacity|];split;[exact NextZero|right;exact NextLive]. }
     assert(NextTerminal:g(scalar_inv_trajectory value (62*fuel+(62+n))%nat)=0).
     { replace(62*fuel+(62+n))%nat with(62*S fuel+n)%nat by lia;exact Terminal. }
     destruct(H fuel ltac:(lia) value (62+n)%nat beta e le1 m1 l r Range Next NextTerminal)
      as(nf & lenf & rhof & lef & mf & Repeat & Progress & Done & TFrame & MFrame).
     exists nf,lenf,rhof,lef,mf;split.
     * rewrite inv_caller_loop_source in Repeat |- *.
       eapply exec_Sloop_loop with(t1:=E0)(t2:=E0)(t3:=E0)(le1:=le1)(le2:=le1)
        (m1:=m1)(m2:=m1)(out1:=Out_normal);[exact Body|constructor|constructor|exact Repeat].
     * split;[lia|];split;[exact Done|];split.
       -- intros id E T1 T7 T8 Outside;rewrite(TFrame id E T1 T7 T8 Outside);apply Temps;assumption.
       -- eapply lframe_trans;[exact Frame|exact MFrame].
Qed.

Theorem exec_scalar_inv_loop value n beta e le m len rho : 0<=value<canonical_group_order ->
 scalar_inv_loop_ready value n beta e le m len rho -> exists nf lenf rhof lef mf,
 Clight2.exec_stmt secp_ge e le m inv_caller_loop E0 lef mf Out_normal /\
 (n+62<=nf)%nat /\ scalar_inv_loop_done value nf beta lef mf lenf rhof /\
 scalar_inv_loop_temps le lef /\ lframe(scalar_inv_batch_frame beta) m mf.
Proof.
 intros Range Ready.
 destruct(inv_divstep_batches_terminate (scalar_inv_trajectory value n)) as[fuel Terminal].
 unfold scalar_inv_trajectory in Terminal;rewrite <-stepN_app_fst in Terminal.
 exact(exec_scalar_inv_loop_fuel fuel value n beta e le m len rho Range Ready Terminal).
Qed.
End COUNT_CALL_BOUNDARY.

(** Discharge the loop's initial numeric invariant from the already proved
    real initialization/copy state. No initialized matrix is required. *)
Lemma scalar_inv_seed_ready w beta e le m : signed62_normalized w ->
 rep (inv_mod_seed_rho modinfo_scalar_limb w) beta (inv_mod_seed_regs modinfo_scalar_limb) m ->
 ematch beta (snd inv_start_alloc) e -> le!_eta=Some(Vlong(Int64.repr(-1))) ->
 le!_modinfo=Some(Vptr(blk beta 1)(Ptrofs.repr(bas beta 1))) -> le!_len=Some(Vint(Int.repr 5)) ->
 scalar_inv_loop_ready (signed62_unsigned_value w) 0 beta e le m 5 (inv_mod_seed_rho modinfo_scalar_limb w).
Proof.
 intros Normal Rep Env Eta Modinfo Len.
 destruct(scalar_inv_represented_seed_bounds w Normal) as(DE & Link & State & Limbs & Capacity & Zero).
 unfold scalar_inv_loop_ready;split;[lia|];split;[exact Rep|];split;[exact Env|];
 split;[exact Eta|];split;[exact Modinfo|];split;[exact Len|];split;[exact DE|];
 split;[exact State|];split;[exact Link|];split;[exact Limbs|];split;[exact Capacity|];
 split;[intros;exact Zero|left;reflexivity].
Qed.
