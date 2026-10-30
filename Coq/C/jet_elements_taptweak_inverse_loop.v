(** Complete linked inverse loop; original trajectory and termination reused. *)
From Coq Require Import ZArith List Lia Arith.Wf_nat.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.extraMath C.divstep C.jet_sx_state C.jet_sx_eval C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_divstep_bounds C.jet_secp_divstep_termination
 C.jet_secp_fe_inverse_batch C.jet_secp_modinv_var_seed C.jet_secp_modinfo_fe_copy C.jet_secp_fe_math
 C.jet_secp_modinv_loop_modulus C.jet_secp_modinv_seed_modulus C.jet_secp_modinv_batch_modulus
 C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg
 C.jet_secp_modinv_var_zero C.jet_secp_modinv_var_shorten C.jet_secp_modinv_var_post
 C.jet_secp_modinv_var_tail C.jet_secp_modinv_var_invariant C.jet_secp_modinv_var_ranges
 C.jet_secp_modinv_var_batch_update C.jet_secp_modinv_de_numeric C.jet_secp_signed62_numeric
 C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_fe_inverse_loop C.jet_elements_taptweak_pure C.jet_ctz_model.
Require Import C.jet_elements_taptweak_inverse_batch.
Local Opaque secp_ge elements_taptweak_ge.

Section LINKED_LOOP.
Variable Model:ctz_model.
Theorem exec_elements_taptweak_field_inv_loop_fuel fuel : forall value n beta e le m len rho,
 0<=value<feP -> field_inv_loop_ready value n beta e le m len rho ->
 g(field_inv_trajectory value(62*fuel+n)%nat)=0 -> exists nf lenf rhof lef mf,
 Clight2.exec_stmt elements_taptweak_ge e le m inv_caller_loop E0 lef mf Out_normal /\
 (n+62<=nf)%nat /\ field_inv_loop_done value nf beta lef mf lenf rhof /\
 field_inv_loop_temps le lef /\ lframe(field_inv_batch_frame beta) m mf /\ readonly_preserved m mf.
Proof.
 induction fuel using lt_wf_ind;intros value n beta e le m len rho Range
  (Length & Rep & Env & Eta & Modinfo & Len & DE & State & Link & Limbs & Capacity & Zero & Live) Terminal.
 destruct(exec_elements_taptweak_field_inv_batch Model value len rho(field_inv_trajectory value n) beta e le m
  (field_inv_loop_eta value n Range Live) Length Rep Env Eta Modinfo Len DE State Link Limbs Capacity)
  as(le1 & m1 & out & Body & Post & NewLen & NewEta & NewDE & NewLink & NewState & NewLimbs & NewCapacity &
   Low & BatchZero & Stop & Outcomes & NewLength & Temps & Frame & Readonly).
 rewrite field_inv_trajectory_batch in NewEta,NewState,Stop.
 set(r:=inv_batch_next_rho len(field_inv_trajectory value n)rho) in *.
 set(l:=inv_batch_next_length len(field_inv_trajectory value n)rho) in *.
 assert(NextZero:value=0 -> de62_input_value(inv_de_rho r) false mod feP=0).
 { intro Z;destruct(BatchZero(field_inv_trajectory_zero value n Z)) as(_ & D);rewrite D;apply Zero;exact Z. }
 destruct Outcomes as[Break|Normal];subst out.
 - exists(62+n)%nat,l,r,le1,m1;split.
   + rewrite inv_caller_loop_source;eapply exec_Sloop_stop1;[exact Body|constructor].
   + split;[lia|];split.
     * unfold field_inv_loop_done;split;[exact NewLength|];split;[exact Post|];split;[exact NewEta|];
       split;[exact NewLen|];split;[exact NewDE|];split;[exact NewState|];split;[exact NewLink|];
       split;[exact NewLimbs|];split;[exact NewCapacity|];split;[exact Low|];split;[exact NextZero|].
       apply Stop;reflexivity.
     * split;[exact Temps|];split;[exact Frame|exact Readonly].
 - assert(NextLive:g(field_inv_trajectory value(62+n)%nat)<>0).
   { intro Z;apply Stop in Z;discriminate Z. }
   destruct fuel as[|fuel].
   + change(g(field_inv_trajectory value n)=0) in Terminal.
     destruct(BatchZero Terminal) as[Impossible _];discriminate Impossible.
   + assert(Next:field_inv_loop_ready value(62+n)%nat beta e le1 m1 l r).
     { unfold field_inv_loop_ready;split;[exact NewLength|];split.
       - apply inv_mod_pre_batch_forget;rewrite inv_mod_loop_field;exact Post.
       - split;[exact Env|];split;[exact NewEta|];split.
         + rewrite(Temps _modinfo) by(unfold inv_post_modified,inv_test_modified,inv_shorten_modified;
           cbn [app In];intuition discriminate);exact Modinfo.
         + split;[exact NewLen|];split;[exact NewDE|];split;[exact NewState|];split;[exact NewLink|];
           split;[exact NewLimbs|];split;[exact NewCapacity|];split;[exact NextZero|right;exact NextLive]. }
     assert(NextTerminal:g(field_inv_trajectory value(62*fuel+(62+n))%nat)=0).
     { replace(62*fuel+(62+n))%nat with(62*S fuel+n)%nat by lia;exact Terminal. }
     destruct(H fuel ltac:(lia) value(62+n)%nat beta e le1 m1 l r Range Next NextTerminal)
      as(nf & lenf & rhof & lef & mf & Repeat & Progress & Done & TFrame & MFrame & RReadonly).
     exists nf,lenf,rhof,lef,mf;split.
     * rewrite inv_caller_loop_source in Repeat |- *.
       eapply exec_Sloop_loop with(t1:=E0)(t2:=E0)(t3:=E0)(le1:=le1)(le2:=le1)
        (m1:=m1)(m2:=m1)(out1:=Out_normal);[exact Body|constructor|constructor|exact Repeat].
     * split;[lia|];split;[exact Done|];split.
       -- intros id E T1 T7 T8 Outside;rewrite(TFrame id E T1 T7 T8 Outside);apply Temps;assumption.
       -- split;[eapply lframe_trans;[exact Frame|exact MFrame]|eapply preserved_trans;[exact Readonly|exact RReadonly]].
Qed.

Theorem exec_elements_taptweak_field_inv_loop value n beta e le m len rho : 0<=value<feP ->
 field_inv_loop_ready value n beta e le m len rho -> exists nf lenf rhof lef mf,
 Clight2.exec_stmt elements_taptweak_ge e le m inv_caller_loop E0 lef mf Out_normal /\
 (n+62<=nf)%nat /\ field_inv_loop_done value nf beta lef mf lenf rhof /\
 field_inv_loop_temps le lef /\ lframe(field_inv_batch_frame beta) m mf /\ readonly_preserved m mf.
Proof.
 intros Range Ready.
 destruct(inv_divstep_batches_terminate(field_inv_trajectory value n)) as[fuel Terminal].
 apply(exec_elements_taptweak_field_inv_loop_fuel fuel value n beta e le m len rho Range Ready).
 unfold field_inv_trajectory in *;rewrite <-stepN_app_fst in Terminal;exact Terminal.
Qed.
End LINKED_LOOP.
