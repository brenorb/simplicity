(** Actual inverse post-update control, retaining the complete caller state. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem C.jet_sx_u64_transport.
Require Import C.jet_sx_region_lframe C.jet_sx_forget_cells C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_zero C.jet_secp_modinv_var_shorten.
Require Import C.jet_secp_modinv_var_post C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg.
Require Import C.jet_secp_modinfo_fe_global C.jet_secp_fe_nv C.jet_secp_modinv_normalize62_words.
Require Import C.jet_secp_statement_prefix C.jet_secp_modinv_de_exec C.jet_secp_modinv_de_numeric.
Require Import C.jet_secp_modinv_de_correction_numeric C.jet_secp_modinv_de_revalue C.jet_secp_fe_math.
Require Import C.jet_secp_modinv_normalize62_numeric C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_start.
Require Import C.jet_secp_modinv_fg_body.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition inv_control_view (rho : nat->int64) n :=
 if (5<=?n)%nat && (n<?15)%nat then rho (10+n)%nat else rho n.
Lemma inv_control_view_word rho (high : bool) j : (j<5)%nat ->
 inv_control_word (inv_control_view rho) high j=rho ((if high then 20 else 15)+j)%nat.
Proof. destruct high;destruct j as [|[|[|[|[|j]]]]];intro J;try lia;reflexivity. Qed.
Lemma inv_control_view_value len rho high : (0<len<=5)%nat ->
 inv_active_value len (inv_control_word (inv_control_view rho) high)=inv_fg_active_value len rho high.
Proof.
 intro Len;unfold inv_active_value,inv_fg_active_value;apply norm62_value_ext;intros i I.
 rewrite inv_control_view_word by lia;reflexivity.
Qed.
Theorem inv_control_project rho beta m : rep rho beta inv_loop_regs m ->
 rep (inv_control_view rho) beta inv_control_regs m.
Proof.
 intro Rep;pose proof Rep as (Len & Sep & Regions);split;[exact Len|];split.
 - eapply rsep_shape with (regs:=inv_loop_regs);[reflexivity|exact Sep].
 - intros r reg At;assert (R : (r<7)%nat) by
    (change (r<length inv_control_regs)%nat;apply nth_error_Some;rewrite At;discriminate).
   destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;
    cbn [inv_control_regs upd nth_error] in At;injection At as <-.
   + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=0%nat)
      (xs:=vars5 0) (ys:=vars5 0);try reflexivity;exact (Regions 0%nat _ eq_refl).
   + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=1%nat)
      (xs:=map XLc modinfo_fe_words) (ys:=map XLc modinfo_fe_words);try reflexivity;exact (Regions 1%nat _ eq_refl).
   + change (region_ok (inv_control_view rho) beta m 2 (forget_region (nth 2 inv_loop_regs (mkreg [] true None)))).
     eapply inv_region_undefined;[repeat constructor|apply forget_region_ok;exact (Regions 2%nat _ eq_refl)].
   + change (region_ok (inv_control_view rho) beta m 3 (forget_region (nth 3 inv_loop_regs (mkreg [] true None)))).
     eapply inv_region_undefined;[repeat constructor|apply forget_region_ok;exact (Regions 3%nat _ eq_refl)].
   + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=4%nat)
      (xs:=vars5 15) (ys:=vars5 5);try reflexivity;exact (Regions 4%nat _ eq_refl).
   + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=5%nat)
      (xs:=vars5 20) (ys:=vars5 10);try reflexivity;exact (Regions 5%nat _ eq_refl).
   + change (region_ok (inv_control_view rho) beta m 6 (forget_region (nth 6 inv_loop_regs (mkreg [] true None)))).
     eapply inv_region_undefined;[repeat constructor|apply forget_region_ok;exact (Regions 6%nat _ eq_refl)].
Qed.

Definition inv_tail_next_rho len (rho : nat->int64) n :=
 if (15<=?n)%nat && (n<?25)%nat then inv_post_next_rho len (inv_control_view rho) (n-10)%nat else rho n.
Definition inv_tail_length len rho := inv_post_length len (inv_control_view rho).
Lemma inv_tail_next_outside len rho n : ((n<15)%nat \/ (25<=n)%nat) -> inv_tail_next_rho len rho n=rho n.
Proof.
 intro Outside;unfold inv_tail_next_rho;destruct (Nat.leb_spec 15 n),(Nat.ltb_spec n 25);try lia;reflexivity.
Qed.
Lemma inv_tail_next_word len rho (high : bool) j : (j<5)%nat ->
 inv_tail_next_rho len rho ((if high then 20 else 15)+j)%nat=
 inv_control_word (inv_post_next_rho len (inv_control_view rho)) high j.
Proof. destruct high;destruct j as [|[|[|[|[|j]]]]];intro J;try lia;reflexivity. Qed.
Lemma inv_tail_next_value len rho high : (0<inv_tail_length len rho<=5)%nat ->
 inv_fg_active_value (inv_tail_length len rho) (inv_tail_next_rho len rho) high=
 inv_active_value (inv_tail_length len rho) (inv_control_word (inv_post_next_rho len (inv_control_view rho)) high).
Proof.
 intro Len;unfold inv_fg_active_value,inv_active_value;apply norm62_value_ext;intros i I.
 rewrite inv_tail_next_word by lia;reflexivity.
Qed.
Lemma inv_tail_restore_array len rho beta m (high : bool) :
 rep (inv_post_next_rho len (inv_control_view rho)) beta inv_control_regs m ->
 region_ok (inv_tail_next_rho len rho) beta m (if high then 5 else 4)
 (nth (if high then 5 else 4) inv_loop_regs (mkreg [] true None)).
Proof.
 intro Rep;destruct high.
 - eapply region_u64_transport with (rho:=inv_post_next_rho len (inv_control_view rho)) (beta:=beta)
    (r:=5%nat) (xs:=vars5 10) (ys:=vars5 20);try reflexivity;exact (rep_region _ _ _ _ 5 _ Rep eq_refl).
 - eapply region_u64_transport with (rho:=inv_post_next_rho len (inv_control_view rho)) (beta:=beta)
    (r:=4%nat) (xs:=vars5 5) (ys:=vars5 15);try reflexivity;exact (rep_region _ _ _ _ 4 _ Rep eq_refl).
Qed.
Theorem inv_tail_restore_caller len rho beta m mf : rep rho beta inv_loop_regs m ->
 rep (inv_post_next_rho len (inv_control_view rho)) beta inv_control_regs mf ->
 lframe (fun b _=>b<>blk beta 4 /\ b<>blk beta 5) m mf ->
 rep (inv_tail_next_rho len rho) beta inv_loop_regs mf.
Proof.
 intros Rep Updated Frame;pose proof (inv_loop_rep_distinct rho beta m Rep) as Distinct.
 pose proof (inv_tail_restore_array len rho beta mf false Updated) as F.
 pose proof (inv_tail_restore_array len rho beta mf true Updated) as G.
 destruct Rep as (Size & Sep & Regions);split;[exact Size|];split;[exact Sep|].
 assert (Outside : forall r,(r<7)%nat -> r<>4%nat -> r<>5%nat ->
  forall pos : Z,blk beta r<>blk beta 4 /\ blk beta r<>blk beta 5).
 { intros r R N4 N5 pos;split;apply Distinct;lia. }
 intros r reg At;assert (R : (r<7)%nat) by
  (change (r<length inv_loop_regs)%nat;apply nth_error_Some;rewrite At;discriminate).
 destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;
  cbn [inv_loop_regs nth_error] in At;injection At as <-.
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=0%nat) (xs:=vars5 0) (ys:=vars5 0);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply Outside;lia|exact (Regions 0%nat _ eq_refl)].
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=1%nat)
    (xs:=map XLc modinfo_fe_words) (ys:=map XLc modinfo_fe_words);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply Outside;lia|exact (Regions 1%nat _ eq_refl)].
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=2%nat) (xs:=vars5 5) (ys:=vars5 5);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply Outside;lia|exact (Regions 2%nat _ eq_refl)].
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=3%nat) (xs:=vars5 10) (ys:=vars5 10);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply Outside;lia|exact (Regions 3%nat _ eq_refl)].
 - exact F.
 - exact G.
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=6%nat)
    (xs:=[XLv 25;XLv 26;XLv 27;XLv 28]) (ys:=[XLv 25;XLv 26;XLv 27;XLv 28]);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply Outside;lia|exact (Regions 6%nat _ eq_refl)].
Qed.

Definition inv_tail_low_bounds len (rho : nat->int64) := forall (high : bool) j,(S j<len)%nat ->
 0<=Int64.signed (rho ((if high then 20 else 15)+j)%nat)<2^62.
Lemma inv_tail_view_bounds len rho : (0<len<=5)%nat -> inv_tail_low_bounds len rho ->
 forall high,inv_active_low_bounds len (inv_control_word (inv_control_view rho) high).
Proof. intros Len Bounds high j J;rewrite inv_control_view_word by lia;apply Bounds;exact J. Qed.
Theorem exec_inv_tail len rho beta e le m : (0<len<=5)%nat -> rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e -> le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 inv_tail_low_bounds len rho -> exists lef mf out,
 Clight2.exec_stmt secp_ge e le m inv_post_control E0 lef mf out /\
 rep (inv_tail_next_rho len rho) beta inv_loop_regs mf /\
 lef!_len=Some (Vint (Int.repr (Z.of_nat (inv_tail_length len rho)))) /\
 (forall high,inv_fg_active_value (inv_tail_length len rho) (inv_tail_next_rho len rho) high=
  inv_fg_active_value len rho high) /\
 inv_tail_low_bounds (inv_tail_length len rho) (inv_tail_next_rho len rho) /\
 (out=Out_break <-> inv_fg_active_value (inv_tail_length len rho) (inv_tail_next_rho len rho) true=0) /\
 (out=Out_normal -> inv_fg_active_value (inv_tail_length len rho) (inv_tail_next_rho len rho) true<>0) /\
 (out=Out_break \/ out=Out_normal) /\ (0<inv_tail_length len rho<=5)%nat /\
 inv_post_temp_frame le lef /\ lframe (fun b _=>b<>blk beta 4 /\ b<>blk beta 5) m mf.
Proof.
 intros Len Rep Env Length Bounds.
 destruct (exec_inv_post_ready len (inv_control_view rho) beta e le m Len (inv_control_project rho beta m Rep)
  (inv_control_temps_from_length _ _ _ _ Length) Env (inv_tail_view_bounds len rho Len Bounds))
  as (lef & mf & out & Exec & Out & Temps & Values & Stop & Nonzero & Outcomes & Range & TFrame & Frame).
 change (0<inv_tail_length len rho<=5)%nat in Range.
 assert (NewLength : lef!_len=Some (Vint (Int.repr (Z.of_nat (inv_tail_length len rho))))).
 { exact (Temps _len _ (PTree.gss _ _ _)). }
 assert (NextValues : forall high,
  inv_fg_active_value (inv_tail_length len rho) (inv_tail_next_rho len rho) high=inv_fg_active_value len rho high).
 { intro high;rewrite inv_tail_next_value by exact Range;unfold inv_tail_length;rewrite (proj1 (Values high)).
   apply inv_control_view_value;exact Len. }
 assert (NextLow : inv_tail_low_bounds (inv_tail_length len rho) (inv_tail_next_rho len rho)).
 { intros high j J;rewrite inv_tail_next_word by lia;apply (proj2 (Values high));exact J. }
 assert (NextStop : out=Out_break <-> inv_fg_active_value (inv_tail_length len rho) (inv_tail_next_rho len rho) true=0).
 { rewrite inv_tail_next_value by exact Range;exact Stop. }
 exists lef,mf,out;split;[exact Exec|];split;[eapply inv_tail_restore_caller;eassumption|];split;[exact NewLength|].
 split;[exact NextValues|];split;[exact NextLow|];split;[exact NextStop|];split.
 - intros Normal Zero;apply (proj2 NextStop) in Zero;congruence.
 - split;[exact Outcomes|];split;[exact Range|];split;assumption.
Qed.

Lemma inv_tail_de_unchanged len rho n : inv_de_rho (inv_tail_next_rho len rho) n=inv_de_rho rho n.
Proof.
 unfold inv_de_rho;destruct (Nat.ltb_spec n 10);
 rewrite inv_tail_next_outside by (first [left;lia|right;lia]);reflexivity.
Qed.

Lemma inv_fg_de_unchanged len rho n : inv_de_rho (inv_fg_next_rho len rho) n=inv_de_rho rho n.
Proof.
 unfold inv_de_rho;destruct (Nat.ltb_spec n 10);
 rewrite inv_fg_next_outside by (first [left;lia|right;lia]);reflexivity.
Qed.
Definition inv_iteration_updates len rho := inv_fg_next_rho len (inv_de_next_rho rho).
Definition inv_iteration_rho len rho := inv_tail_next_rho len (inv_iteration_updates len rho).
Definition inv_iteration_length len rho := inv_tail_length len (inv_iteration_updates len rho).
Lemma inv_iteration_de_word len rho n :
 inv_de_rho (inv_iteration_rho len rho) n=de62_next_rho (inv_de_rho rho) n.
Proof.
 unfold inv_iteration_rho,inv_iteration_updates;rewrite inv_tail_de_unchanged,inv_fg_de_unchanged.
 apply inv_de_next_project.
Qed.
Lemma inv_iteration_de_value len rho high : de62_input_value (inv_de_rho (inv_iteration_rho len rho)) high=
 de62_input_value (de62_next_rho (inv_de_rho rho)) high.
Proof.
 unfold de62_input_value;apply norm62_value_ext;intros i I;rewrite inv_iteration_de_word;reflexivity.
Qed.
Lemma inv_iteration_de_bounds len rho : de62_state_bounds (de62_next_rho (inv_de_rho rho)) ->
 de62_state_bounds (inv_de_rho (inv_iteration_rho len rho)).
Proof.
 intros (Limbs & Values);split.
 - intros high i I;unfold de62_array;rewrite inv_iteration_de_word;apply Limbs;exact I.
 - intro high;rewrite inv_iteration_de_value;apply Values.
Qed.

Definition inv_after_divsteps := Ssequence inv_de_statement (Ssequence inv_fg_statement inv_post_control).
Lemma inv_after_divsteps_source : inv_caller_loop_body=
 statement_sequence (firstn 2 (fst inv_caller_loop_parts)) inv_after_divsteps.
Proof. reflexivity. Qed.
Lemma exec_inv_updates_then_tail e le m lm mm lf mf out :
 Clight2.exec_stmt secp_ge e le m inv_update_calls E0 lm mm Out_normal ->
 Clight2.exec_stmt secp_ge e lm mm inv_post_control E0 lf mf out ->
 Clight2.exec_stmt secp_ge e le m inv_after_divsteps E0 lf mf out.
Proof.
 intros Updates Tail;unfold inv_update_calls in Updates;inversion Updates;subst;try contradiction.
 match goal with
 | H : ?t1 ** ?t2 = E0 |- _=>destruct (Eapp_E0_inv t1 t2 H) as [-> ->]
 | H : E0 = ?t1 ** ?t2 |- _=>destruct (Eapp_E0_inv t1 t2 (eq_sym H)) as [-> ->]
 end.
 unfold inv_after_divsteps;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
 - eassumption.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);eassumption.
Qed.

Theorem exec_inv_after_divsteps len rho beta e le m : (0<len<=5)%nat -> rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e ->
 le!_modinfo=Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
 le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 (forall high,de62_row_bound (inv_de_rho rho) high) -> de62_state_bounds (inv_de_rho rho) ->
 fg_input_bounds (inv_fg_rho len rho) -> exists lef mf out,
 Clight2.exec_stmt secp_ge e le m inv_after_divsteps E0 lef mf out /\
 rep (inv_iteration_rho len rho) beta inv_loop_regs mf /\
 lef!_len=Some (Vint (Int.repr (Z.of_nat (inv_iteration_length len rho)))) /\
 de62_state_bounds (inv_de_rho (inv_iteration_rho len rho)) /\
 (forall high,
  2^62*de62_input_value (inv_de_rho (inv_iteration_rho len rho)) high=de62_matrix_value (inv_de_rho rho) high+
   feP*de62_correction_value (inv_de_rho rho) high /\
  (2^62*de62_input_value (inv_de_rho (inv_iteration_rho len rho)) high-de62_matrix_value (inv_de_rho rho) high) mod feP=0) /\
 (forall high,inv_fg_active_value (inv_iteration_length len rho) (inv_iteration_rho len rho) high=
  fg_matrix_value (inv_fg_rho len (inv_de_next_rho rho)) high len/2^62) /\
 inv_tail_low_bounds (inv_iteration_length len rho) (inv_iteration_rho len rho) /\
 (out=Out_break <-> inv_fg_active_value (inv_iteration_length len rho) (inv_iteration_rho len rho) true=0) /\
 (out=Out_normal -> inv_fg_active_value (inv_iteration_length len rho) (inv_iteration_rho len rho) true<>0) /\
 (out=Out_break \/ out=Out_normal) /\ (0<inv_iteration_length len rho<=5)%nat /\
 inv_post_temp_frame le lef /\
 lframe (fun b ofs=>~foot (inv_de_layout beta) (map rshape de62_regs) b ofs /\
  ~foot (inv_fg_layout beta) (map rshape fg_regs) b ofs /\ b<>blk beta 4 /\ b<>blk beta 5) m mf.
Proof.
 intros Length Rep Env Modinfo Len Rows Bounds FG.
 destruct (exec_inv_update_calls len rho beta e le m Length Rep Env Modinfo Len Rows Bounds FG)
  as (mu & Updates & Updated & DEBounds & DENumeric & FGNumeric & Low & UFrame).
 destruct (exec_inv_tail len (inv_iteration_updates len rho) beta e le mu Length Updated Env Len Low)
  as (lef & mf & out & Tail & Out & NewLen & Values & NewLow & Stop & Nonzero & Outcomes & Range & TFrame & Frame).
 assert (FinalDE : de62_state_bounds (inv_de_rho (inv_iteration_rho len rho))).
 { apply inv_iteration_de_bounds;exact DEBounds. }
 assert (FinalDENumeric : forall high,
  2^62*de62_input_value (inv_de_rho (inv_iteration_rho len rho)) high=de62_matrix_value (inv_de_rho rho) high+
   feP*de62_correction_value (inv_de_rho rho) high /\
  (2^62*de62_input_value (inv_de_rho (inv_iteration_rho len rho)) high-de62_matrix_value (inv_de_rho rho) high) mod feP=0).
 { intro high;rewrite inv_iteration_de_value;apply DENumeric. }
 assert (FinalFG : forall high,inv_fg_active_value (inv_iteration_length len rho) (inv_iteration_rho len rho) high=
  fg_matrix_value (inv_fg_rho len (inv_de_next_rho rho)) high len/2^62).
 { intro high;unfold inv_iteration_length,inv_iteration_rho;rewrite (Values high);apply FGNumeric. }
 exists lef,mf,out;split;[eapply exec_inv_updates_then_tail;eassumption|].
 split;[exact Out|];split;[exact NewLen|];split;[exact FinalDE|];split;[exact FinalDENumeric|].
 split;[exact FinalFG|];split;[exact NewLow|];split;[exact Stop|];split;[exact Nonzero|].
 split;[exact Outcomes|];split;[exact Range|];split;[exact TFrame|].
 eapply lframe_trans.
 - eapply lframe_implies;[exact UFrame|intros b ofs (D & F & Outside) _;split;assumption].
 - eapply lframe_implies;[exact Frame|intros b ofs (D & F & Outside) _;exact Outside].
Qed.
