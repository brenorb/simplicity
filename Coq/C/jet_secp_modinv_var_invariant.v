(** Preserve the input/coefficient invariant through the actual inverse suffix. *)
From Coq Require Import ZArith ZArith.Znumtheory List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_de.
Require Import C.jet_secp_modinv_var_fg C.jet_secp_modinv_var_tail C.jet_secp_modinv_var_post.
Require Import C.jet_secp_modinv_de_exec C.jet_secp_modinv_de_numeric C.jet_secp_modinv_de_correction_numeric.
Require Import C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_body C.jet_secp_modinv_fg_start.
Require Import C.jet_secp_modinv_fg_loop_numeric C.jet_secp_modinv_fg_iteration_numeric.
Require Import C.jet_secp_modinv_normalize62_words C.jet_secp_fe_math.
Require Import C.divstep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma inv_field_modulus_nonzero : feP<>0.
Proof. unfold feP,feR;lia. Qed.
Lemma inv_batch_coprime : rel_prime feP (2^62).
Proof. apply Zgcd_1_rel_prime;vm_compute;reflexivity. Qed.
Lemma inv_cancel_batch a b : (2^62*a) mod feP=(2^62*b) mod feP -> a mod feP=b mod feP.
Proof.
 intro Same.
 assert (Divide : (feP | 2^62*(a-b))).
 { apply Z.mod_divide;[exact inv_field_modulus_nonzero|].
   replace (2^62*(a-b)) with (2^62*a-2^62*b) by ring.
   rewrite Zminus_mod,Same,Z.sub_diag,Zmod_0_l;reflexivity. }
 destruct (Gauss feP (2^62) (a-b) Divide inv_batch_coprime) as (k & Equal).
 replace a with (b+k*feP) by lia;apply Z_mod_plus_full.
Qed.
Lemma inv_linear_mod value d e f g u v : (value*d) mod feP=f mod feP ->
 (value*e) mod feP=g mod feP ->
 (value*(u*d+v*e)) mod feP=(u*f+v*g) mod feP.
Proof.
 intros D E.
 assert (U : (u*(value*d)) mod feP=(u*f) mod feP).
 { rewrite <-(Zmult_mod_idemp_r (value*d) u feP),D,Zmult_mod_idemp_r;reflexivity. }
 assert (V : (v*(value*e)) mod feP=(v*g) mod feP).
 { rewrite <-(Zmult_mod_idemp_r (value*e) v feP),E,Zmult_mod_idemp_r;reflexivity. }
 replace (value*(u*d+v*e)) with (u*(value*d)+v*(value*e)) by ring.
 rewrite (Zplus_mod (u*(value*d)) (v*(value*e)) feP),U,V,<-Zplus_mod;reflexivity.
Qed.
Lemma inv_scaled_coefficient value dnew fnew drow frow correction :
 2^62*dnew=drow+feP*correction -> 2^62*fnew=frow ->
 (value*drow) mod feP=frow mod feP -> (value*dnew) mod feP=fnew mod feP.
Proof.
 intros DE FG Link;apply inv_cancel_batch.
 replace (2^62*(value*dnew)) with (value*(2^62*dnew)) by ring;rewrite DE.
 replace (value*(drow+feP*correction)) with (value*drow+(value*correction)*feP) by ring.
 rewrite Z_mod_plus_full,Link,FG;reflexivity.
Qed.

Definition inv_coefficient_link value len rho := forall high,
 (value*de62_input_value (inv_de_rho rho) high) mod feP=inv_fg_active_value len rho high mod feP.
Lemma inv_fg_input_value len rho high : (0<len<=5)%nat ->
 fg_input_value (inv_fg_rho len rho) high len=inv_fg_active_value len rho high.
Proof.
 intro Len;unfold fg_input_value,inv_fg_active_value;apply norm62_value_ext;intros i I.
 destruct high;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity.
Qed.
Lemma inv_fg_value_after_de len rho high : (0<len<=5)%nat ->
 inv_fg_active_value len (inv_de_next_rho rho) high=inv_fg_active_value len rho high.
Proof.
 intro Len;unfold inv_fg_active_value;apply norm62_value_ext;intros i I.
 rewrite inv_de_next_outside by (right;destruct high;lia);reflexivity.
Qed.
Definition inv_matrix_u rho (high : bool) := Int64.signed (inv_de_rho rho (if high then 12%nat else 10%nat)).
Definition inv_matrix_v rho (high : bool) := Int64.signed (inv_de_rho rho (if high then 13%nat else 11%nat)).
Lemma inv_fg_matrix_value len rho high : (0<len<=5)%nat ->
 fg_matrix_value (inv_fg_rho len (inv_de_next_rho rho)) high len=
 inv_matrix_u rho high*inv_fg_active_value len rho false+
 inv_matrix_v rho high*inv_fg_active_value len rho true.
Proof.
 intro Len;unfold fg_matrix_value;rewrite !inv_fg_input_value by exact Len.
 rewrite !inv_fg_value_after_de by exact Len;destruct high;reflexivity.
Qed.
Definition inv_matrix_divisible len rho := forall high,
 (2^62 | fg_matrix_value (inv_fg_rho len (inv_de_next_rho rho)) high len).

Lemma inv_iteration_link value len rho : (0<len<=5)%nat -> inv_coefficient_link value len rho ->
 inv_matrix_divisible len rho ->
 (forall high,2^62*de62_input_value (inv_de_rho (inv_iteration_rho len rho)) high=
  de62_matrix_value (inv_de_rho rho) high+feP*de62_correction_value (inv_de_rho rho) high) ->
 (forall high,inv_fg_active_value (inv_iteration_length len rho) (inv_iteration_rho len rho) high=
  fg_matrix_value (inv_fg_rho len (inv_de_next_rho rho)) high len/2^62) ->
 inv_coefficient_link value (inv_iteration_length len rho) (inv_iteration_rho len rho).
Proof.
 intros Len Link Divisible DE FG high.
 eapply inv_scaled_coefficient;[apply DE| |].
 - rewrite FG;symmetry;apply Zdivide_Zdiv_eq;[lia|apply Divisible].
 - rewrite inv_fg_matrix_value by exact Len.
   change ((value*(inv_matrix_u rho high*de62_input_value (inv_de_rho rho) false+
    inv_matrix_v rho high*de62_input_value (inv_de_rho rho) true)) mod feP=
    (inv_matrix_u rho high*inv_fg_active_value len rho false+
     inv_matrix_v rho high*inv_fg_active_value len rho true) mod feP).
   apply inv_linear_mod;[apply Link|apply Link].
Qed.

Definition inv_state_matches len rho st := f st=inv_fg_active_value len rho false /\
 g st=inv_fg_active_value len rho true.
Definition inv_matrix_matches rho st :=
 inv_matrix_u rho false=Trans.u (Trans.transN 62 st) /\
 inv_matrix_v rho false=Trans.v (Trans.transN 62 st) /\
 inv_matrix_u rho true=Trans.q (Trans.transN 62 st) /\
 inv_matrix_v rho true=Trans.r (Trans.transN 62 st).
Lemma inv_matrix_row_bounds rho st : inv_matrix_matches rho st ->
 forall high,de62_row_bound (inv_de_rho rho) high.
Proof.
 intros (U & V & Q & R) high.
 pose proof (Trans.bounded_transN 62 st) as Bound;unfold Trans.bounded in Bound.
 change (Z.of_nat 62) with 62 in Bound.
 change (Z.abs (inv_matrix_u rho high)+Z.abs (inv_matrix_v rho high)<=2^62).
 destruct high;[rewrite Q,R|rewrite U,V];lia.
Qed.
Lemma inv_fg_bounds_from_matrix len rho st : inv_matrix_matches rho st ->
 (forall high j,(j<5)%nat ->
  Z.abs (Int64.signed (fg_array_word (inv_fg_rho len rho) high j))<=2^62) ->
 fg_input_bounds (inv_fg_rho len rho).
Proof.
 intros Matrix Limbs;split;[|exact Limbs].
 intro high;pose proof (inv_matrix_row_bounds rho st Matrix high) as Row.
 destruct high;exact Row.
Qed.
Lemma inv_matrix_scaled_state len rho st high : (0<len<=5)%nat ->
 inv_state_matches len rho st -> inv_matrix_matches rho st ->
 fg_matrix_value (inv_fg_rho len (inv_de_next_rho rho)) high len=
 2^62*(if high then g (fst (stepN 62 st)) else f (fst (stepN 62 st))).
Proof.
 intros Len (F & G) (U & V & Q & R);rewrite inv_fg_matrix_value by exact Len.
 destruct high.
 - rewrite Q,R,<-F,<-G;pose proof (f_equal Trans.y (Trans.transN_step 62 st)) as Row.
   change (2^62*g (fst (stepN 62 st))=Trans.q (Trans.transN 62 st)*f st+Trans.r (Trans.transN 62 st)*g st) in Row.
   symmetry;exact Row.
 - rewrite U,V,<-F,<-G;pose proof (f_equal Trans.x (Trans.transN_step 62 st)) as Row.
   change (2^62*f (fst (stepN 62 st))=Trans.u (Trans.transN 62 st)*f st+Trans.v (Trans.transN 62 st)*g st) in Row.
   symmetry;exact Row.
Qed.
Lemma inv_matrix_divisible_from_steps len rho st : (0<len<=5)%nat ->
 inv_state_matches len rho st -> inv_matrix_matches rho st -> inv_matrix_divisible len rho.
Proof.
 intros Len State Matrix high;rewrite (inv_matrix_scaled_state len rho st high Len State Matrix).
 exists (if high then g (fst (stepN 62 st)) else f (fst (stepN 62 st)));ring.
Qed.
Lemma inv_iteration_state_from_steps len rho st : (0<len<=5)%nat ->
 inv_state_matches len rho st -> inv_matrix_matches rho st ->
 (forall high,inv_fg_active_value (inv_iteration_length len rho) (inv_iteration_rho len rho) high=
  fg_matrix_value (inv_fg_rho len (inv_de_next_rho rho)) high len/2^62) ->
 inv_state_matches (inv_iteration_length len rho) (inv_iteration_rho len rho) (fst (stepN 62 st)).
Proof.
 intros Len State Matrix FG;split;rewrite FG, (inv_matrix_scaled_state len rho st _ Len State Matrix);
 rewrite Z.mul_comm,Z.div_mul by lia;reflexivity.
Qed.

Lemma inv_zero_matrix_row rho st : g st=0 -> inv_matrix_matches rho st ->
 inv_matrix_u rho false=2^62 /\ inv_matrix_v rho false=0.
Proof.
 intros Zero (U & V & Q & R).
 pose proof (Trans.transHs 62 st ltac:(rewrite Zero;exists 0;ring)) as Matrix.
 rewrite Matrix in U,V;split;assumption.
Qed.

Lemma inv_zero_iteration_coefficient len rho st : g st=0 -> inv_matrix_matches rho st ->
 2^62*de62_input_value (inv_de_rho (inv_iteration_rho len rho)) false=
  de62_matrix_value (inv_de_rho rho) false+feP*de62_correction_value (inv_de_rho rho) false ->
 de62_input_value (inv_de_rho (inv_iteration_rho len rho)) false mod feP=
  de62_input_value (inv_de_rho rho) false mod feP.
Proof.
 intros Zero Matrix Update.
 destruct (inv_zero_matrix_row rho st Zero Matrix) as (U & V).
 change (2^62*de62_input_value (inv_de_rho (inv_iteration_rho len rho)) false=
  inv_matrix_u rho false*de62_input_value (inv_de_rho rho) false+
  inv_matrix_v rho false*de62_input_value (inv_de_rho rho) true+
  feP*de62_correction_value (inv_de_rho rho) false) in Update.
 rewrite U,V,Z.mul_0_l,Z.add_0_r in Update;apply inv_cancel_batch.
 rewrite Update,(Z.mul_comm feP (de62_correction_value (inv_de_rho rho) false));apply Z_mod_plus_full.
Qed.

Theorem exec_inv_after_divsteps_invariant value len rho st beta e le m :
 (0<len<=5)%nat -> rep rho beta inv_loop_regs m -> ematch beta (snd inv_start_alloc) e ->
 le!_modinfo=Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
 le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 de62_state_bounds (inv_de_rho rho) ->
 (forall high j,(j<5)%nat ->
  Z.abs (Int64.signed (fg_array_word (inv_fg_rho len rho) high j))<=2^62) ->
 inv_coefficient_link value len rho ->
 inv_state_matches len rho st -> inv_matrix_matches rho st -> exists lef mf out,
 Clight2.exec_stmt secp_ge e le m inv_after_divsteps E0 lef mf out /\
 rep (inv_iteration_rho len rho) beta inv_loop_regs mf /\
 lef!_len=Some (Vint (Int.repr (Z.of_nat (inv_iteration_length len rho)))) /\
 de62_state_bounds (inv_de_rho (inv_iteration_rho len rho)) /\
 inv_coefficient_link value (inv_iteration_length len rho) (inv_iteration_rho len rho) /\
 inv_state_matches (inv_iteration_length len rho) (inv_iteration_rho len rho) (fst (stepN 62 st)) /\
 (g st=0 -> out=Out_break /\
  de62_input_value (inv_de_rho (inv_iteration_rho len rho)) false mod feP=
   de62_input_value (inv_de_rho rho) false mod feP) /\
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
 intros Len Rep Env Modinfo Length Bounds FGLimbs Link State Matrix.
 pose proof (inv_matrix_row_bounds rho st Matrix) as Rows.
 pose proof (inv_fg_bounds_from_matrix len rho st Matrix FGLimbs) as FG.
 destruct (exec_inv_after_divsteps len rho beta e le m Len Rep Env Modinfo Length Rows Bounds FG)
  as (lef & mf & out & Exec & Out & NewLen & DEBounds & DENumeric & FGNumeric & Low & Stop & Nonzero & Outcomes & Range & TFrame & Frame).
 assert (NextLink : inv_coefficient_link value (inv_iteration_length len rho) (inv_iteration_rho len rho)).
 { apply inv_iteration_link;[exact Len|exact Link|apply (inv_matrix_divisible_from_steps len rho st Len State Matrix)| |exact FGNumeric].
   intro high;exact (proj1 (DENumeric high)). }
 assert (NextState : inv_state_matches (inv_iteration_length len rho) (inv_iteration_rho len rho) (fst (stepN 62 st))).
 { apply inv_iteration_state_from_steps;assumption. }
 assert (ZeroResult : g st=0 -> out=Out_break /\
  de62_input_value (inv_de_rho (inv_iteration_rho len rho)) false mod feP=
   de62_input_value (inv_de_rho rho) false mod feP).
 { intro Zero;split.
   - apply (proj2 Stop);rewrite <-(proj2 NextState);apply fixed_g;exact Zero.
   - exact (inv_zero_iteration_coefficient len rho st Zero Matrix (proj1 (DENumeric false))). }
 exists lef,mf,out;split;[exact Exec|];split;[exact Out|];split;[exact NewLen|];split;[exact DEBounds|].
 split;[exact NextLink|];split;[exact NextState|];split;[exact ZeroResult|];
 split;[exact DENumeric|];split;[exact FGNumeric|].
 split;[exact Low|];split;[exact Stop|];split;[exact Nonzero|];split;[exact Outcomes|].
 split;[exact Range|];split;assumption.
Qed.
