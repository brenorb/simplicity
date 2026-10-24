(** Numeric invariant of the checked original inverse-transition loop. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Clight ClightBigstep Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_iteration_prefix.
Require Import C.jet_secp_modinv_fg_index.
Require Import C.jet_secp_modinv_fg_loop C.jet_secp_modinv_fg_revalue.
Require Import C.jet_secp_modinv_fg_iteration_numeric C.jet_secp_modinv_fg_iteration_arith.
Require Import C.jet_secp_modinv_normalize62_words.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fg_array_word (rho : nat->int64) (high : bool) j := rho (if high then (5+j)%nat else j).
Definition fg_combination rho high j :=
 Int64.signed (fg_iter_u rho high)*Int64.signed (rho j)+
 Int64.signed (fg_iter_v rho high)*Int64.signed (rho (5+j)%nat).
Definition fg_state_bounds rho : Prop :=
 (forall high,Z.abs (fg_pair_value (fg_iter_input rho high))<=2^63 /\
   Z.abs (Int64.signed (fg_iter_u rho high))+Z.abs (Int64.signed (fg_iter_v rho high))<=2^62) /\
 (forall high j,(j<5)%nat -> Z.abs (Int64.signed (fg_array_word rho high j))<=2^62).

Lemma fg_next_array_word rho (high : bool) j k : (j<5)%nat -> (0<k<5)%nat ->
 fg_array_word (fg_next_rho rho k) high j=
 if Nat.eqb j (k-1) then fg_iter_limb rho high k else fg_array_word rho high j.
Proof.
 destruct high;destruct j as [|[|[|[|[|j]]]]];destruct k as [|[|[|[|[|k]]]]];
 intros J K;try lia;reflexivity.
Qed.
Lemma fg_next_input rho (high : bool) k : fg_iter_input (fg_next_rho rho k) high=fg_iter_carry rho high k.
Proof. destruct high;reflexivity. Qed.
Lemma fg_next_row rho (high : bool) k :
 fg_iter_u (fg_next_rho rho k) high=fg_iter_u rho high /\
 fg_iter_v (fg_next_rho rho k) high=fg_iter_v rho high.
Proof. destruct high;split;reflexivity. Qed.
Lemma fg_limb_signed_unsigned rho high k :
 Int64.signed (fg_iter_limb rho high k)=Int64.unsigned (fg_iter_limb rho high k).
Proof. unfold fg_iter_limb,fg_row_limb;rewrite norm62_mask_signed,norm62_mask_unsigned;reflexivity. Qed.

Lemma fg_state_iteration_bound rho high k : fg_state_bounds rho -> (k<5)%nat -> fg_iter_bound rho high k.
Proof.
 intros (Carries & Limbs) K;destruct (Carries high) as (Carry & Row).
 split;[exact Carry|];split;[exact Row|];split;
 [exact (Limbs false k K)|exact (Limbs true k K)].
Qed.

Lemma fg_state_bounds_next rho k : (0<k<5)%nat -> fg_state_bounds rho -> fg_state_bounds (fg_next_rho rho k).
Proof.
 intros K Bounds;pose proof Bounds as (Carries & Limbs);split.
 - intro high;rewrite fg_next_input;destruct (fg_next_row rho high k) as (U & V);rewrite U,V.
   split;[|exact (proj2 (Carries high))].
   destruct (fg_row_step_numeric _ _ _ _ _ (fg_state_iteration_bound rho high k Bounds ltac:(lia)))
    as (_ & _ & _ & Carry & _);exact Carry.
 - intros high j J;rewrite fg_next_array_word by assumption.
   destruct (Nat.eqb j (k-1));[|exact (Limbs high j J)].
   destruct (fg_row_step_numeric _ _ _ _ _ (fg_state_iteration_bound rho high k Bounds ltac:(lia)))
    as (_ & _ & Limb & _).
   change (0<=Int64.signed (fg_iter_limb rho high k)<2^62) in Limb.
   rewrite Z.abs_eq by lia;lia.
Qed.

Lemma fg_next_combination rho high j k : (j<5)%nat -> (0<k<5)%nat -> (j<>k-1)%nat ->
 fg_combination (fg_next_rho rho k) high j=fg_combination rho high j.
Proof.
 intros J K Not;unfold fg_combination.
 destruct (fg_next_row rho high k) as (U & V);rewrite U,V.
 change (Int64.signed (fg_iter_u rho high)*Int64.signed (fg_array_word (fg_next_rho rho k) false j)+
  Int64.signed (fg_iter_v rho high)*Int64.signed (fg_array_word (fg_next_rho rho k) true j)=
  fg_combination rho high j).
 rewrite !fg_next_array_word by assumption;rewrite (proj2 (Nat.eqb_neq _ _) Not);reflexivity.
Qed.

Fixpoint fg_combination_tail count rho high k : Z := match count with
 | O=>0 | S n=>fg_combination rho high k+2^62*fg_combination_tail n rho high (S k) end.
Fixpoint fg_completed_value count rho high k : Z := match count with
 | O=>fg_pair_value (fg_iter_input rho high)
 | S n=>Int64.signed (fg_array_word rho high (k-1))+2^62*fg_completed_value n rho high (S k) end.

Lemma fg_combination_tail_ext count rho sigma high k :
 (forall j,(k<=j<k+count)%nat -> fg_combination rho high j=fg_combination sigma high j) ->
 fg_combination_tail count rho high k=fg_combination_tail count sigma high k.
Proof.
 induction count as [|count IH] in k|-*;intro Equal;[reflexivity|].
 cbn [fg_combination_tail];rewrite Equal by lia;rewrite IH;[reflexivity|].
 intros j J;apply Equal;lia.
Qed.

Lemma fg_loop_preserves_lower count : forall rho k high j,
 (1<=k)%nat -> (k+count<=5)%nat -> (j<k-1)%nat ->
 fg_array_word (fg_loop_rho count rho k) high j=fg_array_word rho high j.
Proof.
 induction count as [|count IH];intros rho k high j Start End J;[reflexivity|].
 cbn [fg_loop_rho];rewrite IH by lia.
 rewrite fg_next_array_word by lia;rewrite (proj2 (Nat.eqb_neq j (k-1)) ltac:(lia));reflexivity.
Qed.

Theorem fg_loop_numeric count : forall rho high k,
 (1<=k)%nat -> (k+count<=5)%nat -> fg_state_bounds rho ->
 fg_completed_value count (fg_loop_rho count rho k) high k=
 fg_pair_value (fg_iter_input rho high)+fg_combination_tail count rho high k /\
 fg_state_bounds (fg_loop_rho count rho k).
Proof.
 induction count as [|count IH];intros rho high k Start End Bounds.
 - cbn [fg_loop_rho fg_completed_value fg_combination_tail];split;[lia|exact Bounds].
 - assert (K : (0<k<5)%nat) by lia.
   destruct (IH (fg_next_rho rho k) high (S k) ltac:(lia) ltac:(lia)
     (fg_state_bounds_next rho k K Bounds)) as (Recurrence & NextBounds).
   split;[|exact NextBounds].
   cbn [fg_loop_rho fg_completed_value fg_combination_tail].
   rewrite fg_loop_preserves_lower by lia.
   rewrite fg_next_array_word by lia;rewrite Nat.eqb_refl.
   rewrite Recurrence,fg_next_input.
   assert (Tail : fg_combination_tail count (fg_next_rho rho k) high (S k)=
    fg_combination_tail count rho high (S k)).
   { apply fg_combination_tail_ext;intros j J;apply fg_next_combination;lia. }
   rewrite Tail,fg_limb_signed_unsigned.
   destruct (fg_row_step_numeric _ _ _ _ _ (fg_state_iteration_bound rho high k Bounds ltac:(lia)))
    as (_ & _ & _ & _ & Sum).
   change (fg_iter_sum rho high k=fg_pair_value (fg_iter_carry rho high k)*2^62+
    Int64.unsigned (fg_iter_limb rho high k)) in Sum.
   unfold fg_iter_sum,fg_row_sum in Sum;unfold fg_combination.
   lia.
Qed.

Theorem exec_fg_loop_numeric count k rho beta e le m :
 (1<=k)%nat -> (k+count<=5)%nat ->
 Int64.loword (rho 14%nat)=Int.repr (Z.of_nat (k+count)) -> fg_state_bounds rho ->
 rep rho beta fg_iter_regs m -> tmatch rho beta (fg_iter_temps k) le ->
 ematch beta (snd fg_alloc) e -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m fg_loop E0 lef mf Out_normal /\
 (forall high,fg_completed_value count (fg_loop_rho count rho k) high k=
  fg_pair_value (fg_iter_input rho high)+fg_combination_tail count rho high k) /\
 fg_state_bounds (fg_loop_rho count rho k) /\
 rep (fg_loop_rho count rho k) beta fg_iter_regs mf /\
 tmatch (fg_loop_rho count rho k) beta (fg_iter_temps (k+count)) lef /\
 lframe (fun b ofs=>~foot beta (map rshape fg_iter_regs) b ofs) m mf.
Proof.
 intros Start End Len Bounds Rep Temps Env.
 destruct (exec_fg_loop_from_body count k rho beta e le m Start End Len Rep Temps Env)
  as (lef & mf & Exec & Out & Match & Frame).
 exists lef,mf;split;[exact Exec|];split.
 - intro high;exact (proj1 (fg_loop_numeric count rho high k Start End Bounds)).
 - split;[exact (proj2 (fg_loop_numeric count rho false k Start End Bounds))|];
   split;[exact Out|];split;assumption.
Qed.
