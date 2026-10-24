(** Numeric meaning of the original helper's final signed carry stores. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_iteration_prefix.
Require Import C.jet_secp_modinv_fg_loop_numeric C.jet_secp_modinv_fg_iteration_numeric.
Require Import C.jet_secp_modinv_fg_loop C.jet_secp_modinv_fg_revalue.
Require Import C.jet_secp_modinv_fg_index.
Require Import C.jet_secp_modinv_fg_iteration_arith C.jet_secp_i128_shift62_numeric.
Require Import C.jet_secp_modinv_normalize62_words C.jet_secp_u128_shift64_rep.
Require Import C.jet_secp_modinv_fg_finish.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma fg_pair_low_signed p : Int64.min_signed<=fg_pair_value p<=Int64.max_signed ->
 Int64.signed (fst p)=fg_pair_value p.
Proof.
 intro Range.
 assert (Repr : Int64.repr (fg_pair_value p)=fst p).
 { destruct p as [lo hi];unfold fg_pair_value,i128_signed_value;cbn [fst snd].
   rewrite <-(Int64.repr_unsigned lo) at 2;apply Int64.eqm_samerepr.
   exists (Int64.signed hi);reflexivity. }
 rewrite <-Repr;apply Int64.signed_repr;exact Range.
Qed.

Lemma fg_next_carry_fits64 rho high k : fg_state_bounds rho -> (k<5)%nat ->
 Int64.min_signed<=fg_pair_value (fg_iter_input (fg_next_rho rho k) high)<=Int64.max_signed.
Proof.
 intros Bounds K;rewrite fg_next_input.
 pose proof (fg_state_iteration_bound rho high k Bounds K) as Row.
 destruct (fg_row_step_numeric _ _ _ _ _ Row) as (Carry & _).
 change (fg_pair_value (fg_iter_carry rho high k)=fg_iter_sum rho high k/2^62) in Carry.
 rewrite Carry.
 destruct (fg_row_sum_bounds _ _ _ _ _ Row) as (_ & Sum);apply Z.abs_le in Sum.
 change (- (2^63+2^124)<=fg_iter_sum rho high k<=2^63+2^124) in Sum.
 change Int64.min_signed with (-2^63);change Int64.max_signed with (2^63-1).
 split;[apply Z.div_le_lower_bound|apply Z.div_le_upper_bound];lia.
Qed.

Lemma fg_loop_carry_fits64 count : forall rho high k,
 (1<=k)%nat -> (k+count<=5)%nat -> fg_state_bounds rho ->
 Int64.min_signed<=fg_pair_value (fg_iter_input rho high)<=Int64.max_signed ->
 Int64.min_signed<=fg_pair_value (fg_iter_input (fg_loop_rho count rho k) high)<=Int64.max_signed.
Proof.
 induction count as [|count IH];intros rho high k Start End Bounds Initial;[exact Initial|].
 cbn [fg_loop_rho];apply IH;[lia|lia|apply fg_state_bounds_next;[lia|exact Bounds]|].
 apply fg_next_carry_fits64;[exact Bounds|lia].
Qed.

Definition fg_finished_word (rho : nat->int64) len (high : bool) j :=
 if Nat.eqb j (len-1) then fst (fg_iter_input rho high) else fg_array_word rho high j.
Definition fg_finished_value rho len high :=
 norm62_value_z (len-1) (fun j=>Int64.signed (fg_finished_word rho len high j)).

Lemma fg_finish_load len (high : bool) j : (0<len<=5)%nat -> (j<5)%nat ->
 xload (fg_finish_regs len) (if high then 1 else 0) (8*Z.of_nat j) tulong=
 Some (if Nat.eqb j (len-1) then XLv (if high then 17 else 15) else XLv (if high then (5+j)%nat else j)).
Proof.
 destruct high;destruct len as [|[|[|[|[|[|len]]]]]];destruct j as [|[|[|[|[|j]]]]];
 intros Len J;try lia;vm_compute;reflexivity.
Qed.
Lemma fg_finish_value rho len high : (0<len<=5)%nat ->
 Int64.min_signed<=fg_pair_value (fg_iter_input rho high)<=Int64.max_signed ->
 fg_finished_value rho len high=fg_completed_value (len-1) rho high 1.
Proof.
 intros Len Range;pose proof (fg_pair_low_signed (fg_iter_input rho high) Range) as Carry.
 destruct high;destruct len as [|[|[|[|[|[|len]]]]]];try lia;
 cbn [fg_finished_value norm62_value_z fg_finished_word fg_completed_value Nat.sub Nat.eqb];
 rewrite <-Carry;reflexivity.
Qed.

Lemma fg_finish_storage rho beta len m : (0<len<=5)%nat -> rep rho beta (fg_finish_regs len) m ->
 forall (high : bool) j,(j<len)%nat ->
 Mem.load Mint64 m (blk beta (if high then 1 else 0))
  (bas beta (if high then 1 else 0)+8*Z.of_nat j)=Some (Vlong (fg_finished_word rho len high j)).
Proof.
 intros Len Rep high j J.
 pose proof (xload_u64_defined_sound rho beta _ m _ _ _ Rep (fg_finish_load len high j Len ltac:(lia))) as Load.
 unfold fg_finished_word;destruct (Nat.eqb j (len-1));destruct high;exact Load.
Qed.

Theorem exec_fg_finish_numeric len rho beta e le m : (0<len<=5)%nat ->
 Int64.loword (rho 14%nat)=Int.repr (Z.of_nat len) ->
 (forall high,Int64.min_signed<=fg_pair_value (fg_iter_input rho high)<=Int64.max_signed) ->
 rep rho beta fg_iter_regs m -> tmatch rho beta (fg_iter_temps len) le ->
 ematch beta (snd fg_alloc) e -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m fg_finish E0 lef mf Out_normal /\
 (forall (high : bool) j,(j<len)%nat -> Mem.load Mint64 mf (blk beta (if high then 1 else 0))
  (bas beta (if high then 1 else 0)+8*Z.of_nat j)=Some (Vlong (fg_finished_word rho len high j))) /\
 (forall high,fg_finished_value rho len high=fg_completed_value (len-1) rho high 1) /\
 rep rho beta (fg_finish_regs len) mf /\ tmatch rho beta (stemps (fg_finish_state len)) lef /\
 lframe (fun b ofs=>~foot beta (map rshape fg_iter_regs) b ofs) m mf.
Proof.
 intros Bound Len Carry Rep Temps Env.
 destruct (exec_fg_finish len rho beta e le m Bound Len Rep Temps Env)
  as (lef & mf & Exec & Out & Match & Frame).
 exists lef,mf;split;[exact Exec|];split;[exact (fg_finish_storage rho beta len mf Bound Out)|];
 split;[intro high;apply fg_finish_value;[exact Bound|apply Carry]|];
 split;[exact Out|];split;assumption.
Qed.

Lemma fg_loop_length count : forall rho k,fg_loop_rho count rho k 14%nat=rho 14%nat.
Proof. induction count;intros;[reflexivity|cbn [fg_loop_rho];rewrite IHcount;reflexivity]. Qed.

Theorem exec_fg_loop_and_finish len rho beta e le m : (0<len<=5)%nat ->
 Int64.loword (rho 14%nat)=Int.repr (Z.of_nat len) -> fg_state_bounds rho ->
 (forall high,Int64.min_signed<=fg_pair_value (fg_iter_input rho high)<=Int64.max_signed) ->
 rep rho beta fg_iter_regs m -> tmatch rho beta (fg_iter_temps 1) le ->
 ematch beta (snd fg_alloc) e -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m (Ssequence fg_loop fg_finish) E0 lef mf Out_normal /\
 (forall (high : bool) j,(j<len)%nat -> Mem.load Mint64 mf (blk beta (if high then 1 else 0))
  (bas beta (if high then 1 else 0)+8*Z.of_nat j)=
  Some (Vlong (fg_finished_word (fg_loop_rho (len-1) rho 1) len high j))) /\
 (forall high,fg_finished_value (fg_loop_rho (len-1) rho 1) len high=
  fg_pair_value (fg_iter_input rho high)+fg_combination_tail (len-1) rho high 1) /\
 rep (fg_loop_rho (len-1) rho 1) beta (fg_finish_regs len) mf /\
 tmatch (fg_loop_rho (len-1) rho 1) beta (stemps (fg_finish_state len)) lef /\
 lframe (fun b ofs=>~foot beta (map rshape fg_iter_regs) b ofs) m mf.
Proof.
 intros Bound Len Bounds Carry Rep Temps Env.
 assert (Count : (1+(len-1)=len)%nat) by lia.
 assert (LoopLen : Int64.loword (rho 14%nat)=Int.repr (Z.of_nat (1+(len-1)))).
 { rewrite Count;exact Len. }
 destruct (exec_fg_loop_numeric (len-1) 1 rho beta e le m ltac:(lia) ltac:(lia)
  LoopLen Bounds Rep Temps Env) as (ll & ml & Loop & Numeric & BFinal & RFinal & TFinal & FLoop).
 rewrite Count in TFinal.
 assert (FinalLen : Int64.loword (fg_loop_rho (len-1) rho 1 14%nat)=Int.repr (Z.of_nat len)).
 { rewrite fg_loop_length;exact Len. }
 assert (FinalCarry : forall high,Int64.min_signed<=
  fg_pair_value (fg_iter_input (fg_loop_rho (len-1) rho 1) high)<=Int64.max_signed).
 { intro high;apply fg_loop_carry_fits64;[lia|lia|exact Bounds|apply Carry]. }
 destruct (exec_fg_finish_numeric len (fg_loop_rho (len-1) rho 1) beta e ll ml Bound FinalLen
  FinalCarry RFinal TFinal Env) as (lef & mf & Finish & Storage & Value & Out & Match & Frame).
 exists lef,mf;split.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Loop|exact Finish].
 - split;[exact Storage|];split.
   + intro high;rewrite Value;exact (Numeric high).
   + split;[exact Out|];split;[exact Match|eapply lframe_trans;[exact FLoop|exact Frame]].
Qed.
