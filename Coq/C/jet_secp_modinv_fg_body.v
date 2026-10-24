(** Complete original transition body, from initial limbs to final stored rows. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_exec.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix.
Require Import C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_index C.jet_secp_modinv_fg_loop.
Require Import C.jet_secp_modinv_fg_loop_numeric C.jet_secp_modinv_fg_iteration_prefix C.jet_secp_modinv_fg_iteration_numeric.
Require Import C.jet_secp_modinv_fg_iteration_arith C.jet_secp_modinv_fg_finish C.jet_secp_modinv_fg_finish_numeric.
Require Import C.jet_secp_modinv_normalize62_words.
Require Import C.jet_secp_modinv_fg_start.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fg_input_value rho high len := norm62_value_z (len-1) (fun j=>Int64.signed (fg_array_word rho high j)).
Definition fg_matrix_value rho high len :=
 Int64.signed (fg_iter_u rho high)*fg_input_value rho false len+
 Int64.signed (fg_iter_v rho high)*fg_input_value rho true len.
Definition fg_body_rho len rho := fg_loop_rho (len-1) (fg_start_rho rho) 1.
Definition fg_body_word len rho high j := fg_finished_word (fg_body_rho len rho) len high j.
Definition fg_body_value len rho high := fg_finished_value (fg_body_rho len rho) len high.

Lemma fg_matrix_decompose rho high len : (0<len<=5)%nat ->
 fg_matrix_value rho high len=fg_combination rho high 0+2^62*fg_combination_tail (len-1) rho high 1.
Proof.
 destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;
 unfold fg_matrix_value,fg_input_value;cbn [norm62_value_z fg_combination_tail Nat.sub];
 unfold fg_combination,fg_array_word;ring.
Qed.
Lemma fg_start_combination rho high j : (j<5)%nat ->
 fg_combination (fg_start_rho rho) high j=fg_combination rho high j.
Proof.
 intro J;unfold fg_combination;destruct (fg_start_row rho high) as (U & V);rewrite U,V.
 change (Int64.signed (fg_iter_u rho high)*Int64.signed (fg_array_word (fg_start_rho rho) false j)+
  Int64.signed (fg_iter_v rho high)*Int64.signed (fg_array_word (fg_start_rho rho) true j)=fg_combination rho high j).
 rewrite !fg_start_array by exact J;reflexivity.
Qed.
Lemma fg_matrix_quotient rho high len : (0<len<=5)%nat -> fg_input_bounds rho ->
 fg_pair_value (fg_iter_input (fg_start_rho rho) high)+
  fg_combination_tail (len-1) (fg_start_rho rho) high 1=fg_matrix_value rho high len/2^62.
Proof.
 intros Len Bounds;rewrite fg_start_input,fg_start_carry_value by exact Bounds.
 assert (Tail : fg_combination_tail (len-1) (fg_start_rho rho) high 1=
   fg_combination_tail (len-1) rho high 1).
 { apply fg_combination_tail_ext;intros j J;apply fg_start_combination;lia. }
 rewrite Tail,fg_matrix_decompose by exact Len.
 replace (2^62*fg_combination_tail (len-1) rho high 1) with
  (fg_combination_tail (len-1) rho high 1*2^62) by ring.
 rewrite Z.div_add by lia;reflexivity.
Qed.

Lemma fg_rest_source : fg_rest=Ssequence fg_for fg_finish.
Proof. reflexivity. Qed.
Lemma fg_initial_shapes : map rshape (sregs fg_initial)=map rshape fg_iter_regs.
Proof. vm_compute;reflexivity. Qed.

Lemma exec_fg_rest e le m ls lef mf :
 Clight2.exec_stmt secp_ge e le m (Sset _i (Econst_int Int.one tint)) E0 ls m Out_normal ->
 Clight2.exec_stmt secp_ge e ls m (Ssequence fg_loop fg_finish) E0 lef mf Out_normal ->
 Clight2.exec_stmt secp_ge e le m fg_rest E0 lef mf Out_normal.
Proof.
 intros SetI Rest;rewrite fg_rest_source,fg_for_source.
 inversion Rest;subst;try contradiction.
 match goal with
 | H : ?t1 ** ?t2 = E0 |- _=>destruct (Eapp_E0_inv t1 t2 H) as [-> ->]
 | H : E0 = ?t1 ** ?t2 |- _=>destruct (Eapp_E0_inv t1 t2 (eq_sym H)) as [-> ->]
 end.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact SetI|eassumption].
 - eassumption.
Qed.

Theorem exec_fg_body len rho beta e le m : (0<len<=5)%nat ->
 Int64.loword (rho 14%nat)=Int.repr (Z.of_nat len) -> fg_input_bounds rho ->
 rep rho beta (sregs fg_initial) m -> tmatch rho beta (stemps fg_initial) le ->
 ematch beta (snd fg_alloc) e -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_modinv64_update_fg_62_var) E0 lef mf Out_normal /\
 (forall (high : bool) j,(j<len)%nat -> Mem.load Mint64 mf (blk beta (if high then 1 else 0))
  (bas beta (if high then 1 else 0)+8*Z.of_nat j)=Some (Vlong (fg_body_word len rho high j))) /\
 (forall high,fg_body_value len rho high=fg_matrix_value rho high len/2^62) /\
 rep (fg_body_rho len rho) beta (fg_finish_regs len) mf /\
 tmatch (fg_body_rho len rho) beta (stemps (fg_finish_state len)) lef /\
 lframe (fun b ofs=>~foot beta (map rshape (sregs fg_initial)) b ofs) m mf.
Proof.
 intros Bound Len Bounds Rep Temps Env.
 destruct (exec_fg_prefix rho beta e le m Rep Temps Env) as (lp & mp & Prefix & RP & TP & FP).
 set (ls:=PTree.set _i (Vint Int.one) lp).
 assert (SetI : Clight2.exec_stmt secp_ge e lp mp (Sset _i (Econst_int Int.one tint)) E0 ls mp Out_normal).
 { apply exec_Sset;constructor. }
 assert (StartLen : Int64.loword (fg_start_rho rho 14%nat)=Int.repr (Z.of_nat len)) by exact Len.
 destruct (exec_fg_loop_and_finish len (fg_start_rho rho) beta e ls mp Bound StartLen
  (fg_start_state_bounds rho Bounds) (fun high=>fg_start_carry_fits64 rho high Bounds)
  (fg_start_rep rho beta mp RP) (fg_start_temps rho beta lp TP) Env)
  as (lef & mf & Rest & Storage & Value & Out & Match & Frame).
 exists lef,mf;split.
 - rewrite fg_source_split;eapply exec_statement_prefix_then_last;[exact Prefix|].
   eapply exec_fg_rest;[exact SetI|exact Rest].
 - split;[exact Storage|];split.
   + intro high;unfold fg_body_value,fg_body_rho;rewrite Value;apply fg_matrix_quotient;assumption.
   + split;[exact Out|];split;[exact Match|].
     rewrite fg_initial_shapes in FP|-*;eapply lframe_trans;[exact FP|exact Frame].
Qed.
