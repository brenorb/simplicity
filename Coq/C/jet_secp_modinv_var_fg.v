(** Actual inverse caller's f/g update, retaining its caller-owned layout. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem C.jet_sx_u64_transport.
Require Import C.jet_sx_region_lframe C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements.
Require Import C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_zero C.jet_secp_modinv_var_de.
Require Import C.jet_secp_modinv_var_copies C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_owned.
Require Import C.jet_secp_modinv_fg_call C.jet_secp_modinv_fg_start C.jet_secp_modinv_fg_body.
Require Import C.jet_secp_modinv_fg_finish C.jet_secp_modinv_fg_finish_numeric C.jet_secp_modinv_fg_index.
Require Import C.jet_secp_modinfo_fe_global C.jet_secp_fe_nv C.jet_secp_u128_shift64_rep.
Require Import C.jet_secp_modinv_normalize62_words C.jet_secp_modinv_fg_iteration_numeric.
Require Import C.jet_secp_modinv_fg_loop_numeric.
Require Import C.jet_secp_modinv_de_exec C.jet_secp_modinv_de_numeric C.jet_secp_modinv_de_correction_numeric C.jet_secp_modinv_de_revalue.
Require Import C.jet_secp_fe_math.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition inv_fg_rho len (rho : nat->int64) n :=
 if (n<?14)%nat then rho (15+n)%nat else Int64.repr (Z.of_nat len).
Definition inv_fg_select (r : nat) := nth r [4%nat;5%nat;6%nat] 0%nat.
Definition inv_fg_layout beta := [lay beta 4;lay beta 5;lay beta 6].
Lemma inv_fg_layout_at beta r : (r<3)%nat -> lay (inv_fg_layout beta) r=lay beta (inv_fg_select r).
Proof. destruct r as [|[|[|r]]];intro R;try lia;reflexivity. Qed.
Lemma inv_fg_block beta r : (r<3)%nat -> blk (inv_fg_layout beta) r=blk beta (inv_fg_select r).
Proof. intro R;unfold blk;rewrite inv_fg_layout_at by exact R;reflexivity. Qed.
Lemma inv_fg_base beta r : (r<3)%nat -> bas (inv_fg_layout beta) r=bas beta (inv_fg_select r).
Proof. intro R;unfold bas;rewrite inv_fg_layout_at by exact R;reflexivity. Qed.
Lemma inv_fg_separate beta : inv_loop_distinct beta -> fg_three_distinct (inv_fg_layout beta).
Proof.
 intros Distinct i j I J Ne;rewrite !inv_fg_block by assumption;apply Distinct;
 destruct i as [|[|[|i]]],j as [|[|[|j]]];try lia;cbn [inv_fg_select nth];lia.
Qed.

Definition inv_fg_next_rho len (rho : nat->int64) n := match n with
 | 15%nat=>fg_body_word len (inv_fg_rho len rho) false 0
 | 16%nat=>fg_body_word len (inv_fg_rho len rho) false 1
 | 17%nat=>fg_body_word len (inv_fg_rho len rho) false 2
 | 18%nat=>fg_body_word len (inv_fg_rho len rho) false 3
 | 19%nat=>fg_body_word len (inv_fg_rho len rho) false 4
 | 20%nat=>fg_body_word len (inv_fg_rho len rho) true 0
 | 21%nat=>fg_body_word len (inv_fg_rho len rho) true 1
 | 22%nat=>fg_body_word len (inv_fg_rho len rho) true 2
 | 23%nat=>fg_body_word len (inv_fg_rho len rho) true 3
 | 24%nat=>fg_body_word len (inv_fg_rho len rho) true 4
 | _=>rho n end.
Lemma inv_fg_next_outside len rho n : ((n<15)%nat \/ (25<=n)%nat) -> inv_fg_next_rho len rho n=rho n.
Proof.
 intro Outside;destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]];try reflexivity.
 destruct n as [|[|[|[|[|[|[|[|[|[|n]]]]]]]]]];try lia;reflexivity.
Qed.
Lemma inv_fg_next_word len rho (high : bool) j : (j<5)%nat ->
 inv_fg_next_rho len rho ((if high then 20 else 15)+j)%nat=fg_body_word len (inv_fg_rho len rho) high j.
Proof. destruct high;destruct j as [|[|[|[|[|j]]]]];intro J;try lia;reflexivity. Qed.
Definition inv_fg_output_exprs len (high : bool) := map (fun j=>
 if Nat.eqb j (len-1) then XLv (if high then 17 else 15)
 else XLv (if high then (5+j)%nat else j)) (seq 0 5).
Lemma inv_fg_output_array len high : (0<len<=5)%nat ->
 fg_result_array len high=mkreg (u64_cells 0 (inv_fg_output_exprs len high)) true (Some 40).
Proof. destruct high;destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;vm_compute;reflexivity. Qed.
Lemma inv_fg_output_den len rho beta (high : bool) : (0<len<=5)%nat ->
 map (den (inv_fg_next_rho len rho) (lay beta)) (vars5 (if high then 20 else 15))=
 map (den (fg_body_rho len (inv_fg_rho len rho)) (lay (inv_fg_layout beta))) (inv_fg_output_exprs len high).
Proof. destruct high;destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;reflexivity. Qed.
Lemma inv_fg_matrix_den len rho beta : (0<len<=5)%nat ->
 map (den (inv_fg_next_rho len rho) (lay beta)) [XLv 25;XLv 26;XLv 27;XLv 28]=
 map (den (fg_body_rho len (inv_fg_rho len rho)) (lay (inv_fg_layout beta))) [XLv 10;XLv 11;XLv 12;XLv 13].
Proof. destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;reflexivity. Qed.
Theorem inv_fg_project len rho beta m : rep rho beta inv_loop_regs m ->
 rep (inv_fg_rho len rho) (inv_fg_layout beta) fg_owned_regs m.
Proof.
 intro Rep;apply fg_rep_three.
 - reflexivity.
 - apply fg_distinct_three_sep;apply inv_fg_separate;apply (inv_loop_rep_distinct rho beta m Rep).
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=4%nat)
    (xs:=vars5 15) (ys:=vars5 0);try reflexivity;exact (rep_region _ _ _ _ 4 _ Rep eq_refl).
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=5%nat)
    (xs:=vars5 20) (ys:=vars5 5);try reflexivity;exact (rep_region _ _ _ _ 5 _ Rep eq_refl).
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=6%nat)
    (xs:=[XLv 25;XLv 26;XLv 27;XLv 28]) (ys:=[XLv 10;XLv 11;XLv 12;XLv 13]);
    try reflexivity;exact (rep_region _ _ _ _ 6 _ Rep eq_refl).
Qed.
Lemma inv_fg_length len rho : (0<len<=5)%nat ->
 Int64.loword (inv_fg_rho len rho 14%nat)=Int.repr (Z.of_nat len).
Proof. destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;reflexivity. Qed.

Definition inv_fg_statement := nth 3 (fst inv_caller_loop_parts) Sskip.
Definition inv_fg_arguments := [Etempvar _len tint;inv_s62_address _f;inv_s62_address _g;inv_matrix_address].
Lemma inv_fg_statement_source : inv_fg_statement=curve_call _secp256k1_modinv64_update_fg_62_var
 f_secp256k1_modinv64_update_fg_62_var None inv_fg_arguments.
Proof. reflexivity. Qed.
Lemma inv_fg_owned_bases rho beta m : rep rho beta inv_loop_regs m ->
 bas beta 4=0 /\ bas beta 5=0 /\ bas beta 6=0.
Proof.
 intro Rep;split;[|split];eapply rep_owned_region_base_zero;[exact Rep|reflexivity|reflexivity|
 exact Rep|reflexivity|reflexivity|exact Rep|reflexivity|reflexivity].
Qed.
Lemma inv_fg_arguments_eval len rho beta e le m : rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e -> le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 eval_exprlist secp_ge e le m inv_fg_arguments
 (type_of_params (fn_params f_secp256k1_modinv64_update_fg_62_var))
 [Vint (Int.repr (Z.of_nat len));
  Vptr (blk (inv_fg_layout beta) 0) (Ptrofs.repr (bas (inv_fg_layout beta) 0));
  Vptr (blk (inv_fg_layout beta) 1) (Ptrofs.repr (bas (inv_fg_layout beta) 1));
  Vptr (blk (inv_fg_layout beta) 2) (Ptrofs.repr (bas (inv_fg_layout beta) 2))].
Proof.
 intros Rep Env Len;destruct (inv_fg_owned_bases rho beta m Rep) as (F & G & T).
 rewrite !inv_fg_base,!inv_fg_block by lia;cbn [inv_fg_select nth];rewrite F,G,T.
 eapply eval_Econs;[apply eval_Etempvar;exact Len|reflexivity|].
 eapply eval_Econs.
 - apply eval_Eaddrof;apply eval_Evar_local;exact (proj1 (Env _f)).
 - reflexivity.
 - eapply eval_Econs.
   + apply eval_Eaddrof;apply eval_Evar_local;exact (proj1 (Env _g)).
   + reflexivity.
   + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact (proj1 (Env _t))|reflexivity|constructor].
Qed.

Theorem exec_inv_fg_call len rho beta e le m : (0<len<=5)%nat -> rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e -> le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 fg_input_bounds (inv_fg_rho len rho) -> exists mf,
 Clight2.exec_stmt secp_ge e le m inv_fg_statement E0 le mf Out_normal /\
 (forall high,fg_body_value len (inv_fg_rho len rho) high=fg_matrix_value (inv_fg_rho len rho) high len/2^62) /\
 rep (fg_body_rho len (inv_fg_rho len rho)) (inv_fg_layout beta) (fg_owned_out len) mf /\
 lframe (fun b ofs=>~foot (inv_fg_layout beta) (map rshape fg_regs) b ofs) m mf.
Proof.
 intros Length Rep Env Len Bounds;destruct (eval_fg_transition_owned len (inv_fg_rho len rho) (inv_fg_layout beta) m
  Length (inv_fg_length len rho Length) Bounds (inv_fg_project len rho beta m Rep))
  as (mf & Call & Words & Numeric & Out & Frame).
 exists mf;split;[|split;[exact Numeric|];split;assumption].
 rewrite inv_fg_statement_source;eapply exec_curve_call with (result:=None) (v:=Vundef).
 - unfold secp_pure;repeat (first [left;reflexivity|right]).
 - exact (proj1 (Env _secp256k1_modinv64_update_fg_62_var)).
 - exact (inv_fg_arguments_eval len rho beta e le m Rep Env Len).
 - exact Call.
Qed.

Lemma inv_fg_restore_array len rho beta m (high : bool) : (0<len<=5)%nat ->
 rep (fg_body_rho len (inv_fg_rho len rho)) (inv_fg_layout beta) (fg_owned_out len) m ->
 region_ok (inv_fg_next_rho len rho) beta m (if high then 5 else 4)
 (nth (if high then 5 else 4) inv_loop_regs fg_region_default).
Proof.
 intros Len Rep.
 pose proof (rep_region _ _ _ _ (if high then 1%nat else 0%nat) (fg_result_array len high)
  Rep ltac:(destruct high;reflexivity)) as Region.
 rewrite (inv_fg_output_array len high Len) in Region.
 destruct high.
 - eapply region_u64_transport with (rho:=fg_body_rho len (inv_fg_rho len rho)) (beta:=inv_fg_layout beta)
    (r:=1%nat) (xs:=inv_fg_output_exprs len true) (ys:=vars5 20);try reflexivity.
   + exact (inv_fg_output_den len rho beta true Len).
   + exact Region.
 - eapply region_u64_transport with (rho:=fg_body_rho len (inv_fg_rho len rho)) (beta:=inv_fg_layout beta)
    (r:=0%nat) (xs:=inv_fg_output_exprs len false) (ys:=vars5 15);try reflexivity.
   + exact (inv_fg_output_den len rho beta false Len).
   + exact Region.
Qed.
Lemma inv_fg_restore_matrix len rho beta m : (0<len<=5)%nat ->
 rep (fg_body_rho len (inv_fg_rho len rho)) (inv_fg_layout beta) (fg_owned_out len) m ->
 region_ok (inv_fg_next_rho len rho) beta m 6 (nth 6 inv_loop_regs fg_region_default).
Proof.
 intros Len Rep;eapply region_u64_transport with (rho:=fg_body_rho len (inv_fg_rho len rho))
  (beta:=inv_fg_layout beta) (r:=2%nat) (xs:=[XLv 10;XLv 11;XLv 12;XLv 13])
  (ys:=[XLv 25;XLv 26;XLv 27;XLv 28]);try reflexivity.
 - exact (inv_fg_matrix_den len rho beta Len).
 - exact (rep_region _ _ _ _ 2 _ Rep eq_refl).
Qed.
Lemma inv_fg_other_outside beta r : inv_loop_distinct beta -> (r<4)%nat ->
 forall pos,~foot (inv_fg_layout beta) (map rshape fg_regs) (blk beta r) pos.
Proof.
 intros Distinct R pos (j & sh & d & ch & At & Member & Equal & Range).
 assert (J : (j<3)%nat).
 { change (j<length (map rshape fg_regs))%nat;apply nth_error_Some;rewrite At;discriminate. }
 rewrite inv_fg_block in Equal by exact J.
 assert (Bound : (4<=inv_fg_select j<7)%nat).
 { destruct j as [|[|[|j]]];try lia;cbn [inv_fg_select nth];lia. }
 apply (Distinct r (inv_fg_select j) ltac:(lia) ltac:(lia) ltac:(lia));exact Equal.
Qed.
Theorem inv_fg_restore_caller len rho beta m mf : (0<len<=5)%nat -> rep rho beta inv_loop_regs m ->
 rep (fg_body_rho len (inv_fg_rho len rho)) (inv_fg_layout beta) (fg_owned_out len) mf ->
 lframe (fun b ofs=>~foot (inv_fg_layout beta) (map rshape fg_regs) b ofs) m mf ->
 rep (inv_fg_next_rho len rho) beta inv_loop_regs mf.
Proof.
 intros Len Rep Updated Frame;pose proof (inv_loop_rep_distinct rho beta m Rep) as Distinct.
 pose proof (inv_fg_restore_array len rho beta mf false Len Updated) as F.
 pose proof (inv_fg_restore_array len rho beta mf true Len Updated) as G.
 pose proof (inv_fg_restore_matrix len rho beta mf Len Updated) as T.
 destruct Rep as (Size & Sep & Regions);split;[exact Size|];split;[exact Sep|].
 intros r reg At;assert (R : (r<7)%nat) by (change (r<length inv_loop_regs)%nat;apply nth_error_Some;rewrite At;discriminate).
 destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;
  cbn [inv_loop_regs nth_error] in At;injection At as <-.
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=0%nat) (xs:=vars5 0) (ys:=vars5 0);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply inv_fg_other_outside;[exact Distinct|lia]|exact (Regions 0%nat _ eq_refl)].
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=1%nat)
    (xs:=map XLc modinfo_fe_words) (ys:=map XLc modinfo_fe_words);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply inv_fg_other_outside;[exact Distinct|lia]|exact (Regions 1%nat _ eq_refl)].
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=2%nat) (xs:=vars5 5) (ys:=vars5 5);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply inv_fg_other_outside;[exact Distinct|lia]|exact (Regions 2%nat _ eq_refl)].
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=3%nat) (xs:=vars5 10) (ys:=vars5 10);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply inv_fg_other_outside;[exact Distinct|lia]|exact (Regions 3%nat _ eq_refl)].
 - exact F.
 - exact G.
 - exact T.
Qed.

Corollary exec_inv_fg_caller len rho beta e le m : (0<len<=5)%nat -> rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e -> le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 fg_input_bounds (inv_fg_rho len rho) -> exists mf,
 Clight2.exec_stmt secp_ge e le m inv_fg_statement E0 le mf Out_normal /\
 rep (inv_fg_next_rho len rho) beta inv_loop_regs mf /\
 (forall high,fg_body_value len (inv_fg_rho len rho) high=fg_matrix_value (inv_fg_rho len rho) high len/2^62) /\
 lframe (fun b ofs=>~foot (inv_fg_layout beta) (map rshape fg_regs) b ofs) m mf.
Proof.
 intros Length Rep Env Len Bounds;destruct (exec_inv_fg_call len rho beta e le m Length Rep Env Len Bounds)
  as (mf & Exec & Numeric & Out & Frame).
 exists mf;split;[exact Exec|];split;[eapply inv_fg_restore_caller;eassumption|];split;assumption.
Qed.

Definition inv_fg_active_value len (rho : nat->int64) (high : bool) :=
 norm62_value_z (len-1) (fun j=>Int64.signed (rho ((if high then 20 else 15)+j)%nat)).
Lemma inv_fg_next_value len rho high : (0<len<=5)%nat ->
 inv_fg_active_value len (inv_fg_next_rho len rho) high=fg_body_value len (inv_fg_rho len rho) high.
Proof. destruct high;destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;reflexivity. Qed.
Lemma inv_fg_load_expr (high : bool) j : (j<5)%nat ->
 xload inv_loop_regs (if high then 5 else 4) (8*Z.of_nat j) tulong=
 Some (XLv ((if high then 20 else 15)+j)%nat).
Proof. destruct high;destruct j as [|[|[|[|[|j]]]]];intro J;try lia;reflexivity. Qed.
Lemma inv_fg_caller_loads len rho beta m : rep (inv_fg_next_rho len rho) beta inv_loop_regs m ->
 forall (high : bool) j,(j<5)%nat -> Mem.load Mint64 m (blk beta (if high then 5 else 4))
 (bas beta (if high then 5 else 4)+8*Z.of_nat j)=Some (Vlong (fg_body_word len (inv_fg_rho len rho) high j)).
Proof.
 intros Rep high j J;pose proof (xload_u64_defined_sound _ _ _ _ _ _ _ Rep (inv_fg_load_expr high j J)) as Load.
 change (Mem.load Mint64 m (blk beta (if high then 5 else 4))
  (bas beta (if high then 5 else 4)+8*Z.of_nat j)=
  Some (Vlong (inv_fg_next_rho len rho ((if high then 20 else 15)+j)%nat))) in Load.
 rewrite inv_fg_next_word in Load by exact J;exact Load.
Qed.
Lemma inv_fg_mask_bound a : 0<=Int64.signed (Int64.and a (Int64.repr (2^62-1)))<2^62.
Proof. rewrite norm62_mask_signed;apply Z.mod_pos_bound;lia. Qed.
Lemma inv_fg_body_lower len rho high j : (0<len<=5)%nat -> (S j<len)%nat ->
 0<=Int64.signed (fg_body_word len rho high j)<2^62.
Proof.
 destruct high;destruct len as [|[|[|[|[|[|len]]]]]];
 destruct j as [|[|[|[|j]]]];intros Len J;try lia.
 all: apply inv_fg_mask_bound.
Qed.

Corollary exec_inv_fg_ready len rho beta e le m : (0<len<=5)%nat -> rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e -> le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 fg_input_bounds (inv_fg_rho len rho) -> exists mf,
 Clight2.exec_stmt secp_ge e le m inv_fg_statement E0 le mf Out_normal /\
 rep (inv_fg_next_rho len rho) beta inv_loop_regs mf /\
 (forall (high : bool) j,(j<5)%nat -> Mem.load Mint64 mf (blk beta (if high then 5 else 4))
  (bas beta (if high then 5 else 4)+8*Z.of_nat j)=Some (Vlong (fg_body_word len (inv_fg_rho len rho) high j))) /\
 (forall high,inv_fg_active_value len (inv_fg_next_rho len rho) high=fg_matrix_value (inv_fg_rho len rho) high len/2^62) /\
 (forall (high : bool) j,(S j<len)%nat ->
  0<=Int64.signed (inv_fg_next_rho len rho ((if high then 20 else 15)+j)%nat)<2^62) /\
 lframe (fun b ofs=>~foot (inv_fg_layout beta) (map rshape fg_regs) b ofs) m mf.
Proof.
 intros Length Rep Env Len Bounds;destruct (exec_inv_fg_caller len rho beta e le m Length Rep Env Len Bounds)
  as (mf & Exec & Out & Numeric & Frame).
 exists mf;split;[exact Exec|];split;[exact Out|];split;[apply inv_fg_caller_loads;exact Out|];split.
 - intro high;rewrite inv_fg_next_value by exact Length;apply Numeric.
 - split;[|exact Frame];intros high j J;rewrite inv_fg_next_word by lia;apply inv_fg_body_lower;assumption.
Qed.

Lemma inv_fg_after_de len rho n : inv_fg_rho len (inv_de_next_rho rho) n=inv_fg_rho len rho n.
Proof.
 unfold inv_fg_rho;destruct (n<?14)%nat;[rewrite inv_de_next_outside by (right;lia)|];reflexivity.
Qed.
Lemma inv_fg_bounds_after_de len rho : fg_input_bounds (inv_fg_rho len rho) ->
 fg_input_bounds (inv_fg_rho len (inv_de_next_rho rho)).
Proof.
 intros (Rows & Limbs);split.
 - intro high;unfold fg_iter_u,fg_iter_v;rewrite !inv_fg_after_de;apply Rows.
 - intros high j J;unfold fg_array_word;rewrite inv_fg_after_de;apply Limbs;exact J.
Qed.
Definition inv_update_calls := Ssequence inv_de_statement inv_fg_statement.
Lemma inv_update_calls_source : skipn 2 (firstn 4 (fst inv_caller_loop_parts))=
 [inv_de_statement;inv_fg_statement].
Proof. reflexivity. Qed.
Theorem exec_inv_update_calls len rho beta e le m : (0<len<=5)%nat -> rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e ->
 le!_modinfo=Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
 le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 (forall high,de62_row_bound (inv_de_rho rho) high) -> de62_state_bounds (inv_de_rho rho) ->
 fg_input_bounds (inv_fg_rho len rho) -> exists mf,
 Clight2.exec_stmt secp_ge e le m inv_update_calls E0 le mf Out_normal /\
 rep (inv_fg_next_rho len (inv_de_next_rho rho)) beta inv_loop_regs mf /\
 de62_state_bounds (de62_next_rho (inv_de_rho rho)) /\
 (forall high,
  2^62*de62_input_value (de62_next_rho (inv_de_rho rho)) high=de62_matrix_value (inv_de_rho rho) high+
   feP*de62_correction_value (inv_de_rho rho) high /\
  (2^62*de62_input_value (de62_next_rho (inv_de_rho rho)) high-de62_matrix_value (inv_de_rho rho) high) mod feP=0) /\
 (forall high,inv_fg_active_value len (inv_fg_next_rho len (inv_de_next_rho rho)) high=
  fg_matrix_value (inv_fg_rho len (inv_de_next_rho rho)) high len/2^62) /\
 (forall (high : bool) j,(S j<len)%nat ->
  0<=Int64.signed (inv_fg_next_rho len (inv_de_next_rho rho) ((if high then 20 else 15)+j)%nat)<2^62) /\
 lframe (fun b ofs=>~foot (inv_de_layout beta) (map rshape de62_regs) b ofs /\
  ~foot (inv_fg_layout beta) (map rshape fg_regs) b ofs) m mf.
Proof.
 intros Length Rep Env Modinfo Len Rows Bounds FG.
 destruct (exec_inv_de_caller rho beta e le m Rep Env Modinfo Rows Bounds)
  as (md & DE & DEOut & DEBounds & DENumeric & DEFrame).
 destruct (exec_inv_fg_ready len (inv_de_next_rho rho) beta e le md Length DEOut Env Len
  (inv_fg_bounds_after_de len rho FG)) as (mf & FGExec & FGOut & Loads & FGNumeric & Low & FGFrame).
 exists mf;split.
 - unfold inv_update_calls;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=md);eassumption.
 - split;[exact FGOut|];split;[exact DEBounds|];split;[exact DENumeric|];split;[exact FGNumeric|];split;[exact Low|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact DEFrame|intros b ofs Both _;exact (proj1 Both)].
   + eapply lframe_implies;[exact FGFrame|intros b ofs Both _;exact (proj2 Both)].
Qed.
