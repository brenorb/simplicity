(** Caller-owned inverse locals projected to the original coefficient update. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem C.jet_sx_u64_transport.
Require Import C.jet_sx_region_lframe C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements.
Require Import C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_zero C.jet_secp_modinv_var_shorten C.jet_secp_modinv_var_post.
Require Import C.jet_secp_modinv_de_exec C.jet_secp_modinv_de_revalue C.jet_secp_modinv_de_numeric.
Require Import C.jet_secp_modinv_de_correction_numeric C.jet_secp_modinfo_fe_global C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_modinv_fg_index C.jet_secp_u128_shift64_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition inv_loop_regs :=
 [mkreg (u64_cells 0 (vars5 0)) true (Some 40);
  mkreg (u64_cells 0 (map XLc modinfo_fe_words)) false None;
  mkreg (u64_cells 0 (vars5 5)) true (Some 40);
  mkreg (u64_cells 0 (vars5 10)) true (Some 40);
  mkreg (u64_cells 0 (vars5 15)) true (Some 40);
  mkreg (u64_cells 0 (vars5 20)) true (Some 40);
  mkreg (u64_cells 0 [XLv 25;XLv 26;XLv 27;XLv 28]) true (Some 32)].
Definition inv_de_rho (rho : nat->int64) n := if (n <? 10)%nat then rho (5+n)%nat else rho (15+n)%nat.
Definition inv_de_select (r : nat) := nth r [2%nat;3%nat;6%nat;1%nat] 0%nat.
Definition inv_de_layout beta := [lay beta 2;lay beta 3;lay beta 6;lay beta 1].
Definition inv_loop_distinct beta := forall i j,(i<7)%nat -> (j<7)%nat -> i<>j -> blk beta i<>blk beta j.

Lemma inv_loop_none r : (r<7)%nat ->
 rfree (nth r inv_loop_regs (mkreg [] false None))=None -> r=1%nat.
Proof. destruct r as [|[|[|[|[|[|[|r]]]]]]];intros R E;try lia;try discriminate;reflexivity. Qed.
Lemma inv_loop_rep_distinct rho beta m : rep rho beta inv_loop_regs m -> inv_loop_distinct beta.
Proof.
 intros (_ & Sep & _) i j I J Ne.
 pose proof (nth_error_nth' inv_loop_regs (mkreg [] false None) I) as AtI.
 pose proof (nth_error_nth' inv_loop_regs (mkreg [] false None) J) as AtJ.
 destruct (Sep i j _ _ Ne AtI AtJ) as [Different|[NoI [NoJ _]]];[exact Different|].
 exfalso;apply Ne;rewrite (inv_loop_none i I NoI),(inv_loop_none j J NoJ);reflexivity.
Qed.
Lemma inv_de_layout_at beta r : (r<4)%nat -> lay (inv_de_layout beta) r=lay beta (inv_de_select r).
Proof. destruct r as [|[|[|[|r]]]];intro R;try lia;reflexivity. Qed.
Lemma inv_de_block beta r : (r<4)%nat -> blk (inv_de_layout beta) r=blk beta (inv_de_select r).
Proof. intro R;unfold blk;rewrite inv_de_layout_at by exact R;reflexivity. Qed.
Lemma inv_de_base beta r : (r<4)%nat -> bas (inv_de_layout beta) r=bas beta (inv_de_select r).
Proof. intro R;unfold bas;rewrite inv_de_layout_at by exact R;reflexivity. Qed.
Lemma inv_de_separate beta : inv_loop_distinct beta -> rsep (inv_de_layout beta) de62_regs.
Proof.
 intros Distinct i j ri rj Ne AtI AtJ;left.
 assert (I : (i<4)%nat) by (change (i<length de62_regs)%nat;apply nth_error_Some;rewrite AtI;discriminate).
 assert (J : (j<4)%nat) by (change (j<length de62_regs)%nat;apply nth_error_Some;rewrite AtJ;discriminate).
 rewrite !inv_de_block by assumption;apply Distinct;
  destruct i as [|[|[|[|i]]]],j as [|[|[|[|j]]]];try lia;cbn [inv_de_select nth];lia.
Qed.

Theorem inv_de_project rho beta m : rep rho beta inv_loop_regs m ->
 rep (inv_de_rho rho) (inv_de_layout beta) de62_regs m.
Proof.
 intro Rep;apply de62_rep_four.
 - reflexivity.
 - apply inv_de_separate;apply (inv_loop_rep_distinct rho beta m Rep).
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=2%nat)
    (xs:=vars5 5) (ys:=vars5 0);try reflexivity;exact (rep_region _ _ _ _ 2 _ Rep eq_refl).
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=3%nat)
    (xs:=vars5 10) (ys:=vars5 5);try reflexivity;exact (rep_region _ _ _ _ 3 _ Rep eq_refl).
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=6%nat)
    (xs:=[XLv 25;XLv 26;XLv 27;XLv 28]) (ys:=[XLv 10;XLv 11;XLv 12;XLv 13]);
    try reflexivity;exact (rep_region _ _ _ _ 6 _ Rep eq_refl).
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=1%nat)
    (xs:=map XLc modinfo_fe_words) (ys:=map XLc modinfo_fe_words);
    try reflexivity;exact (rep_region _ _ _ _ 1 _ Rep eq_refl).
Qed.

Definition inv_de_statement := nth 2 (fst inv_caller_loop_parts) Sskip.
Definition inv_s62_address id := Eaddrof (Evar id fg_s62_type) (tptr fg_s62_type).
Definition inv_matrix_type := Tstruct _secp256k1_modinv64_trans2x2 noattr.
Definition inv_matrix_address := Eaddrof (Evar _t inv_matrix_type) (tptr inv_matrix_type).
Definition inv_metadata_type := Tstruct _secp256k1_modinv64_modinfo noattr.
Definition inv_metadata_arg := Etempvar _modinfo (tptr inv_metadata_type).
Lemma inv_de_statement_source : inv_de_statement=curve_call _secp256k1_modinv64_update_de_62
 f_secp256k1_modinv64_update_de_62 None
 [inv_s62_address _d;inv_s62_address _e;inv_matrix_address;inv_metadata_arg].
Proof. reflexivity. Qed.

Lemma inv_loop_owned_bases rho beta m : rep rho beta inv_loop_regs m ->
 bas beta 2=0 /\ bas beta 3=0 /\ bas beta 6=0.
Proof.
 intro Rep;split;[|split];eapply rep_owned_region_base_zero;[exact Rep|reflexivity|reflexivity|
 exact Rep|reflexivity|reflexivity|exact Rep|reflexivity|reflexivity].
Qed.
Lemma inv_de_arguments rho beta e le m : rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e ->
 le!_modinfo=Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
 eval_exprlist secp_ge e le m [inv_s62_address _d;inv_s62_address _e;inv_matrix_address;inv_metadata_arg]
 (type_of_params (fn_params f_secp256k1_modinv64_update_de_62))
 [Vptr (blk (inv_de_layout beta) 0) (Ptrofs.repr (bas (inv_de_layout beta) 0));
  Vptr (blk (inv_de_layout beta) 1) (Ptrofs.repr (bas (inv_de_layout beta) 1));
  Vptr (blk (inv_de_layout beta) 2) (Ptrofs.repr (bas (inv_de_layout beta) 2));
  Vptr (blk (inv_de_layout beta) 3) (Ptrofs.repr (bas (inv_de_layout beta) 3))].
Proof.
 intros Rep Env Modinfo;destruct (inv_loop_owned_bases rho beta m Rep) as (D & E & T).
 rewrite !inv_de_base,!inv_de_block by lia;cbn [inv_de_select nth];rewrite D,E,T.
 eapply eval_Econs.
 - apply eval_Eaddrof;apply eval_Evar_local;exact (proj1 (Env _d)).
 - reflexivity.
 - eapply eval_Econs.
   + apply eval_Eaddrof;apply eval_Evar_local;exact (proj1 (Env _e)).
   + reflexivity.
   + eapply eval_Econs.
     * apply eval_Eaddrof;apply eval_Evar_local;exact (proj1 (Env _t)).
     * reflexivity.
     * eapply eval_Econs;[apply eval_Etempvar;exact Modinfo|reflexivity|constructor].
Qed.

Theorem exec_inv_de_call rho beta e le m : rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e ->
 le!_modinfo=Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
 (forall high,de62_row_bound (inv_de_rho rho) high) -> de62_state_bounds (inv_de_rho rho) -> exists mf,
 Clight2.exec_stmt secp_ge e le m inv_de_statement E0 le mf Out_normal /\
 rep (de62_next_rho (inv_de_rho rho)) (inv_de_layout beta) de62_regs mf /\
 de62_state_bounds (de62_next_rho (inv_de_rho rho)) /\
 (forall high,
  2^62*de62_input_value (de62_next_rho (inv_de_rho rho)) high=de62_matrix_value (inv_de_rho rho) high+
   feP*de62_correction_value (inv_de_rho rho) high /\
  (2^62*de62_input_value (de62_next_rho (inv_de_rho rho)) high-de62_matrix_value (inv_de_rho rho) high) mod feP=0) /\
 lframe (fun b ofs=>~foot (inv_de_layout beta) (map rshape de62_regs) b ofs) m mf.
Proof.
 intros Rep Env Modinfo Rows Bounds;destruct (eval_de_step (inv_de_rho rho) (inv_de_layout beta) m
  (inv_de_project rho beta m Rep) Rows Bounds) as (mf & Call & Out & NextBounds & Numeric & Frame).
 exists mf;split;[|split;[exact Out|];split;[exact NextBounds|];split;assumption].
 rewrite inv_de_statement_source;eapply exec_curve_call with (result:=None) (v:=Vundef).
 - unfold secp_pure;repeat (first [left;reflexivity|right]).
 - exact (proj1 (Env _secp256k1_modinv64_update_de_62)).
 - apply (inv_de_arguments rho beta e le m Rep Env Modinfo).
 - exact Call.
Qed.

Definition inv_de_next_rho (rho : nat->int64) n :=
 if (5<=?n)%nat && (n<?15)%nat then de62_next_rho (inv_de_rho rho) (n-5)%nat else rho n.
Lemma inv_de_next_outside rho n : ((n<5)%nat \/ (15<=n)%nat) -> inv_de_next_rho rho n=rho n.
Proof.
 intro Outside;unfold inv_de_next_rho;destruct (Nat.leb_spec 5 n),(Nat.ltb_spec n 15);try lia;reflexivity.
Qed.
Lemma inv_de_next_project rho n : inv_de_rho (inv_de_next_rho rho) n=de62_next_rho (inv_de_rho rho) n.
Proof.
 destruct (Nat.lt_ge_cases n 10) as [N|N].
 - destruct n as [|[|[|[|[|[|[|[|[|[|n]]]]]]]]]];try lia;reflexivity.
 - unfold inv_de_rho at 1;rewrite (proj2 (Nat.ltb_ge n 10) N).
   rewrite inv_de_next_outside by (right;lia).
   unfold de62_next_rho,inv_de_rho;rewrite (proj2 (Nat.ltb_ge n 10) N);reflexivity.
Qed.

Lemma inv_de_other_indices r j : (r=0%nat \/ r=4%nat \/ r=5%nat) -> (j<4)%nat ->
 (inv_de_select j<7)%nat /\ r<>inv_de_select j.
Proof.
 intros R J;destruct R as [R|[R|R]];subst r;destruct j as [|[|[|[|j]]]];try lia;
  cbn [inv_de_select nth];split;lia.
Qed.
Lemma inv_de_other_outside beta r : inv_loop_distinct beta -> (r=0%nat \/ r=4%nat \/ r=5%nat) ->
 forall pos,~foot (inv_de_layout beta) (map rshape de62_regs) (blk beta r) pos.
Proof.
 intros Distinct R pos (j & sh & d & ch & At & Member & Equal & Range).
 assert (J : (j<4)%nat).
 { change (j<length (map rshape de62_regs))%nat;apply nth_error_Some;rewrite At;discriminate. }
 rewrite inv_de_block in Equal by exact J.
 destruct (inv_de_other_indices r j R J) as (Bound & Ne).
 apply (Distinct r (inv_de_select j) ltac:(destruct R as [R|[R|R]];subst r;lia) Bound Ne);exact Equal.
Qed.

Lemma inv_de_restore_parts rho beta m : rep (de62_next_rho (inv_de_rho rho)) (inv_de_layout beta) de62_regs m ->
 region_ok (inv_de_next_rho rho) beta m 1 (nth 1 inv_loop_regs (mkreg [] false None)) /\
 region_ok (inv_de_next_rho rho) beta m 2 (nth 2 inv_loop_regs (mkreg [] false None)) /\
 region_ok (inv_de_next_rho rho) beta m 3 (nth 3 inv_loop_regs (mkreg [] false None)) /\
 region_ok (inv_de_next_rho rho) beta m 6 (nth 6 inv_loop_regs (mkreg [] false None)).
Proof.
 intro Rep;split;[|split;[|split]].
 - eapply region_u64_transport with (rho:=de62_next_rho (inv_de_rho rho)) (beta:=inv_de_layout beta) (r:=3%nat)
    (xs:=map XLc modinfo_fe_words) (ys:=map XLc modinfo_fe_words);
    try reflexivity;exact (rep_region _ _ _ _ 3 _ Rep eq_refl).
 - eapply region_u64_transport with (rho:=de62_next_rho (inv_de_rho rho)) (beta:=inv_de_layout beta) (r:=0%nat)
    (xs:=vars5 0) (ys:=vars5 5);try reflexivity;exact (rep_region _ _ _ _ 0 _ Rep eq_refl).
 - eapply region_u64_transport with (rho:=de62_next_rho (inv_de_rho rho)) (beta:=inv_de_layout beta) (r:=1%nat)
    (xs:=vars5 5) (ys:=vars5 10);try reflexivity;exact (rep_region _ _ _ _ 1 _ Rep eq_refl).
 - eapply region_u64_transport with (rho:=de62_next_rho (inv_de_rho rho)) (beta:=inv_de_layout beta) (r:=2%nat)
    (xs:=[XLv 10;XLv 11;XLv 12;XLv 13]) (ys:=[XLv 25;XLv 26;XLv 27;XLv 28]);
    try reflexivity;exact (rep_region _ _ _ _ 2 _ Rep eq_refl).
Qed.

Theorem inv_de_restore_caller rho beta m mf : rep rho beta inv_loop_regs m ->
 rep (de62_next_rho (inv_de_rho rho)) (inv_de_layout beta) de62_regs mf ->
 lframe (fun b ofs=>~foot (inv_de_layout beta) (map rshape de62_regs) b ofs) m mf ->
 rep (inv_de_next_rho rho) beta inv_loop_regs mf.
Proof.
 intros Rep Updated Frame;pose proof (inv_loop_rep_distinct rho beta m Rep) as Distinct.
 destruct (inv_de_restore_parts rho beta mf Updated) as (Metadata & D & E & T).
 destruct Rep as (Size & Sep & Regions);split;[exact Size|];split;[exact Sep|].
 intros r reg At;assert (R : (r<7)%nat) by (change (r<length inv_loop_regs)%nat;apply nth_error_Some;rewrite At;discriminate).
 destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;
  cbn [inv_loop_regs nth_error] in At;injection At as <-.
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=0%nat) (xs:=vars5 0) (ys:=vars5 0);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply inv_de_other_outside;[exact Distinct|auto]|exact (Regions 0%nat _ eq_refl)].
 - exact Metadata.
 - exact D.
 - exact E.
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=4%nat) (xs:=vars5 15) (ys:=vars5 15);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply inv_de_other_outside;[exact Distinct|auto]|exact (Regions 4%nat _ eq_refl)].
 - eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=5%nat) (xs:=vars5 20) (ys:=vars5 20);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply inv_de_other_outside;[exact Distinct|auto]|exact (Regions 5%nat _ eq_refl)].
 - exact T.
Qed.

Corollary exec_inv_de_caller rho beta e le m : rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e ->
 le!_modinfo=Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
 (forall high,de62_row_bound (inv_de_rho rho) high) -> de62_state_bounds (inv_de_rho rho) -> exists mf,
 Clight2.exec_stmt secp_ge e le m inv_de_statement E0 le mf Out_normal /\
 rep (inv_de_next_rho rho) beta inv_loop_regs mf /\
 de62_state_bounds (de62_next_rho (inv_de_rho rho)) /\
 (forall high,
  2^62*de62_input_value (de62_next_rho (inv_de_rho rho)) high=de62_matrix_value (inv_de_rho rho) high+
   feP*de62_correction_value (inv_de_rho rho) high /\
  (2^62*de62_input_value (de62_next_rho (inv_de_rho rho)) high-de62_matrix_value (inv_de_rho rho) high) mod feP=0) /\
 lframe (fun b ofs=>~foot (inv_de_layout beta) (map rshape de62_regs) b ofs) m mf.
Proof.
 intros Rep Env Modinfo Rows Bounds;destruct (exec_inv_de_call rho beta e le m Rep Env Modinfo Rows Bounds)
  as (mf & Exec & Out & NextBounds & Numeric & Frame).
 exists mf;split;[exact Exec|];split;[eapply inv_de_restore_caller;eassumption|];split;[exact NextBounds|];split;assumption.
Qed.
