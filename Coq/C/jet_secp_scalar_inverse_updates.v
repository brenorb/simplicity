(** The actual scalar inverse's coefficient/f-g call pair in one live
    caller-owned state. The incoming bounds/matrix are loop obligations;
    the calls, new representation, exact values and frames are derived. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_eval C.jet_sx_mem
 C.jet_sx_u64_transport C.jet_sx_region_lframe C.jet_secp_linkage C.jets_secp
 C.jet_secp_fns C.jet_secp_curve_statements C.jet_secp_fe_nv C.jet_secp_modinv_loop_modulus
 C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg
 C.jet_secp_modinv_de_exec C.jet_secp_modinv_de_revalue C.jet_secp_modinv_de_numeric
 C.jet_secp_modinv_de_correction_numeric C.jet_secp_scalar_de_exec C.jet_secp_scalar_de_numeric
 C.jet_secp_scalar_de_ranges C.jet_secp_scalar_de_revalue C.jet_secp_scalar_normalize62
 C.jet_secp_modinv_normalize62_modulus C.jet_secp_modinv_normalize62_words
 C.jet_secp_modinv_fg_loop_numeric C.jet_secp_modinv_fg_start C.jet_secp_modinv_fg_prefix
 C.jet_secp_modinv_fg_body C.jet_secp_modinv_fg_finish_numeric C.jet_secp_canonical_scalar
 C.jet_secp_modinv_fg_iteration_numeric C.jet_secp_scalar_de_invariant
 C.jet_secp_modinv_var_invariant C.jet_secp_modinv_var_ranges C.jet_secp_modinv_var_tail C.divstep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_inv_de_next_rho (rho : nat->int64) n :=
 if (5<=?n)%nat && (n<?15)%nat then scalar_de62_next_rho(inv_de_rho rho)(n-5)%nat else rho n.
Lemma scalar_inv_de_next_outside rho n : ((n<5)%nat \/ (15<=n)%nat) -> scalar_inv_de_next_rho rho n=rho n.
Proof.
 intro Outside;unfold scalar_inv_de_next_rho;destruct(Nat.leb_spec 5 n),(Nat.ltb_spec n 15);try lia;reflexivity.
Qed.

Lemma scalar_inv_de_next_project rho n : inv_de_rho(scalar_inv_de_next_rho rho) n=scalar_de62_next_rho(inv_de_rho rho) n.
Proof.
 destruct(Nat.lt_ge_cases n 10) as[N|N].
 - destruct n as [|[|[|[|[|[|[|[|[|[|n]]]]]]]]]];try lia;reflexivity.
 - unfold inv_de_rho at 1;rewrite(proj2(Nat.ltb_ge n 10) N).
   rewrite scalar_inv_de_next_outside by(right;lia).
   unfold scalar_de62_next_rho,inv_de_rho;rewrite(proj2(Nat.ltb_ge n 10) N);reflexivity.
Qed.

Theorem scalar_inv_de_project rho beta m : rep rho beta (inv_mod_loop_regs modinfo_scalar_limb) m ->
 rep (inv_de_rho rho) (inv_de_layout beta) scalar_de62_regs m.
Proof.
 intro Rep;apply de62_rep_four.
 - reflexivity.
 - eapply rsep_shape with(regs:=de62_regs);[reflexivity|].
   apply inv_de_separate;exact(inv_mod_loop_distinct modinfo_scalar_limb rho beta m Rep).
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=2%nat)
    (xs:=vars5 5) (ys:=vars5 0);try reflexivity;exact(rep_region _ _ _ _ 2 _ Rep eq_refl).
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=3%nat)
    (xs:=vars5 10) (ys:=vars5 5);try reflexivity;exact(rep_region _ _ _ _ 3 _ Rep eq_refl).
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=6%nat)
    (xs:=[XLv 25;XLv 26;XLv 27;XLv 28]) (ys:=[XLv 10;XLv 11;XLv 12;XLv 13]);
    try reflexivity;exact(rep_region _ _ _ _ 6 _ Rep eq_refl).
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=1%nat)
    (xs:=map XLc C.jet_secp_modinfo_scalar_global.modinfo_scalar_words)
    (ys:=map XLc C.jet_secp_modinfo_scalar_global.modinfo_scalar_words);
    try reflexivity;exact(rep_region _ _ _ _ 1 _ Rep eq_refl).
Qed.

Theorem scalar_inv_de_restore rho beta m mf : rep rho beta (inv_mod_loop_regs modinfo_scalar_limb) m ->
 rep (scalar_de62_next_rho(inv_de_rho rho)) (inv_de_layout beta) scalar_de62_regs mf ->
 lframe(fun b ofs=>~foot (inv_de_layout beta) (map rshape scalar_de62_regs) b ofs) m mf ->
 rep (scalar_inv_de_next_rho rho) beta (inv_mod_loop_regs modinfo_scalar_limb) mf.
Proof.
 intros Rep Updated Frame;pose proof(inv_mod_loop_distinct modinfo_scalar_limb rho beta m Rep) as Distinct.
 destruct Rep as(Size & Sep & Regions);split;[exact Size|];split;[exact Sep|].
 intros r reg At;assert(R:(r<7)%nat) by(change(r<length(inv_mod_loop_regs modinfo_scalar_limb))%nat;apply nth_error_Some;rewrite At;discriminate).
 destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;cbn [inv_mod_loop_regs nth_error] in At;injection At as <-.
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=0%nat) (xs:=vars5 0) (ys:=vars5 0);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply inv_de_other_outside;[exact Distinct|auto]|exact(Regions 0%nat _ eq_refl)].
 - eapply region_u64_transport with(rho:=scalar_de62_next_rho(inv_de_rho rho)) (beta:=inv_de_layout beta) (r:=3%nat)
    (xs:=map XLc C.jet_secp_modinfo_scalar_global.modinfo_scalar_words)
    (ys:=map XLc C.jet_secp_modinfo_scalar_global.modinfo_scalar_words);
    try reflexivity;exact(rep_region _ _ _ _ 3 _ Updated eq_refl).
 - eapply region_u64_transport with(rho:=scalar_de62_next_rho(inv_de_rho rho)) (beta:=inv_de_layout beta) (r:=0%nat)
    (xs:=vars5 0) (ys:=vars5 5);try reflexivity;exact(rep_region _ _ _ _ 0 _ Updated eq_refl).
 - eapply region_u64_transport with(rho:=scalar_de62_next_rho(inv_de_rho rho)) (beta:=inv_de_layout beta) (r:=1%nat)
    (xs:=vars5 5) (ys:=vars5 10);try reflexivity;exact(rep_region _ _ _ _ 1 _ Updated eq_refl).
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=4%nat) (xs:=vars5 15) (ys:=vars5 15);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply inv_de_other_outside;[exact Distinct|auto]|exact(Regions 4%nat _ eq_refl)].
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=5%nat) (xs:=vars5 20) (ys:=vars5 20);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply inv_de_other_outside;[exact Distinct|auto]|exact(Regions 5%nat _ eq_refl)].
 - eapply region_u64_transport with(rho:=scalar_de62_next_rho(inv_de_rho rho)) (beta:=inv_de_layout beta) (r:=2%nat)
    (xs:=[XLv 10;XLv 11;XLv 12;XLv 13]) (ys:=[XLv 25;XLv 26;XLv 27;XLv 28]);
    try reflexivity;exact(rep_region _ _ _ _ 2 _ Updated eq_refl).
Qed.

Theorem exec_scalar_inv_de_caller rho beta e le m : rep rho beta (inv_mod_loop_regs modinfo_scalar_limb) m ->
 ematch beta (snd inv_start_alloc) e -> le!_modinfo=Some(Vptr(blk beta 1)(Ptrofs.repr(bas beta 1))) ->
 (forall high,de62_row_bound(inv_de_rho rho) high) -> scalar_de62_state_bounds(inv_de_rho rho) -> exists mf,
 Clight2.exec_stmt secp_ge e le m inv_de_statement E0 le mf Out_normal /\
 rep (scalar_inv_de_next_rho rho) beta (inv_mod_loop_regs modinfo_scalar_limb) mf /\
 scalar_de62_state_bounds(scalar_de62_next_rho(inv_de_rho rho)) /\
 (forall high,2^62*de62_input_value(scalar_de62_next_rho(inv_de_rho rho)) high=
  de62_matrix_value(inv_de_rho rho) high+canonical_group_order*scalar_de62_correction_value(inv_de_rho rho) high /\
  (2^62*de62_input_value(scalar_de62_next_rho(inv_de_rho rho)) high-de62_matrix_value(inv_de_rho rho) high) mod canonical_group_order=0) /\
 lframe(fun b ofs=>~foot (inv_de_layout beta) (map rshape scalar_de62_regs) b ofs) m mf.
Proof.
 intros Rep Env Modinfo Rows Bounds.
 destruct(eval_scalar_de_step (inv_de_rho rho) (inv_de_layout beta) m (scalar_inv_de_project rho beta m Rep) Rows Bounds)
  as(mf & Call & Out & NextBounds & Numeric & Frame).
 exists mf;split.
 - rewrite inv_de_statement_source;eapply exec_curve_call with(result:=None) (v:=Vundef).
   + unfold secp_pure;repeat(first[left;reflexivity|right]).
   + exact(proj1(Env _secp256k1_modinv64_update_de_62)).
   + exact(inv_mod_de_arguments modinfo_scalar_limb rho beta e le m Rep Env Modinfo).
   + exact Call.
 - split;[eapply scalar_inv_de_restore;eassumption|];split;[exact NextBounds|];split;assumption.
Qed.

Lemma scalar_inv_fg_rho_after_de len rho n : inv_fg_rho len (scalar_inv_de_next_rho rho) n=inv_fg_rho len rho n.
Proof.
 unfold inv_fg_rho;destruct(Nat.ltb_spec n 14);[rewrite scalar_inv_de_next_outside by(right;lia)|];reflexivity.
Qed.
Lemma scalar_inv_fg_bounds_after_de len rho : fg_input_bounds(inv_fg_rho len rho) ->
 fg_input_bounds(inv_fg_rho len (scalar_inv_de_next_rho rho)).
Proof.
 intros(Rows & Limbs);split.
 - intro high;unfold fg_iter_u,fg_iter_v;rewrite !scalar_inv_fg_rho_after_de;apply Rows.
 - intros high j J;unfold fg_array_word;rewrite scalar_inv_fg_rho_after_de;apply Limbs;exact J.
Qed.

Definition scalar_inv_updates := Ssequence inv_de_statement inv_fg_statement.
Definition scalar_inv_updates_rho len rho := inv_fg_next_rho len (scalar_inv_de_next_rho rho).
Lemma scalar_inv_updates_source : firstn 2 (skipn 2 (fst C.jet_secp_modinv_var_zero.inv_caller_loop_parts))=
 [inv_de_statement;inv_fg_statement].
Proof. reflexivity. Qed.
Lemma scalar_inv_updates_de_word len rho n : inv_de_rho(scalar_inv_updates_rho len rho) n=
 scalar_de62_next_rho(inv_de_rho rho) n.
Proof.
 rewrite <-scalar_inv_de_next_project;unfold scalar_inv_updates_rho,inv_de_rho.
 destruct(Nat.ltb_spec n 10);rewrite inv_fg_next_outside by(first[left;lia|right;lia]);reflexivity.
Qed.
Lemma scalar_inv_updates_de_array len rho high i : de62_array(inv_de_rho(scalar_inv_updates_rho len rho)) high i=
 de62_array(scalar_de62_next_rho(inv_de_rho rho)) high i.
Proof. unfold de62_array;destruct high;apply scalar_inv_updates_de_word. Qed.
Lemma scalar_inv_updates_de_value len rho high : de62_input_value(inv_de_rho(scalar_inv_updates_rho len rho)) high=
 de62_input_value(scalar_de62_next_rho(inv_de_rho rho)) high.
Proof.
 unfold de62_input_value;apply norm62_value_ext;intros i I;rewrite scalar_inv_updates_de_word;reflexivity.
Qed.
Lemma scalar_inv_updates_de_bounds len rho : scalar_de62_state_bounds(scalar_de62_next_rho(inv_de_rho rho)) ->
 scalar_de62_state_bounds(inv_de_rho(scalar_inv_updates_rho len rho)).
Proof.
 intros(Limbs & Values);split.
 - intros high i I;rewrite scalar_inv_updates_de_array;apply Limbs;exact I.
 - intro high;rewrite scalar_inv_updates_de_value;apply Values.
Qed.

Theorem exec_scalar_inv_updates len rho beta e le m : (0<len<=5)%nat ->
 rep rho beta (inv_mod_loop_regs modinfo_scalar_limb) m -> ematch beta (snd inv_start_alloc) e ->
 le!_modinfo=Some(Vptr(blk beta 1)(Ptrofs.repr(bas beta 1))) -> le!_len=Some(Vint(Int.repr(Z.of_nat len))) ->
 (forall high,de62_row_bound(inv_de_rho rho) high) -> scalar_de62_state_bounds(inv_de_rho rho) ->
 fg_input_bounds(inv_fg_rho len rho) -> exists mf,
 Clight2.exec_stmt secp_ge e le m scalar_inv_updates E0 le mf Out_normal /\
 rep (scalar_inv_updates_rho len rho) beta (inv_mod_loop_regs modinfo_scalar_limb) mf /\
 scalar_de62_state_bounds(inv_de_rho(scalar_inv_updates_rho len rho)) /\
 (forall high,2^62*de62_input_value(inv_de_rho(scalar_inv_updates_rho len rho)) high=
   de62_matrix_value(inv_de_rho rho) high+canonical_group_order*scalar_de62_correction_value(inv_de_rho rho) high /\
   (2^62*de62_input_value(inv_de_rho(scalar_inv_updates_rho len rho)) high-de62_matrix_value(inv_de_rho rho) high) mod canonical_group_order=0) /\
 (forall high,inv_fg_active_value len (scalar_inv_updates_rho len rho) high=
   fg_matrix_value(inv_fg_rho len (scalar_inv_de_next_rho rho)) high len/2^62) /\
 lframe(fun b ofs=>~foot (inv_de_layout beta) (map rshape scalar_de62_regs) b ofs /\
   ~foot (inv_fg_layout beta) (map rshape fg_regs) b ofs) m mf.
Proof.
 intros Length Rep Env Modinfo Len Rows Bounds FG.
 destruct(exec_scalar_inv_de_caller rho beta e le m Rep Env Modinfo Rows Bounds)
  as(md & DECall & DERep & DEBounds & DENumeric & DEFrame).
 destruct(exec_inv_mod_fg_caller modinfo_scalar_limb len (scalar_inv_de_next_rho rho) beta e le md
  Length DERep Env Len (scalar_inv_fg_bounds_after_de len rho FG))
  as(mf & FGCall & Out & FGNumeric & FGFrame).
 exists mf;split.
 - unfold scalar_inv_updates;eapply exec_Sseq_1 with(t1:=E0) (t2:=E0) (le1:=le) (m1:=md);eassumption.
 - split;[exact Out|];split;[apply scalar_inv_updates_de_bounds;exact DEBounds|];split.
   + intro high;rewrite scalar_inv_updates_de_value;exact(DENumeric high).
   + split.
     * intro high;unfold scalar_inv_updates_rho;rewrite inv_fg_next_value by exact Length;apply FGNumeric.
     * eapply lframe_trans;[eapply lframe_implies;[exact DEFrame|]|eapply lframe_implies;[exact FGFrame|]];
       intros b ofs [DEOutside FGOutside] Valid;assumption.
Qed.

Lemma scalar_inv_fg_value_after_de len rho high : inv_fg_active_value len (scalar_inv_de_next_rho rho) high=
 inv_fg_active_value len rho high.
Proof.
 unfold inv_fg_active_value;apply norm62_value_ext;intros i I.
 rewrite scalar_inv_de_next_outside by(right;destruct high;lia);reflexivity.
Qed.
Lemma scalar_inv_fg_matrix_after_de len rho high : (0<len<=5)%nat ->
 fg_matrix_value(inv_fg_rho len (scalar_inv_de_next_rho rho)) high len=
 inv_matrix_u rho high*inv_fg_active_value len rho false+inv_matrix_v rho high*inv_fg_active_value len rho true.
Proof.
 intro Length;unfold fg_matrix_value;rewrite !inv_fg_input_value by exact Length.
 rewrite !scalar_inv_fg_value_after_de;destruct high;reflexivity.
Qed.
Lemma scalar_inv_updates_scaled_state len rho st high : (0<len<=5)%nat ->
 inv_state_matches len rho st -> inv_matrix_matches rho st ->
 fg_matrix_value(inv_fg_rho len (scalar_inv_de_next_rho rho)) high len=
 2^62*(if high then g(fst(stepN 62 st)) else f(fst(stepN 62 st))).
Proof.
 intros Length State Matrix;rewrite scalar_inv_fg_matrix_after_de by exact Length.
 rewrite <-(inv_fg_matrix_value len rho high Length);apply inv_matrix_scaled_state;assumption.
Qed.

Lemma scalar_inv_updates_state_matches len rho st : (0<len<=5)%nat ->
 inv_state_matches len rho st -> inv_matrix_matches rho st ->
 (forall high,inv_fg_active_value len (scalar_inv_updates_rho len rho) high=
  fg_matrix_value(inv_fg_rho len (scalar_inv_de_next_rho rho)) high len/2^62) ->
 inv_state_matches len (scalar_inv_updates_rho len rho) (fst(stepN 62 st)).
Proof.
 intros Length State Matrix Numeric;split;rewrite Numeric,(scalar_inv_updates_scaled_state len rho st _ Length State Matrix);
 rewrite Z.mul_comm,Z.div_mul by lia;reflexivity.
Qed.

Lemma scalar_inv_updates_coefficient_link value len rho st : inv_matrix_matches rho st ->
 scalar_de62_coefficient_link value (inv_de_rho rho) st ->
 (forall high,2^62*de62_input_value(inv_de_rho(scalar_inv_updates_rho len rho)) high=
  de62_matrix_value(inv_de_rho rho) high+canonical_group_order*scalar_de62_correction_value(inv_de_rho rho) high) ->
 scalar_de62_coefficient_link value (inv_de_rho(scalar_inv_updates_rho len rho)) (fst(stepN 62 st)).
Proof.
 intros Matrix Link Numeric high;rewrite scalar_inv_updates_de_value.
 apply(scalar_de62_next_coefficient_link value (inv_de_rho rho) st Matrix Link).
 intro h;rewrite <-(scalar_inv_updates_de_value len rho h);apply Numeric.
Qed.

(** Canonical matrix/state relations are internal incoming obligations, not
    assumed C calls. Both real updates and all next-state conclusions follow. *)
Theorem exec_scalar_inv_updates_invariant value len rho st beta e le m : (0<len<=5)%nat ->
 rep rho beta (inv_mod_loop_regs modinfo_scalar_limb) m -> ematch beta (snd inv_start_alloc) e ->
 le!_modinfo=Some(Vptr(blk beta 1)(Ptrofs.repr(bas beta 1))) -> le!_len=Some(Vint(Int.repr(Z.of_nat len))) ->
 scalar_de62_state_bounds(inv_de_rho rho) -> inv_state_matches len rho st -> inv_matrix_matches rho st ->
 scalar_de62_coefficient_link value (inv_de_rho rho) st ->
 (forall high j,(j<5)%nat -> Z.abs(Int64.signed(fg_array_word(inv_fg_rho len rho) high j))<=2^62) -> exists mf,
 Clight2.exec_stmt secp_ge e le m scalar_inv_updates E0 le mf Out_normal /\
 rep (scalar_inv_updates_rho len rho) beta (inv_mod_loop_regs modinfo_scalar_limb) mf /\
 scalar_de62_state_bounds(inv_de_rho(scalar_inv_updates_rho len rho)) /\
 scalar_de62_coefficient_link value (inv_de_rho(scalar_inv_updates_rho len rho)) (fst(stepN 62 st)) /\
 inv_state_matches len (scalar_inv_updates_rho len rho) (fst(stepN 62 st)) /\
 inv_tail_low_bounds len (scalar_inv_updates_rho len rho) /\
 (g st=0 -> de62_input_value(inv_de_rho(scalar_inv_updates_rho len rho)) false mod canonical_group_order=
   de62_input_value(inv_de_rho rho) false mod canonical_group_order) /\
 (forall high,2^62*de62_input_value(inv_de_rho(scalar_inv_updates_rho len rho)) high=
   de62_matrix_value(inv_de_rho rho) high+canonical_group_order*scalar_de62_correction_value(inv_de_rho rho) high /\
   (2^62*de62_input_value(inv_de_rho(scalar_inv_updates_rho len rho)) high-de62_matrix_value(inv_de_rho rho) high) mod canonical_group_order=0) /\
 (forall high,inv_fg_active_value len (scalar_inv_updates_rho len rho) high=
   fg_matrix_value(inv_fg_rho len (scalar_inv_de_next_rho rho)) high len/2^62) /\
 lframe(fun b ofs=>~foot (inv_de_layout beta) (map rshape scalar_de62_regs) b ofs /\
   ~foot (inv_fg_layout beta) (map rshape fg_regs) b ofs) m mf.
Proof.
 intros Length Rep Env Modinfo Len Bounds State Matrix Link Limbs.
 destruct(exec_scalar_inv_updates len rho beta e le m Length Rep Env Modinfo Len
   (inv_matrix_row_bounds rho st Matrix) Bounds (inv_fg_bounds_from_matrix len rho st Matrix Limbs))
  as(mf & Exec & Out & NextBounds & DENumeric & FGNumeric & Frame).
 exists mf;split;[exact Exec|];split;[exact Out|];split;[exact NextBounds|];split.
 - apply(scalar_inv_updates_coefficient_link value len rho st Matrix Link);intro high;exact(proj1(DENumeric high)).
 - split;[exact(scalar_inv_updates_state_matches len rho st Length State Matrix FGNumeric)|];split.
   + apply inv_fg_next_low;exact Length.
   + split.
     * intro Zero;rewrite scalar_inv_updates_de_value.
       apply(scalar_de62_zero_coefficient (inv_de_rho rho) st Zero Matrix).
       rewrite <-(scalar_inv_updates_de_value len rho false);exact(proj1(DENumeric false)).
     * split;[exact DENumeric|];split;assumption.
Qed.
