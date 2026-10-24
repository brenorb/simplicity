(** Caller-owned inverse state and f/g execution for either six-word
    modulus. Reuse the checked modulus-independent f/g helper and revalue
    lemmas; changing metadata never changes the generated C program. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem
 C.jet_sx_u64_transport C.jet_sx_region_lframe C.jet_secp_linkage C.jets_secp
 C.jet_secp_fns C.jet_secp_curve_statements C.jet_secp_fe_nv C.jet_secp_local_regions
 C.jet_secp_modinv_entry_modulus C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_de
 C.jet_secp_modinv_var_fg C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_owned
 C.jet_secp_modinv_fg_body C.jet_secp_modinv_fg_start C.jet_secp_modinv_fg_finish_numeric
 C.jet_secp_modinfo_fe_copy C.jet_secp_modinv_fg_loop_numeric C.jet_secp_u128_shift64_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition inv_mod_loop_regs mu :=
 [mkreg(u64_cells 0 (vars5 0)) true (Some 40);
  mkreg(u64_cells 0 (map XLc(inv_mod_words mu))) false None;
  mkreg(u64_cells 0 (vars5 5)) true (Some 40);
  mkreg(u64_cells 0 (vars5 10)) true (Some 40);
  mkreg(u64_cells 0 (vars5 15)) true (Some 40);
  mkreg(u64_cells 0 (vars5 20)) true (Some 40);
  mkreg(u64_cells 0 [XLv 25;XLv 26;XLv 27;XLv 28]) true (Some 32)].
Lemma inv_mod_loop_field : inv_mod_loop_regs modinfo_fe_limb=inv_loop_regs.
Proof. reflexivity. Qed.
Lemma inv_mod_loop_none mu r : (r<7)%nat ->
 rfree(nth r (inv_mod_loop_regs mu) (mkreg [] false None))=None -> r=1%nat.
Proof. destruct r as [|[|[|[|[|[|[|r]]]]]]];intros R E;try lia;try discriminate;reflexivity. Qed.
Lemma inv_mod_loop_distinct mu rho beta m : rep rho beta (inv_mod_loop_regs mu) m -> inv_loop_distinct beta.
Proof.
 intros(_ & Sep & _) i j I J Ne.
 pose proof(nth_error_nth' (inv_mod_loop_regs mu) (mkreg [] false None) I) as AtI.
 pose proof(nth_error_nth' (inv_mod_loop_regs mu) (mkreg [] false None) J) as AtJ.
 destruct(Sep i j _ _ Ne AtI AtJ) as[Different | [NoI [NoJ _]]];[exact Different|].
 exfalso;apply Ne;rewrite(inv_mod_loop_none mu i I NoI),(inv_mod_loop_none mu j J NoJ);reflexivity.
Qed.
Lemma inv_mod_owned_base mu rho beta m r : rep rho beta (inv_mod_loop_regs mu) m ->
 (r<7)%nat -> r<>1%nat -> bas beta r=0.
Proof.
 intros Rep R Ne;destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;
 eapply rep_owned_region_base_zero;[exact Rep|reflexivity|reflexivity|
 exact Rep|reflexivity|reflexivity|exact Rep|reflexivity|reflexivity|
 exact Rep|reflexivity|reflexivity|exact Rep|reflexivity|reflexivity|exact Rep|reflexivity|reflexivity].
Qed.

Theorem inv_mod_fg_project mu len rho beta m : rep rho beta (inv_mod_loop_regs mu) m ->
 rep (inv_fg_rho len rho) (inv_fg_layout beta) fg_owned_regs m.
Proof.
 intro Rep;apply fg_rep_three.
 - reflexivity.
 - apply fg_distinct_three_sep;apply inv_fg_separate;exact(inv_mod_loop_distinct mu rho beta m Rep).
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=4%nat)
    (xs:=vars5 15) (ys:=vars5 0);try reflexivity;exact(rep_region _ _ _ _ 4 _ Rep eq_refl).
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=5%nat)
    (xs:=vars5 20) (ys:=vars5 5);try reflexivity;exact(rep_region _ _ _ _ 5 _ Rep eq_refl).
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=6%nat)
    (xs:=[XLv 25;XLv 26;XLv 27;XLv 28]) (ys:=[XLv 10;XLv 11;XLv 12;XLv 13]);
    try reflexivity;exact(rep_region _ _ _ _ 6 _ Rep eq_refl).
Qed.

Lemma inv_mod_de_arguments mu rho beta e le m : rep rho beta (inv_mod_loop_regs mu) m ->
 ematch beta (snd inv_start_alloc) e ->
 le!_modinfo=Some(Vptr(blk beta 1)(Ptrofs.repr(bas beta 1))) ->
 eval_exprlist secp_ge e le m [inv_s62_address _d;inv_s62_address _e;inv_matrix_address;inv_metadata_arg]
 (type_of_params(fn_params f_secp256k1_modinv64_update_de_62))
 [Vptr(blk(inv_de_layout beta) 0)(Ptrofs.repr(bas(inv_de_layout beta) 0));
  Vptr(blk(inv_de_layout beta) 1)(Ptrofs.repr(bas(inv_de_layout beta) 1));
  Vptr(blk(inv_de_layout beta) 2)(Ptrofs.repr(bas(inv_de_layout beta) 2));
  Vptr(blk(inv_de_layout beta) 3)(Ptrofs.repr(bas(inv_de_layout beta) 3))].
Proof.
 intros Rep Env Modinfo;rewrite !inv_de_base,!inv_de_block by lia;cbn [inv_de_select nth].
 rewrite(inv_mod_owned_base mu rho beta m 2 Rep ltac:(lia) ltac:(lia)),
  (inv_mod_owned_base mu rho beta m 3 Rep ltac:(lia) ltac:(lia)),
  (inv_mod_owned_base mu rho beta m 6 Rep ltac:(lia) ltac:(lia)).
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact(proj1(Env _d))|reflexivity|].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact(proj1(Env _e))|reflexivity|].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact(proj1(Env _t))|reflexivity|].
 eapply eval_Econs;[apply eval_Etempvar;exact Modinfo|reflexivity|constructor].
Qed.

Lemma inv_mod_fg_arguments mu len rho beta e le m : rep rho beta (inv_mod_loop_regs mu) m ->
 ematch beta (snd inv_start_alloc) e -> le!_len=Some(Vint(Int.repr(Z.of_nat len))) ->
 eval_exprlist secp_ge e le m inv_fg_arguments (type_of_params(fn_params f_secp256k1_modinv64_update_fg_62_var))
 [Vint(Int.repr(Z.of_nat len));
  Vptr(blk(inv_fg_layout beta) 0)(Ptrofs.repr(bas(inv_fg_layout beta) 0));
  Vptr(blk(inv_fg_layout beta) 1)(Ptrofs.repr(bas(inv_fg_layout beta) 1));
  Vptr(blk(inv_fg_layout beta) 2)(Ptrofs.repr(bas(inv_fg_layout beta) 2))].
Proof.
 intros Rep Env Len;rewrite !inv_fg_base,!inv_fg_block by lia;cbn [inv_fg_select nth].
 rewrite(inv_mod_owned_base mu rho beta m 4 Rep ltac:(lia) ltac:(lia)),
  (inv_mod_owned_base mu rho beta m 5 Rep ltac:(lia) ltac:(lia)),
  (inv_mod_owned_base mu rho beta m 6 Rep ltac:(lia) ltac:(lia)).
 eapply eval_Econs;[apply eval_Etempvar;exact Len|reflexivity|].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact(proj1(Env _f))|reflexivity|].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact(proj1(Env _g))|reflexivity|].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact(proj1(Env _t))|reflexivity|constructor].
Qed.

Theorem inv_mod_fg_restore mu len rho beta m mf : (0<len<=5)%nat -> rep rho beta (inv_mod_loop_regs mu) m ->
 rep (fg_body_rho len (inv_fg_rho len rho)) (inv_fg_layout beta) (fg_owned_out len) mf ->
 lframe(fun b ofs=>~foot (inv_fg_layout beta) (map rshape fg_regs) b ofs) m mf ->
 rep (inv_fg_next_rho len rho) beta (inv_mod_loop_regs mu) mf.
Proof.
 intros Len Rep Updated Frame;pose proof(inv_mod_loop_distinct mu rho beta m Rep) as Distinct.
 pose proof(inv_fg_restore_array len rho beta mf false Len Updated) as F.
 pose proof(inv_fg_restore_array len rho beta mf true Len Updated) as G.
 pose proof(inv_fg_restore_matrix len rho beta mf Len Updated) as T.
 destruct Rep as(Size & Sep & Regions);split;[exact Size|];split;[exact Sep|].
 intros r reg At;assert(R:(r<7)%nat) by(change(r<length(inv_mod_loop_regs mu))%nat;apply nth_error_Some;rewrite At;discriminate).
 destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;cbn [inv_mod_loop_regs nth_error] in At;injection At as <-.
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=0%nat) (xs:=vars5 0) (ys:=vars5 0);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply inv_fg_other_outside;[exact Distinct|lia]|exact(Regions 0%nat _ eq_refl)].
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=1%nat)
    (xs:=map XLc(inv_mod_words mu)) (ys:=map XLc(inv_mod_words mu));try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply inv_fg_other_outside;[exact Distinct|lia]|exact(Regions 1%nat _ eq_refl)].
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=2%nat) (xs:=vars5 5) (ys:=vars5 5);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply inv_fg_other_outside;[exact Distinct|lia]|exact(Regions 2%nat _ eq_refl)].
 - eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=3%nat) (xs:=vars5 10) (ys:=vars5 10);try reflexivity.
   eapply region_ok_lframe;[exact Frame|apply inv_fg_other_outside;[exact Distinct|lia]|exact(Regions 3%nat _ eq_refl)].
 - exact F.
 - exact G.
 - exact T.
Qed.

Theorem exec_inv_mod_fg_caller mu len rho beta e le m : (0<len<=5)%nat ->
 rep rho beta (inv_mod_loop_regs mu) m -> ematch beta (snd inv_start_alloc) e ->
 le!_len=Some(Vint(Int.repr(Z.of_nat len))) -> fg_input_bounds(inv_fg_rho len rho) -> exists mf,
 Clight2.exec_stmt secp_ge e le m inv_fg_statement E0 le mf Out_normal /\
 rep (inv_fg_next_rho len rho) beta (inv_mod_loop_regs mu) mf /\
 (forall high,fg_body_value len (inv_fg_rho len rho) high=fg_matrix_value(inv_fg_rho len rho) high len/2^62) /\
 lframe(fun b ofs=>~foot (inv_fg_layout beta) (map rshape fg_regs) b ofs) m mf.
Proof.
 intros Length Rep Env Len Bounds.
 destruct(eval_fg_transition_owned len (inv_fg_rho len rho) (inv_fg_layout beta) m
  Length (inv_fg_length len rho Length) Bounds (inv_mod_fg_project mu len rho beta m Rep))
  as(mf & Call & Words & Numeric & Out & Frame).
 exists mf;split.
 - rewrite inv_fg_statement_source;eapply exec_curve_call with(result:=None) (v:=Vundef).
   + unfold secp_pure;repeat(first[left;reflexivity|right]).
   + exact(proj1(Env _secp256k1_modinv64_update_fg_62_var)).
   + exact(inv_mod_fg_arguments mu len rho beta e le m Rep Env Len).
   + exact Call.
 - split;[eapply inv_mod_fg_restore;eassumption|];split;assumption.
Qed.
