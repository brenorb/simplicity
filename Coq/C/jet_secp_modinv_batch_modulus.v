(** Actual inverse caller loads and complete divstep call, for either modulus.
    The counting-call premise is explicit, internal, and still undischarged.
    Matrix values are derived from execution, never assumed initialized. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.extraMath C.divstep C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_eval
 C.jet_sx_mem C.jet_sx_region_lframe C.jet_sx_u64_transport C.jet_sx_forget_cells
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_modinv_loop_modulus C.jet_secp_modinv_seed_modulus C.jet_secp_modinv_entry_modulus
 C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_seed C.jet_secp_modinv_var_de
 C.jet_secp_modinv_var_fg C.jet_secp_modinv_var_invariant C.jet_secp_modinv_var_first_batch
 C.jet_secp_modinv_var_batch_entry C.jet_secp_modinv_var_batch_exit
 C.jet_secp_div62_loop C.jet_secp_div62_exit C.jet_secp_local_regions C.jet_secp_fe_nv
 C.jet_secp_u128_shift64_rep C.jet_secp_statement_prefix.
Require Import C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma inv_mod_pre_batch_regs mu : inv_mod_seed_regs mu=forget_after 6 (inv_mod_loop_regs mu).
Proof. reflexivity. Qed.
Lemma inv_mod_pre_batch_forget mu rho beta m : rep rho beta (inv_mod_loop_regs mu) m ->
 rep rho beta (inv_mod_seed_regs mu) m.
Proof. intro Rep;rewrite inv_mod_pre_batch_regs;apply rep_forget_after;exact Rep. Qed.

Lemma inv_mod_batch_low_load mu rho beta m (high : bool) : rep rho beta (inv_mod_seed_regs mu) m ->
 Mem.load Mint64 m (blk beta (if high then 5 else 4)) 0=
 Some(Vlong(rho (if high then 20 else 15)%nat)).
Proof.
 intro Rep.
 assert(Base:bas beta (if high then 5 else 4)=0).
 { destruct high;eapply rep_owned_region_base_zero;[exact Rep|reflexivity|reflexivity|
   exact Rep|reflexivity|reflexivity]. }
 assert(Load:xload (inv_mod_seed_regs mu) (if high then 5 else 4) 0 tulong=
   Some(XLv(if high then 20 else 15))) by(destruct high;reflexivity).
 pose proof(xload_u64_defined_sound _ _ _ _ _ _ _ Rep Load) as Word.
 rewrite Base,Z.add_0_l in Word;destruct high;exact Word.
Qed.

Theorem inv_mod_batch_restore mu st rho beta m mf : rep rho beta (inv_mod_seed_regs mu) m ->
 Mem.range_perm mf (blk beta 6) 0 32 Cur Freeable ->
 (forall j,(j<4)%nat -> Mem.load Mint64 mf (blk beta 6) (8*Z.of_nat j)=Some(Vlong(div62_exit_words st j))) ->
 lframe(fun b _=>b<>blk beta 6) m mf ->
 rep (inv_batch_result_rho st rho) beta (inv_mod_loop_regs mu) mf.
Proof.
 intros Rep Free Loads Frame;pose proof Rep as(Len & Sep & Regions).
 assert(Base:bas beta 6=0).
 { exact(proj1(rep_free_region rho beta (inv_mod_seed_regs mu) m 6 32 Rep
   ltac:(change(6<7)%nat;lia) eq_refl)). }
 assert(Others:forall r reg,nth_error(inv_mod_seed_regs mu) r=Some reg -> r<>6%nat ->
   region_ok rho beta mf r reg).
 { intros r reg At Ne;eapply region_ok_lframe;[exact Frame| |exact(Regions _ _ At)].
   intros pos;destruct(Sep r 6%nat reg inv_seed_matrix Ne At eq_refl) as[Different|(_ & NoOwner & _)];
   [exact Different|discriminate NoOwner]. }
 split;[exact Len|];split.
 - apply(rsep_shape beta (inv_mod_seed_regs mu));[reflexivity|exact Sep].
 - intros r reg At;assert(R:(r<7)%nat) by
   (change(r<length(inv_mod_loop_regs mu))%nat;apply nth_error_Some;rewrite At;discriminate).
   destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;
     cbn [inv_mod_loop_regs nth_error] in At;injection At as <-.
   + eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=0%nat)
      (xs:=vars5 0) (ys:=vars5 0);try reflexivity;apply Others;[reflexivity|discriminate].
   + eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=1%nat)
      (xs:=map XLc(inv_mod_words mu)) (ys:=map XLc(inv_mod_words mu));
      try reflexivity;apply Others;[reflexivity|discriminate].
   + eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=2%nat)
      (xs:=vars5 5) (ys:=vars5 5);try reflexivity;apply Others;[reflexivity|discriminate].
   + eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=3%nat)
      (xs:=vars5 10) (ys:=vars5 10);try reflexivity;apply Others;[reflexivity|discriminate].
   + eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=4%nat)
      (xs:=vars5 15) (ys:=vars5 15);try reflexivity;apply Others;[reflexivity|discriminate].
   + eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=5%nat)
      (xs:=vars5 20) (ys:=vars5 20);try reflexivity;apply Others;[reflexivity|discriminate].
   + apply inv_batch_matrix_region;assumption.
Qed.

Definition inv_divstep_batch := statement_sequence
 [inv_divstep_load false;inv_divstep_load true] inv_divstep_call.
Definition inv_divstep_returned st rho le := PTree.set _t'1
 (Vlong(Int64.repr(eta(fst(stepN 62 st))))) (inv_divstep_loaded_values (rho 15%nat) (rho 20%nat) le).
Lemma inv_divstep_returned_outside st rho le id : id<>_t'1 -> id<>_t'7 -> id<>_t'8 ->
 (inv_divstep_returned st rho le)!id=le!id.
Proof.
 intros T1 T7 T8;unfold inv_divstep_returned,inv_divstep_loaded_values;
 rewrite !PTree.gso by congruence;reflexivity.
Qed.

Theorem exec_inv_mod_batch mu len rho st beta e le m :
 (forall x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 m (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 -683<=eta st<683 -> (0<len<=5)%nat -> rep rho beta (inv_mod_seed_regs mu) m ->
 ematch beta (snd inv_start_alloc) e -> le!_eta=Some(Vlong(Int64.repr(eta st))) ->
 inv_state_matches len rho st -> exists mf,
 Clight2.exec_stmt secp_ge e le m inv_divstep_batch E0 (inv_divstep_returned st rho le) mf Out_normal /\
 rep (inv_batch_result_rho st rho) beta (inv_mod_loop_regs mu) mf /\
 inv_matrix_matches (inv_batch_result_rho st rho) st /\
 lframe(fun b _=>b<>blk beta 6) m mf /\ readonly_preserved m mf.
Proof.
 intros CountCall EtaRange Length Rep Env Eta State.
 pose proof(exec_inv_divstep_load_values e le m (blk beta 4) (blk beta 5) (rho 15%nat) (rho 20%nat)
  (proj1(Env _f)) (proj1(Env _g)) (inv_mod_batch_low_load mu rho beta m false Rep)
  (inv_mod_batch_low_load mu rho beta m true Rep)) as Loads.
 destruct(rep_free_region rho beta (inv_mod_seed_regs mu) m 6 32 Rep
  ltac:(change(6<7)%nat;lia) eq_refl) as(Base & Free).
 destruct(eval_div62_from_count_calls m CountCall st 62 (rho 15%nat) (rho 20%nat) (blk beta 6)
  ltac:(lia) EtaRange
  ltac:(rewrite(proj1 State);exact(inv_batch_low_modulo len rho false))
  ltac:(rewrite(proj2 State);exact(inv_batch_low_modulo len rho true)) Free)
  as(mf & Call & SignedLoads & ExactLoads & Returned & Owned & Frame & Readonly).
 assert(ExecCall:Clight2.exec_stmt secp_ge e (inv_divstep_loaded_values (rho 15%nat) (rho 20%nat) le)
  m inv_divstep_call E0 (inv_divstep_returned st rho le) mf Out_normal).
 { unfold inv_divstep_call,inv_divstep_returned;eapply exec_curve_call with
   (result:=Some _t'1) (v:=Vlong(Int64.repr(eta(fst(stepN 62 st)))))
   (vargs:=[Vlong(Int64.repr(eta st));Vlong(rho 15%nat);Vlong(rho 20%nat);Vptr(blk beta 6) Ptrofs.zero]).
   - unfold secp_pure;repeat(first[left;reflexivity|right]).
   - exact(proj1(Env _secp256k1_modinv64_divsteps_62_var)).
   - exact(inv_divstep_arguments_values beta e le m (Int64.repr(eta st)) (rho 15%nat) (rho 20%nat) Env Eta).
   - exact Call. }
 exists mf;split.
 - unfold inv_divstep_batch;eapply exec_statement_prefix_then_last;[exact Loads|exact ExecCall].
 - split;[eapply inv_mod_batch_restore;eassumption|];split;[apply inv_batch_result_matrix|];split;assumption.
Qed.
