(** Whole original conditional-bit-add function, with allocation and freeing
    of its uint128 local. Its four output words are the actual stored words. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep
 C.jet_secp_linkage C.jets_secp C.jet_secp_frame C.jet_secp_scalar_cadd_control C.jet_secp_scalar_cadd_run
 C.jet_secp_scalar_cadd_body C.jet_secp_multiply_call_lifecycle C.jet_secp_u128_shift64_rep
 C.jet_secp_local_regions C.jet_secp_scalar_add_initial C.jet_secp_scalar_get_b32_storage
 C.jet_secp_slice_permissions C.jet_secp_closed_helpers C.jet_clight_internal_frame
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge xstmt cadd_table cadd_allocated cadd_checkpoint cadd_final_state.

Definition cadd_output_sx := Eval vm_compute in fun flag=>
 map cell_sx (rcells (hd (mkreg [] false None) (sregs (cadd_final_state flag)))).
Definition cadd_output_regs flag := [mkreg (u64_cells 0 (cadd_output_sx flag)) true (Some 32)].
Definition cadd_output_words rho flag := map (lv rho) (cadd_output_sx flag).
Lemma cadd_output_region flag : firstn 1 (sregs (cadd_final_state flag))=cadd_output_regs flag.
Proof. destruct flag;timeout 10 (vm_compute;reflexivity). Qed.
Lemma cadd_output_length flag : length (cadd_output_sx flag)=4%nat.
Proof. destruct flag;reflexivity. Qed.
Lemma cadd_output_load flag i x : nth_error (cadd_output_sx flag) i=Some x ->
 xload (cadd_output_regs flag) 0 (8*Z.of_nat i) tulong=Some x /\ isk KL x=true.
Proof.
 intro Nth;assert (Index:(i<4)%nat) by (rewrite <-(cadd_output_length flag);eapply nth_error_Some;congruence).
 destruct i as [|[|[|[|i]]]];try lia;destruct flag;injection Nth as <-;
 timeout 10 (vm_compute;split;reflexivity).
Qed.

Theorem eval_cadd_from_regions flag rho beta m : rep rho beta cadd_initial_regs m ->
 exists mf, Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_cadd_bit)
  (map (den rho (lay beta)) (cadd_args flag)) E0 mf Vundef /\
 rep rho beta (cadd_output_regs flag) mf /\
 lframe (fun b ofs=>~foot beta (map rshape cadd_initial_regs) b ofs) m mf.
Proof.
 intro Rep.
 destruct (owned_void_call secp_ge f_secp256k1_scalar_cadd_bit (cadd_args flag) cadd_initial_regs
  (fst cadd_allocated) (snd cadd_allocated) (cadd_initial_temps flag)
  (fun _=>sregs (cadd_final_state flag))) with (rho:=rho) (beta:=beta) (m:=m)
  as (mf & Run & Rep' & Frame).
 - reflexivity.
 - reflexivity.
 - destruct flag;reflexivity.
 - exact cadd_allocation.
 - exact (cadd_binding flag).
 - intro r;rewrite <-cadd_checkpoint_last;apply cadd_checkpoint_shape;lia.
 - intros;exact (exec_cadd_body flag _ _ _ _ _ H H0 H1).
 - exact Rep.
 - exists mf;split;[exact Run|];split;[rewrite <-cadd_output_region;exact Rep'|exact Frame].
Qed.

Lemma cadd_result_storage rho beta flag m : rep rho beta (cadd_output_regs flag) m ->
 bas beta 0=0 /\ Mem.range_perm m (blk beta 0) 0 32 Cur Freeable /\
 scalar_at m (blk beta 0) 0 (cadd_output_words rho flag).
Proof.
 intro Rep;destruct (rep_free_region rho beta (cadd_output_regs flag) m 0 32 Rep
  ltac:(cbn [cadd_output_regs length];lia) eq_refl) as (Base & Free).
 split;[exact Base|];split;[exact Free|].
 unfold scalar_at,cadd_output_words;split;[rewrite map_length;apply cadd_output_length|].
 split;[lia|];split;[exists 0;lia|];split;
 [change (32<=18446744073709551615);lia|];split.
 - intros pos Range;eapply Mem.perm_implies;[apply Free;lia|constructor].
 - intros i word Nth;rewrite nth_error_map in Nth.
   destruct (nth_error (cadd_output_sx flag) i) as [x|] eqn:X;[|discriminate].
   injection Nth as <-;destruct (cadd_output_load flag i x X) as (Load & Kind).
   pose proof (xload_u64_defined_sound rho beta (cadd_output_regs flag) m 0 (8*Z.of_nat i) x Rep Load) as Actual.
   rewrite Base,Z.add_0_l in Actual;rewrite (den_KL rho (lay beta) x Kind),lv_den in Actual;exact Actual.
Qed.

Lemma cadd_closed : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_scalar_cadd_bit)=true.
Proof. timeout 10 (vm_compute;reflexivity). Qed.

Theorem eval_scalar_cadd_owned (flag:bool) rho m b :
 scalar_at m b 0 (scalar_add_values rho 0) -> Mem.range_perm m b 0 32 Cur Freeable ->
 exists mf, Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_cadd_bit)
  [Vptr b Ptrofs.zero;Vint Int.zero;Vint (if flag then Int.one else Int.zero)] E0 mf Vundef /\
 scalar_at mf b 0 (cadd_output_words rho flag) /\ Mem.range_perm mf b 0 32 Cur Freeable /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (fun b' _=>b'<>b) m mf.
Proof.
 intros Stored Free.
 assert (Rep:rep rho [(b,0)] cadd_initial_regs m).
 { apply (rep_add rho [] [] m b 0);[apply rep_nil|cbn;tauto|].
   apply scalar_add_region_from_values;[reflexivity|exact Stored|exact Free]. }
 destruct (eval_cadd_from_regions flag rho [(b,0)] m Rep) as (mf & Run & Rep' & Frame).
 change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_cadd_bit)
  [Vptr b Ptrofs.zero;Vint Int.zero;Vint (if flag then Int.one else Int.zero)] E0 mf Vundef) in Run.
 destruct (cadd_result_storage rho [(b,0)] flag mf Rep') as (_ & Free' & Stored').
 exists mf;split;[exact Run|];split;[exact Stored'|];split;[exact Free'|];split.
 - eapply secp_internal_keeps_permissions;[exact cadd_closed|reflexivity|exact Run].
 - split.
   + eapply (secp_closed_function_preserved f_secp256k1_scalar_cadd_bit);
     [exact cadd_closed|reflexivity|exact Run].
   + eapply lframe_implies;[exact Frame|].
     intros b' ofs Different Valid (r & sh & d & ch & Nth & Cell & Same & Rest).
     destruct r as [|r];[cbn [blk lay nth fst] in Same;congruence|].
     destruct r;discriminate.
Qed.
