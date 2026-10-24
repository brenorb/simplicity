(** The original transition helper including entry, allocation and freeing. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_start.
Require Import C.jet_secp_modinv_fg_body C.jet_secp_modinv_fg_finish C.jet_secp_modinv_fg_finish_numeric.
Require Import C.jet_secp_modinv_fg_loop C.jet_secp_modinv_fg_loop_numeric C.jet_secp_modinv_fg_iteration_numeric.
Require Import C.jet_secp_modinv_fg_iteration_arith C.jet_secp_u128_shift64_rep.
Require Import C.jet_secp_multiply_call_lifecycle.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fg_call_args := [XL2I (XLv 14);XP 0 0;XP 1 0;XP 2 0].
Definition fg_call_pre len rho : Prop :=
 Int64.loword (rho 14%nat)=Int.repr (Z.of_nat len) /\ fg_input_bounds rho.
Definition fg_call_out len := firstn 3 (fg_finish_regs len).
Lemma fg_call_alloc : xalloc (std_cells (genv_cenv secp_ge)) (genv_cenv secp_ge)
 (fn_vars f_secp256k1_modinv64_update_fg_62_var) (length fg_regs)=Some (fst fg_alloc,snd fg_alloc).
Proof. reflexivity. Qed.
Lemma fg_call_bind : xbind (fn_params f_secp256k1_modinv64_update_fg_62_var) fg_call_args (PTree.empty sx)=Some fg_temps.
Proof. reflexivity. Qed.
Lemma fg_call_shapes len : (0<len<=5)%nat ->
 map rshape (fg_finish_regs len)=map rshape (fg_regs++fst fg_alloc).
Proof. destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;vm_compute;reflexivity. Qed.
Lemma fg_body_value_exact len rho high : (0<len<=5)%nat -> fg_input_bounds rho ->
 fg_body_value len rho high=fg_matrix_value rho high len/2^62.
Proof.
 intros Len Bounds.
 assert (Carry : Int64.min_signed<=fg_pair_value (fg_iter_input (fg_body_rho len rho) high)<=Int64.max_signed).
 { apply fg_loop_carry_fits64;[lia|lia|apply fg_start_state_bounds;exact Bounds|].
   apply fg_start_carry_fits64;exact Bounds. }
 unfold fg_body_value;rewrite fg_finish_value by assumption.
 unfold fg_body_rho;rewrite (proj1 (fg_loop_numeric (len-1) (fg_start_rho rho) high 1 ltac:(lia)
  ltac:(lia) (fg_start_state_bounds rho Bounds))).
 apply fg_matrix_quotient;assumption.
Qed.

Lemma fg_call_array_load len (high : bool) d : (0<len<=5)%nat ->
 xload (fg_call_out len) (if high then 1 else 0) d tulong=
 xload (fg_finish_regs len) (if high then 1 else 0) d tulong.
Proof. destruct high;destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;reflexivity. Qed.
Lemma fg_call_storage rho beta len m : (0<len<=5)%nat -> rep rho beta (fg_call_out len) m ->
 forall (high : bool) j,(j<len)%nat ->
 Mem.load Mint64 m (blk beta (if high then 1 else 0))
  (bas beta (if high then 1 else 0)+8*Z.of_nat j)=Some (Vlong (fg_finished_word rho len high j)).
Proof.
 intros Len Rep high j J.
 pose proof (eq_trans (fg_call_array_load len high (8*Z.of_nat j) Len)
  (fg_finish_load len high j Len ltac:(lia))) as Load.
 pose proof (xload_u64_defined_sound rho beta _ m _ _ _ Rep Load) as Word.
 unfold fg_finished_word;destruct (Nat.eqb j (len-1));destruct high;exact Word.
Qed.

Theorem eval_fg_transition len rho beta m : (0<len<=5)%nat ->
 Int64.loword (rho 14%nat)=Int.repr (Z.of_nat len) -> fg_input_bounds rho -> rep rho beta fg_regs m ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_update_fg_62_var)
  [Vint (Int.repr (Z.of_nat len));Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
 (forall (high : bool) j,(j<len)%nat -> Mem.load Mint64 mf (blk beta (if high then 1 else 0))
  (bas beta (if high then 1 else 0)+8*Z.of_nat j)=Some (Vlong (fg_body_word len rho high j))) /\
 (forall high,fg_body_value len rho high=fg_matrix_value rho high len/2^62) /\
 rep (fg_body_rho len rho) beta (fg_call_out len) mf /\
 lframe (fun b ofs=>~foot beta (map rshape fg_regs) b ofs) m mf.
Proof.
 intros Bound Len Bounds Rep.
 assert (Body : forall r beta' e le mi,fg_call_pre len r ->
  rep r beta' (fg_regs++fst fg_alloc) mi -> tmatch r beta' fg_temps le -> ematch beta' (snd fg_alloc) e ->
  exists lef mf,Clight2.exec_stmt secp_ge e le mi (fn_body f_secp256k1_modinv64_update_fg_62_var) E0 lef mf Out_normal /\
  rep (fg_body_rho len r) beta' (fg_finish_regs len) mf /\
  lframe (fun b ofs=>~foot beta' (map rshape (fg_regs++fst fg_alloc)) b ofs) mi mf).
 { intros r beta' e le mi (L & B) R T E.
   destruct (exec_fg_body len r beta' e le mi Bound L B R T E)
    as (lef & mf & Exec & Storage & Value & Out & Match & Frame).
   exists lef,mf;split;[exact Exec|];split;assumption. }
 destruct (owned_void_call_state secp_ge f_secp256k1_modinv64_update_fg_62_var fg_call_args
  fg_regs (fst fg_alloc) (snd fg_alloc) fg_temps (fg_call_pre len) (fg_body_rho len)
  (fun _=>fg_finish_regs len) eq_refl eq_refl eq_refl fg_call_alloc fg_call_bind
  (fun _=>fg_call_shapes len Bound) Body rho beta m (conj Len Bounds) Rep)
  as (mf & Call & Out & Frame).
 change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_update_fg_62_var)
  [Vint (Int64.loword (rho 14%nat));Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0));Vptr (blk beta 2) (Ptrofs.repr (bas beta 2+0))] E0 mf Vundef) in Call.
 rewrite Len,!Z.add_0_r in Call.
 exists mf;split;[exact Call|];split;[exact (fg_call_storage _ beta len mf Bound Out)|];
 split;[intro high;apply fg_body_value_exact;assumption|];split;assumption.
Qed.
