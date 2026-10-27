(** Original scalar_mul call shape with r distinct from a and b. The full
    product feeds fresh-destination reduction, with no fabricated r value. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem C.jet_sx_u64_transport
 C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions
 C.jet_secp_scalar_add_separate_run C.jet_secp_scalar_add_separate
 C.jet_secp_reduce512_fresh_runs C.jet_secp_scalar_reduce512_run C.jet_secp_scalar_mul512_borrowed
 C.jet_secp_scalar_mul512_run C.jet_secp_scalar_mul512_machine C.jet_secp_scalar_mul512_symbolic
 C.jet_secp_product_reduce_bridge C.jet_secp_scalar_mul_caller_body C.jet_secp_scalar_mul_caller_alloc
 C.jet_secp_scalar_mul_caller_function C.jet_secp_closed_helpers C.jet_clight_internal_frame.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma fresh_product_reduce_rep rho beta br m :
 rep rho beta scalar_mul512_borrowed_output_regs m ->
 Mem.range_perm m br 0 32 Cur Freeable -> br<>blk beta 0 ->
 rep (product_reduce_rho rho) [(br,0);(blk beta 0,0)] reduce512_fresh_initial_regs m.
Proof.
 intros Product Free Separate.
 destruct (rep_free_region _ _ _ _ 0 64 Product ltac:(cbn;lia) eq_refl) as [Base ProductFree].
 assert (Dest:rep (product_reduce_rho rho) [(br,0)] [mkreg scalar_add_separate_cells true (Some 32)] m).
 { apply (rep_snoc (product_reduce_rho rho) [] [] m br scalar_add_separate_cells 32);
   [apply rep_nil|cbn;tauto| |exact Free|exact (proj1 scalar_add_separate_cells_ok)|
    exact (proj2 scalar_add_separate_cells_ok)|change (32<=18446744073709551615);lia].
   eapply Mem.perm_valid_block;apply (Free 0);lia. }
 apply (rep_add (product_reduce_rho rho) [(br,0)] [mkreg scalar_add_separate_cells true (Some 32)] m (blk beta 0) 0);
 [exact Dest|cbn;intros [Eq|[]];congruence|].
 eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=0%nat)
  (xs:=scalar_mul512_limbs) (ys:=[XLv 0;XLv 1;XLv 2;XLv 3;XLv 4;XLv 5;XLv 6;XLv 7])
  (w:=true) (owned:=Some 64).
 - change ((blk beta 0,0)=lay beta 0).
   unfold blk,bas in Base|-*;destruct (lay beta 0) as [b z];cbn in *;subst z;reflexivity.
 - symmetry;apply scalar_mul512_limbs_length.
 - rewrite product_reduce_input_map,scalar_mul512_outputs_machine;reflexivity.
 - reflexivity.
 - exact (rep_region _ _ _ _ 0 _ Product eq_refl).
Qed.

Definition scalar_mul_separate_temps beta br :=
 PTree.set _b (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1)))
 (PTree.set _a (Vptr (blk beta 0) (Ptrofs.repr (bas beta 0)))
 (PTree.set _r (Vptr br Ptrofs.zero) (PTree.empty val))).

Local Opaque secp_ge.
Lemma scalar_mul_separate_entry beta br m ma bl : Mem.alloc m 0 64=(ma,bl) ->
 function_entry2 secp_ge f_secp256k1_scalar_mul
 [Vptr br Ptrofs.zero;Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
  Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))]
 m (scalar_mul_caller_env (scalar_mul_stack_layout beta bl)) (scalar_mul_separate_temps beta br) ma.
Proof.
 intro Alloc;destruct (fn_okb_true _ scalar_mul_caller_ok) as (Vars & Params & Disjoint).
 constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
 eapply alloc_variables_cons;[exact Alloc|constructor].
Qed.

Lemma exec_scalar_mul_separate_calls beta br bl m mp mf :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul_512)
 [Vptr bl Ptrofs.zero;Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
  Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mp Vundef ->
 Clight2.eval_funcall secp_ge mp (Internal f_secp256k1_scalar_reduce_512)
 [Vptr br Ptrofs.zero;Vptr bl Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (scalar_mul_caller_env (scalar_mul_stack_layout beta bl))
 (scalar_mul_separate_temps beta br) m (fn_body f_secp256k1_scalar_mul)
 E0 (scalar_mul_separate_temps beta br) mf Out_normal.
Proof.
 intros Product Reduce;rewrite scalar_mul_caller_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=scalar_mul_separate_temps beta br) (m1:=mp).
 - apply (exec_scalar_mul_product_call (scalar_mul_stack_layout beta bl));try reflexivity;exact Product.
 - apply (exec_scalar_mul_reduction_call [(bl,0);(br,0)]);try reflexivity;exact Reduce.
Qed.

Lemma scalar_mul_separate_closed : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_scalar_mul)=true.
Proof. timeout 10 (vm_compute;reflexivity). Qed.
