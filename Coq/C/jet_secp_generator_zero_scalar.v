(** Original read-only zero-scalar call for the generator's skipped point. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events Maps.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem C.jet_sx_pure.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric.
Import ListNotations Values.
Local Open Scope Z_scope.
Local Opaque secp_ge.
Set Default Timeout 10.

Lemma generator_scalar_zero_memory m mf args v :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_is_zero) args E0 mf v -> mf=m.
Proof.
 intro Call;inversion Call;subst.
 match goal with Entry:function_entry2 _ _ _ _ _ _ _ |- _ => inversion Entry;subst;clear Entry end.
 match goal with Alloc:alloc_variables _ _ _ (fn_vars f_secp256k1_scalar_is_zero) _ _ |- _ =>
  cbn [fn_vars f_secp256k1_scalar_is_zero] in Alloc;inversion Alloc;subst;clear Alloc end.
 match goal with Body:exec_stmt function_entry2 secp_ge _ _ _ (fn_body f_secp256k1_scalar_is_zero) _ _ _ _ |- _ =>
  cbn [fn_body f_secp256k1_scalar_is_zero] in Body end.
 repeat match goal with
 | H:exec_stmt function_entry2 secp_ge _ _ _ (Ssequence _ _) _ _ _ _ |- _ => inversion H;subst;clear H
 | H:exec_stmt function_entry2 secp_ge _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion H;subst;clear H
 | H:exec_stmt function_entry2 secp_ge _ _ _ (Sreturn _) _ _ _ _ |- _ => inversion H;subst;clear H
 end;try contradiction.
 all:match goal with Free:Mem.free_list _ (blocks_of_env _ empty_env)=_ |- _ =>
  cbn [blocks_of_env empty_env] in Free;inversion Free;reflexivity end.
Qed.

Definition generator_zero_regs :=
 [mkreg (u64_cells 0 [XLv 0;XLv 1;XLv 2;XLv 3]) false None].
Definition generator_zero_run := xfun (genv_cenv secp_ge) [] [] 80 f_secp256k1_scalar_is_zero
 [XP 0 0] generator_zero_regs [] 4.
Definition generator_zero_state := match generator_zero_run with Some (RDone st _) => st
 | _=>mkst (PTree.empty sx) [] [] 0 end.
Lemma generator_zero_run_eq : generator_zero_run=Some (RDone generator_zero_state ONormal).
Proof. vm_compute;reflexivity. Qed.
Lemma generator_zero_log : slog generator_zero_state=[].
Proof. reflexivity. Qed.
Definition generator_zero_return := match (stemps generator_zero_state)!1%positive with
 | Some x=>x | None=>XIc Int.zero end.
Lemma generator_zero_result : (stemps generator_zero_state)!1%positive=Some generator_zero_return.
Proof. reflexivity. Qed.
Lemma generator_zero_value layout : den (fun _=>Int64.zero) layout generator_zero_return=Vint Int.one.
Proof. reflexivity. Qed.

Lemma generator_zero_rep m b ofs :
 scalar_at m b ofs [Int64.zero;Int64.zero;Int64.zero;Int64.zero] ->
 rep (fun _=>Int64.zero) [(b,ofs)] generator_zero_regs m.
Proof.
 intros (Length & Base & Align & Hi & Readable & Loads).
 apply (rep_add _ [] [] m b ofs);[apply rep_nil|cbn;tauto|].
 apply region_u64;cbn [blk bas lay nth fst snd length].
 - exact Base.
 - exact Align.
 - exact Hi.
 - eapply Mem.perm_valid_block;apply (Readable ofs);lia.
 - exact Readable.
 - intros i x Nth;destruct i as [|[|[|[|i]]]];cbn [nth_error] in Nth;
    try (destruct i;discriminate Nth);injection Nth as <-.
   all:split;[|reflexivity].
   + exact (Loads 0%nat Int64.zero eq_refl).
   + exact (Loads 1%nat Int64.zero eq_refl).
   + exact (Loads 2%nat Int64.zero eq_refl).
   + exact (Loads 3%nat Int64.zero eq_refl).
Qed.

Theorem eval_generator_scalar_zero m b ofs :
 scalar_at m b ofs [Int64.zero;Int64.zero;Int64.zero;Int64.zero] ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_is_zero)
  [Vptr b (Ptrofs.repr ofs)] E0 m (Vint Int.one).
Proof.
 intro Storage.
 destruct (xfun_pure secp_ge [] ltac:(intros;contradiction) 80 f_secp256k1_scalar_is_zero
  [XP 0 0] generator_zero_regs 4 (RDone generator_zero_state ONormal) generator_zero_run_eq
  ltac:(cbn [leaves_log_nil];rewrite generator_zero_log;reflexivity)
  (fun _=>Int64.zero) [(b,ofs)] m (generator_zero_rep m b ofs Storage))
  as (mf & result & Call & Final & Return & Shape & Frame).
 cbn [rsel fst] in Return;rewrite generator_zero_result,generator_zero_value in Return;subst result.
 change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_is_zero)
  [Vptr b (Ptrofs.repr (ofs+0))] E0 mf (Vint Int.one)) in Call.
 rewrite Z.add_0_r in Call.
 pose proof (generator_scalar_zero_memory m mf _ _ Call);subst mf;exact Call.
Qed.
