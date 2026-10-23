(** Actual signed multiply-accumulate, including the discarded verification
    expressions and private local allocation in the frozen C body. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_sx_pure C.jet_secp_linkage C.jets_secp C.jet_secp_i128_mul_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition smul_accum_regs : list region :=
 [mkreg (u64_cells 0 [XLv 2;XLv 3]) true (Some 16)].
Definition smul_accum_run := xfun (genv_cenv secp_ge) [] (int_table smul128_functions) 300
 f_secp256k1_i128_accum_mul [XP 0 0;XLv 0;XLv 1] smul_accum_regs [] 4.
Definition smul_accum_tree := Eval vm_compute in match smul_accum_run with
 | Some tree=>tree | None=>RDone (mkst (PTree.empty sx) [] [] 0) ONormal end.
Definition smul_accum_lo := XLb Badd (XLv 2) smul128_lo.
Definition smul_accum_hi := XLb Badd (XLv 3)
 (XLb Badd smul128_hi (XI2L Signed (XLcmp Clt Unsigned smul_accum_lo smul128_lo))).
Definition smul_accum_out := [mkreg (u64_cells 0 [smul_accum_lo;smul_accum_hi]) true (Some 16)].

Lemma smul_accum_run_eq : smul_accum_run=Some smul_accum_tree.
Proof. reflexivity. Qed.
Lemma smul_accum_logs_nil : leaves_log_nil smul_accum_tree=true.
Proof. reflexivity. Qed.
Lemma smul_accum_outputs rho layout :
 sregs (fst (rsel rho layout smul_accum_tree))=smul_accum_out.
Proof.
 cbn [smul_accum_tree rsel].
 repeat match goal with |- context [if ?c then _ else _]=>destruct c end;reflexivity.
Qed.
Lemma smul_accum_return rho layout :
 (stemps (fst (rsel rho layout smul_accum_tree)))!1%positive=None.
Proof.
 cbn [smul_accum_tree rsel].
 repeat match goal with |- context [if ?c then _ else _]=>destruct c end;reflexivity.
Qed.

Theorem eval_i128_accum_mul_symbolic rho layout m : rep rho layout smul_accum_regs m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_i128_accum_mul)
  [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));Vlong (rho 0%nat);Vlong (rho 1%nat)] E0 mf Vundef /\
 rep rho layout smul_accum_out mf /\
 lframe (fun b ofs=>~foot layout (map rshape smul_accum_regs) b ofs) m mf.
Proof.
 intro Rep.
 destruct (xfun_pure secp_ge smul128_functions smul128_functions_ok 300 f_secp256k1_i128_accum_mul
  [XP 0 0;XLv 0;XLv 1] smul_accum_regs 4 _ smul_accum_run_eq smul_accum_logs_nil rho layout m Rep)
  as (mf & value & Call & Out & Ret & Shape & Frame).
 rewrite smul_accum_return in Ret;subst value;rewrite smul_accum_outputs in Out.
 change (map (den rho (lay layout)) [XP 0 0;XLv 0;XLv 1]) with
  [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+0));Vlong (rho 0%nat);Vlong (rho 1%nat)] in Call.
 rewrite Z.add_0_r in Call;exists mf;exact (conj Call (conj Out Frame)).
Qed.
