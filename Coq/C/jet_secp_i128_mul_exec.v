(** Execute the actual signed64-by-signed64 product into an uninitialized
    16-byte destination. Numeric interpretation is a separate bridge. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem C.jet_sx_pure.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_umul128_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition smul128_functions := [(_secp256k1_mul128,f_secp256k1_mul128)].
Lemma smul128_functions_ok id fd : In (id,fd) smul128_functions ->
 exists b, Globalenvs.Genv.find_symbol secp_ge id=Some b /\
 Globalenvs.Genv.find_funct_ptr secp_ge b=Some (Internal fd).
Proof.
 intros [E|[]];injection E as <- <-;apply secp_pure_ok.
 unfold secp_pure;do 2 right;left;reflexivity.
Qed.
Definition smul128_regs := [mkreg [mkcell 0 Mint64 None;mkcell 8 Mint64 None] true (Some 16)].
Definition smul128_run := xfun (genv_cenv secp_ge) [] (int_table smul128_functions) 200
 f_secp256k1_i128_mul [XP 0 0;XLv 0;XLv 1] smul128_regs [] 2.
Definition smul128_tree := Eval vm_compute in smul128_run.
Definition smul128_state := match smul128_tree with
 | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.

Definition smul128_ll := umul128_ll.
Definition smul128_lh := XLb Bmul (mul_low32 (XLv 0)) (XLsh Hshr (XLv 1) 32).
Definition smul128_hl := XLb Bmul (XLsh Hshr (XLv 0) 32) (mul_low32 (XLv 1)).
Definition smul128_hh := XLb Bmul (XLsh Hshr (XLv 0) 32) (XLsh Hshr (XLv 1) 32).
Definition smul128_mid := XLb Badd
 (XLb Badd (XLsh Hshru smul128_ll 32) (mul_low32 smul128_lh)) (mul_low32 smul128_hl).
Definition smul128_lo := XLb Badd (XLsh Hshl smul128_mid 32) (mul_low32 smul128_ll).
Definition smul128_hi := XLb Badd
 (XLb Badd (XLb Badd smul128_hh (XLsh Hshr smul128_lh 32))
  (XLsh Hshr smul128_hl 32)) (XLsh Hshru smul128_mid 32).
Definition smul128_out := [mkreg (u64_cells 0 [smul128_lo;smul128_hi]) true (Some 16)].

Lemma smul128_run_eq : smul128_run=Some (RDone smul128_state ONormal).
Proof. reflexivity. Qed.
Lemma smul128_return : (stemps smul128_state)!1%positive=None.
Proof. reflexivity. Qed.
Lemma smul128_output : sregs smul128_state=smul128_out.
Proof. reflexivity. Qed.
Lemma smul128_log_nil : slog smul128_state=[].
Proof. reflexivity. Qed.

Theorem eval_i128_mul_symbolic rho layout m : rep rho layout smul128_regs m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_i128_mul)
  [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));Vlong (rho 0%nat);Vlong (rho 1%nat)] E0 mf Vundef /\
 rep rho layout smul128_out mf /\
 lframe (fun b ofs=>~foot layout (map rshape smul128_regs) b ofs) m mf.
Proof.
 intro Rep.
 destruct (xfun_pure secp_ge smul128_functions smul128_functions_ok 200 f_secp256k1_i128_mul
  [XP 0 0;XLv 0;XLv 1] smul128_regs 2 _ smul128_run_eq eq_refl rho layout m Rep)
  as (mf & value & Call & Out & Ret & Shape & Frame).
 cbn [rsel fst] in Out,Ret;rewrite smul128_return in Ret;subst value.
 rewrite smul128_output in Out.
 change (map (den rho (lay layout)) [XP 0 0;XLv 0;XLv 1]) with
  [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+0));Vlong (rho 0%nat);Vlong (rho 1%nat)] in Call.
 rewrite Z.add_0_r in Call.
 exists mf;exact (conj Call (conj Out Frame)).
Qed.
