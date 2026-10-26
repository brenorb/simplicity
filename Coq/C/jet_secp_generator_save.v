(** Original generator saver, retaining its infinity inspection and both
    normalize/get_b32 calls. The infinity flag is an arbitrary machine int:
    the frozen verification loop inspects it but does not reject it. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure
  C.jet_sx_mem C.jet_sx_rep C.jet_sx_rename C.jet_secp_fns C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_b32_exec.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition generator_save_buffer := mkreg
  (map (fun c=>mkcell (cofs c) (cchunk c) None) (jet_secp_fe_b32.byte_cells 0 64 0)) true (Some 64).
Definition generator_save_point flag := mkreg
  (u64_cells 0 (map XLv (seq 0 5)) ++ u64_cells 40 (map XLv (seq 5 5)) ++
   [mkcell 80 Mint32 (Some (XI flag))]) true (Some 88).
Definition generator_save_regs flag := [generator_save_point flag;generator_save_buffer].
Definition generator_save_args := [XP 1 0;XP 0 0].
Definition generator_save_run flag := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 800
  f_secp256k1_generator_save generator_save_args (generator_save_regs flag) [] 10.
Definition generator_save_tree := Eval vm_compute in fun flag=>generator_save_run flag.
Definition generator_save_result flag := match generator_save_tree flag with
  | Some rr=>rr | None=>RDone (mkst (PTree.empty sx) [] [] 0) ONormal end.
Lemma generator_save_run_eq flag : generator_save_run flag=Some (generator_save_result flag).
Proof. reflexivity. Qed.
Lemma generator_save_return flag rho beta :
  (stemps (fst (rsel rho (lay beta) (generator_save_result flag))))!1%positive=None.
Proof.
  cbn [generator_save_result generator_save_tree rsel fst stemps].
  repeat match goal with |- context [if ?test then _ else _]=>destruct test end;reflexivity.
Qed.

Theorem eval_generator_save_symbolic flag rho beta m : rep rho beta (generator_save_regs flag) m ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_generator_save)
    [Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));Vptr (blk beta 0) (Ptrofs.repr (bas beta 0))] E0 mf Vundef /\
  rep rho beta (sregs (fst (rsel rho (lay beta) (generator_save_result flag)))) mf /\
  lframe (fun b pos=>~foot beta (map rshape (generator_save_regs flag)) b pos) m mf.
Proof.
  intro Rep;destruct (xfun_pure secp_ge secp_pure secp_pure_ok 800 f_secp256k1_generator_save
    generator_save_args (generator_save_regs flag) 10 _ (generator_save_run_eq flag) eq_refl rho beta m Rep)
    as (mf & result & Run & Final & Return & Shape & Frame).
  rewrite generator_save_return in Return;subst result.
  change (map (den rho (lay beta)) generator_save_args) with
    [Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0));Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0))] in Run.
  rewrite !Z.add_0_r in Run.
  exists mf;split;[exact Run|];split;[exact Final|exact Frame].
Qed.
