(** Original generator byte-array loader. Its source and result are the
    actual 64-byte and 88-byte caller allocations used by hash_to_curve. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem
  C.jet_sx_rep C.jet_sx_rename C.jet_secp_fns C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_affine_storage
  C.jet_secp_local_regions C.jet_secp_multiply_normalize_bridge.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition generator_load_source := mkreg (C.jet_secp_fe_b32.byte_cells 0 64 0) true (Some 64).
Definition generator_load_regs := [affine_storage_undef;generator_load_source].
Definition generator_load_args := [XP 0 0;XP 1 0].
Definition generator_load_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 800
  f_secp256k1_generator_load generator_load_args generator_load_regs [] 64.
Definition generator_load_tree := Eval vm_compute in generator_load_run.
Definition generator_load_state := match generator_load_tree with
  | Some (RDone st _) => st | _=>mkst (PTree.empty sx) [] [] 0 end.
Definition generator_field_exprs := map (fun c=>match cval c with Some x=>x | None=>XL Int64.zero end) (cells0 sb_leaf).
Definition generator_load_cells := u64_cells 0 generator_field_exprs ++
  u64_cells 40 (map (sx_rename (fun n=>(n+32)%nat)) generator_field_exprs) ++
  [mkcell 80 Mint32 (Some (XIc Int.zero))].
Definition generator_load_out_regs := [mkreg generator_load_cells true (Some 88);generator_load_source].
Lemma generator_load_run_eq : generator_load_run=Some (RDone generator_load_state ONormal).
Proof. reflexivity. Qed.
Lemma generator_load_return : (stemps generator_load_state)!1%positive=None.
Proof. reflexivity. Qed.
Lemma generator_load_shape : sregs generator_load_state=generator_load_out_regs.
Proof. reflexivity. Qed.
Lemma generator_field_length : length generator_field_exprs=5%nat.
Proof. reflexivity. Qed.

Theorem eval_generator_load_symbolic rho beta m : rep rho beta generator_load_regs m -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_generator_load)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
  rep rho beta generator_load_out_regs mf /\
  lframe (fun b pos=>~foot beta (map rshape generator_load_regs) b pos) m mf.
Proof.
  intro Rep;destruct (xfun_pure secp_ge secp_pure secp_pure_ok 800 f_secp256k1_generator_load
    generator_load_args generator_load_regs 64 _ generator_load_run_eq eq_refl rho beta m Rep)
    as (mf & result & Run & Final & Return & Shape & Frame).
  cbn [rsel fst] in Final,Return;rewrite generator_load_return in Return;subst result.
  change (map (den rho (lay beta)) generator_load_args) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0))] in Run.
  rewrite !Z.add_0_r in Run;rewrite generator_load_shape in Final.
  exists mf;split;[exact Run|];split;[exact Final|exact Frame].
Qed.
