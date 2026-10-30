(** Actual original 5x52-to-4x64 native field-storage packer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem
 C.jet_sx_rep C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition storage_pack_args:=[XP 0 0;XP 1 0].
Definition storage_pack_dest:=mkreg
 [mkcell 0 Mint64 None;mkcell 8 Mint64 None;mkcell 16 Mint64 None;mkcell 24 Mint64 None] true None.
Definition storage_pack_regs:=[storage_pack_dest;mkreg (u64_cells 0 (vars5 0)) false None].
Definition storage_pack_out:=
 [XLb Bor (XLv 0) (XLsh Hshl (XLv 1) 52);
  XLb Bor (XLsh Hshru (XLv 1) 12) (XLsh Hshl (XLv 2) 40);
  XLb Bor (XLsh Hshru (XLv 2) 24) (XLsh Hshl (XLv 3) 28);
  XLb Bor (XLsh Hshru (XLv 3) 36) (XLsh Hshl (XLv 4) 16)].
Definition storage_pack_words (w:nat->int64) i:=nth i
 [Int64.or (w 0%nat) (Int64.shl (w 1%nat) (Int64.repr 52));
  Int64.or (Int64.shru (w 1%nat) (Int64.repr 12)) (Int64.shl (w 2%nat) (Int64.repr 40));
  Int64.or (Int64.shru (w 2%nat) (Int64.repr 24)) (Int64.shl (w 3%nat) (Int64.repr 28));
  Int64.or (Int64.shru (w 3%nat) (Int64.repr 36)) (Int64.shl (w 4%nat) (Int64.repr 16))] Int64.zero.
Definition storage_pack_run:=xfun (genv_cenv secp_ge) [] (int_table secp_pure) 80
 f_secp256k1_fe_to_storage storage_pack_args storage_pack_regs [] 5.
Definition storage_pack_tree:=Eval vm_compute in storage_pack_run.
Definition storage_pack_state:=match storage_pack_tree with
 |Some (RDone st _)=>st|_=>mkst (PTree.empty sx) [] [] 0 end.
Definition storage_pack_out_regs:=
 [mkreg (u64_cells 0 storage_pack_out) true None;mkreg (u64_cells 0 (vars5 0)) false None].
Lemma storage_pack_run_eq:storage_pack_run=Some (RDone storage_pack_state ONormal).
Proof. reflexivity. Qed.
Lemma storage_pack_return:(stemps storage_pack_state)!1%positive=None.
Proof. reflexivity. Qed.
Lemma storage_pack_output_shape:sregs storage_pack_state=storage_pack_out_regs.
Proof. reflexivity. Qed.
Lemma storage_pack_output_den rho beta:
 map (den rho (lay beta)) storage_pack_out=
 map Vlong [storage_pack_words rho 0%nat;storage_pack_words rho 1%nat;
  storage_pack_words rho 2%nat;storage_pack_words rho 3%nat].
Proof. reflexivity. Qed.
Theorem eval_storage_pack_symbolic rho beta m:
 rep rho beta storage_pack_regs m ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_to_storage)
 [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
 rep rho beta storage_pack_out_regs mf /\
 lframe (fun b pos=>~foot beta (map rshape storage_pack_regs) b pos) m mf.
Proof.
 intro Initial.
 destruct (xfun_pure secp_ge secp_pure secp_pure_ok 80 f_secp256k1_fe_to_storage
  storage_pack_args storage_pack_regs 5 _ storage_pack_run_eq eq_refl rho beta m Initial)
 as (mf & result & Call & Final & Return & Shape & Frame).
 cbn [rsel fst] in Final,Return;rewrite storage_pack_return in Return;subst result.
 change (map (den rho (lay beta)) storage_pack_args) with
 [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0))] in Call.
 rewrite !Z.add_0_r in Call;rewrite storage_pack_output_shape in Final.
 exists mf;split;[exact Call|];split;assumption.
Qed.
