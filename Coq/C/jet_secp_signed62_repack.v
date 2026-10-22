(** Both original field/signed62 conversion functions, sharing one verified
    execution and storage interface. Numeric representation bridges follow. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep
 C.jet_sx_revalue_cells C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_local_regions
 C.jet_secp_multiply_normalize_bridge C.jet_secp_field_negate_separate C.jet_secp_curve_frame.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition fe_repack_function (to62 : bool) :=
 if to62 then f_secp256k1_fe_to_signed62 else f_secp256k1_fe_from_signed62.
Definition fe_repack_args := [XP 0 0;XP 1 0].
Definition fe_repack_regs := negate_sep_regs.
Definition fe_repack_out (to62 : bool) : list sx :=
 if to62 then
 [XLb Band (XLb Bor (XLv 0) (XLsh Hshl (XLv 1) 52)) (XLsh Hshru (XLc (Int64.repr (-1))) 2);
  XLb Band (XLb Bor (XLsh Hshru (XLv 1) 10) (XLsh Hshl (XLv 2) 42)) (XLsh Hshru (XLc (Int64.repr (-1))) 2);
  XLb Band (XLb Bor (XLsh Hshru (XLv 2) 20) (XLsh Hshl (XLv 3) 32)) (XLsh Hshru (XLc (Int64.repr (-1))) 2);
  XLb Band (XLb Bor (XLsh Hshru (XLv 3) 30) (XLsh Hshl (XLv 4) 22)) (XLsh Hshru (XLc (Int64.repr (-1))) 2);
  XLsh Hshru (XLv 4) 40]
 else
 [XLb Band (XLv 0) (XLsh Hshru (XLc (Int64.repr (-1))) 12);
  XLb Band (XLb Bor (XLsh Hshru (XLv 0) 52) (XLsh Hshl (XLv 1) 10)) (XLsh Hshru (XLc (Int64.repr (-1))) 12);
  XLb Band (XLb Bor (XLsh Hshru (XLv 1) 42) (XLsh Hshl (XLv 2) 20)) (XLsh Hshru (XLc (Int64.repr (-1))) 12);
  XLb Band (XLb Bor (XLsh Hshru (XLv 2) 32) (XLsh Hshl (XLv 3) 30)) (XLsh Hshru (XLc (Int64.repr (-1))) 12);
  XLb Bor (XLsh Hshru (XLv 3) 22) (XLsh Hshl (XLv 4) 40)].

Definition fe_repack_words (to62 : bool) (w : nat -> int64) i :=
 nth i (if to62 then
 [Int64.and (Int64.or (w 0%nat) (Int64.shl (w 1%nat) (Int64.repr 52))) (Int64.repr (2^62-1));
  Int64.and (Int64.or (Int64.shru (w 1%nat) (Int64.repr 10)) (Int64.shl (w 2%nat) (Int64.repr 42))) (Int64.repr (2^62-1));
  Int64.and (Int64.or (Int64.shru (w 2%nat) (Int64.repr 20)) (Int64.shl (w 3%nat) (Int64.repr 32))) (Int64.repr (2^62-1));
  Int64.and (Int64.or (Int64.shru (w 3%nat) (Int64.repr 30)) (Int64.shl (w 4%nat) (Int64.repr 22))) (Int64.repr (2^62-1));
  Int64.shru (w 4%nat) (Int64.repr 40)] else
 [Int64.and (w 0%nat) (Int64.repr (2^52-1));
  Int64.and (Int64.or (Int64.shru (w 0%nat) (Int64.repr 52)) (Int64.shl (w 1%nat) (Int64.repr 10))) (Int64.repr (2^52-1));
  Int64.and (Int64.or (Int64.shru (w 1%nat) (Int64.repr 42)) (Int64.shl (w 2%nat) (Int64.repr 20))) (Int64.repr (2^52-1));
  Int64.and (Int64.or (Int64.shru (w 2%nat) (Int64.repr 32)) (Int64.shl (w 3%nat) (Int64.repr 30))) (Int64.repr (2^52-1));
  Int64.or (Int64.shru (w 3%nat) (Int64.repr 22)) (Int64.shl (w 4%nat) (Int64.repr 40))]) Int64.zero.
Definition fe_repack_run to62 := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160
 (fe_repack_function to62) fe_repack_args fe_repack_regs [] 5.
Definition fe_to62_tree := Eval vm_compute in fe_repack_run true.
Definition fe_from62_tree := Eval vm_compute in fe_repack_run false.
Definition fe_repack_tree (to62 : bool) := if to62 then fe_to62_tree else fe_from62_tree.
Definition fe_repack_state to62 := match fe_repack_tree to62 with
 | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition fe_repack_out_regs to62 :=
 [mkreg (u64_cells 0 (fe_repack_out to62)) true (Some 40);free_region (fe_reg (vars5 0)) 40].

Lemma fe_repack_run_eq to62 : fe_repack_run to62=Some (RDone (fe_repack_state to62) ONormal).
Proof. destruct to62;reflexivity. Qed.
Lemma fe_repack_return to62 : (stemps (fe_repack_state to62))!1%positive=None.
Proof. destruct to62;reflexivity. Qed.
Lemma fe_repack_output_shape to62 : sregs (fe_repack_state to62)=fe_repack_out_regs to62.
Proof. destruct to62;reflexivity. Qed.
Lemma fe_repack_output_den to62 rho beta :
 map (den rho (lay beta)) (fe_repack_out to62)=map Vlong (words5 (fe_repack_words to62 rho)).
Proof. destruct to62;reflexivity. Qed.

Theorem eval_fe_repack_symbolic to62 rho beta m : rep rho beta fe_repack_regs m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal (fe_repack_function to62))
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
 rep rho beta (fe_repack_out_regs to62) mf /\
 lframe (fun b pos => ~foot beta (map rshape fe_repack_regs) b pos) m mf.
Proof.
 intro HR.
 destruct (xfun_pure secp_ge secp_pure secp_pure_ok 160 (fe_repack_function to62)
  fe_repack_args fe_repack_regs 5 _ (fe_repack_run_eq to62) ltac:(destruct to62;reflexivity) rho beta m HR)
  as (mf & result & HC & HP & HV & HS & HL).
 cbn [rsel fst] in HP,HV;rewrite fe_repack_return in HV;subst result.
 change (map (den rho (lay beta)) fe_repack_args) with
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0))] in HC.
 rewrite !Z.add_0_r in HC;rewrite fe_repack_output_shape in HP.
 exists mf;split;[exact HC|];split;assumption.
Qed.

Lemma fe_repack_fields to62 w beta m : rep w beta (fe_repack_out_regs to62) m ->
 fe_at m (blk beta 0) (bas beta 0) (words5 (fe_repack_words to62 w)) /\
 fe_at m (blk beta 1) (bas beta 1) (words5 w) /\
 Mem.range_perm m (blk beta 0) 0 40 Cur Freeable /\
 Mem.range_perm m (blk beta 1) 0 40 Cur Freeable.
Proof.
 intro HR.
 pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
 pose proof (rep_region _ _ _ m 1 _ HR eq_refl) as H1.
 pose proof H0 as (_ & _ & _ & _ & _ & _ & HF0 & _).
 pose proof H1 as (_ & _ & _ & _ & _ & _ & HF1 & _).
 pose proof (region_ok_revalue_u64 w beta m 0 (fe_repack_out to62) true (Some 40) H0
   ltac:(destruct to62;reflexivity)) as V0.
 rewrite (revalue_u64_machine_map _ _ _ _ (fe_repack_output_den to62 w beta)) in V0.
 pose proof (region_ok_revalue_u64 w beta m 1 (vars5 0) true (Some 40) H1 eq_refl) as V1.
 assert (HD : map (den w (lay beta)) (vars5 0)=map Vlong (words5 w)) by reflexivity.
 rewrite (revalue_u64_machine_map _ _ _ _ HD) in V1.
 split;[exact (u64_region_fe_at _ _ _ _ _ _ V0)|].
 split;[exact (u64_region_fe_at _ _ _ _ _ _ V1)|];split;assumption.
Qed.

Theorem eval_fe_repack_from_storage to62 w m bout bin : bout<>bin ->
 Mem.range_perm m bout 0 40 Cur Freeable -> fe_at m bin 0 (words5 w) ->
 Mem.range_perm m bin 0 40 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal (fe_repack_function to62))
  [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
 fe_at mf bout 0 (words5 (fe_repack_words to62 w)) /\ fe_at mf bin 0 (words5 w) /\
 Mem.range_perm mf bout 0 40 Cur Freeable /\ Mem.range_perm mf bin 0 40 Cur Freeable /\
 lframe (fun b _=>b<>bout /\ b<>bin) m mf.
Proof.
 intros NE FO FI FS.
 destruct (eval_fe_repack_symbolic to62 w [(bout,0);(bin,0)] m
   (negate_sep_initial w m bout bin NE FO FI FS)) as (mf & HC & HP & HL).
 destruct (fe_repack_fields to62 w [(bout,0);(bin,0)] mf HP) as (OF & IF & OFree & IFree).
 exists mf;split;[exact HC|];split;[exact OF|];split;[exact IF|];split;[exact OFree|];split;[exact IFree|].
 exact (curve_frame_two fe_repack_regs bout bin m mf eq_refl HL).
Qed.
