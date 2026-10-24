(** Actual 64/62-bit scalar conversion calls used by scalar_inverse_var.
    The two original functions share an execution/storage interface. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_sx_revalue_cells C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv.
Require Import C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_local_regions C.jet_secp_curve_frame.
Require Import C.jet_secp_scalar_add_initial C.jet_secp_scalar_get_b32_storage C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_point_mul_storage C.jet_secp_field_add_initial.
Require C.jet_secp_scalar_split128_storage.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition scalar62_function (to62:bool) := if to62 then f_secp256k1_scalar_to_signed62 else f_secp256k1_scalar_from_signed62.
Definition scalar62_size (signed:bool) : Z := if signed then 40 else 32.
Definition scalar62_vars (signed:bool) := if signed then vars5 0 else scalar_add_vars 0.
Definition scalar62_values (signed:bool) (w:nat->int64) := if signed then words5 w else scalar_add_values w 0.
Definition scalar62_storage (signed:bool) w m b :=
  if signed then fe_at m b 0 (words5 w) else scalar_at m b 0 (scalar_add_values w 0).
Definition scalar62_undef (signed:bool) :=
  if signed then fe_undef else mkreg(firstn 4 (rcells fe_undef)) true None.
Definition scalar62_regs (to62:bool) :=
  [free_region(scalar62_undef to62)(scalar62_size to62);
   free_region(mkreg(u64_cells 0 (scalar62_vars(negb to62))) true None)(scalar62_size(negb to62))].
Definition scalar62_exprs (to62:bool) : list sx := if to62 then
  [XLb Band (XLv 0) (XLsh Hshru (XLc Int64.mone) 2);
   XLb Band (XLb Bor (XLsh Hshru (XLv 0) 62) (XLsh Hshl (XLv 1) 2)) (XLsh Hshru (XLc Int64.mone) 2);
   XLb Band (XLb Bor (XLsh Hshru (XLv 1) 60) (XLsh Hshl (XLv 2) 4)) (XLsh Hshru (XLc Int64.mone) 2);
   XLb Band (XLb Bor (XLsh Hshru (XLv 2) 58) (XLsh Hshl (XLv 3) 6)) (XLsh Hshru (XLc Int64.mone) 2);
   XLsh Hshru (XLv 3) 56]
  else
  [XLb Bor (XLv 0) (XLsh Hshl (XLv 1) 62);
   XLb Bor (XLsh Hshru (XLv 1) 2) (XLsh Hshl (XLv 2) 60);
   XLb Bor (XLsh Hshru (XLv 2) 4) (XLsh Hshl (XLv 3) 58);
   XLb Bor (XLsh Hshru (XLv 3) 6) (XLsh Hshl (XLv 4) 56)].
Definition scalar62_words (to62:bool) (w:nat->int64) i := nth i (if to62 then
  [Int64.and(w 0%nat)(Int64.repr(2^62-1));
   Int64.and(Int64.or(Int64.shru(w 0%nat)(Int64.repr 62))(Int64.shl(w 1%nat)(Int64.repr 2)))(Int64.repr(2^62-1));
   Int64.and(Int64.or(Int64.shru(w 1%nat)(Int64.repr 60))(Int64.shl(w 2%nat)(Int64.repr 4)))(Int64.repr(2^62-1));
   Int64.and(Int64.or(Int64.shru(w 2%nat)(Int64.repr 58))(Int64.shl(w 3%nat)(Int64.repr 6)))(Int64.repr(2^62-1));
   Int64.shru(w 3%nat)(Int64.repr 56)] else
  [Int64.or(w 0%nat)(Int64.shl(w 1%nat)(Int64.repr 62));
   Int64.or(Int64.shru(w 1%nat)(Int64.repr 2))(Int64.shl(w 2%nat)(Int64.repr 60));
   Int64.or(Int64.shru(w 2%nat)(Int64.repr 4))(Int64.shl(w 3%nat)(Int64.repr 58));
   Int64.or(Int64.shru(w 3%nat)(Int64.repr 6))(Int64.shl(w 4%nat)(Int64.repr 56))]) Int64.zero.
Definition scalar62_run to62 := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160
  (scalar62_function to62) [XP 0 0;XP 1 0] (scalar62_regs to62) [] 5.
Definition scalar_to62_tree := Eval vm_compute in scalar62_run true.
Definition scalar_from62_tree := Eval vm_compute in scalar62_run false.
Definition scalar62_state (to62:bool) := match (if to62 then scalar_to62_tree else scalar_from62_tree) with
  | Some(RDone st _)=>st | _=>mkst(PTree.empty sx) [] [] 0 end.
Definition scalar62_out_regs to62 :=
  [mkreg(u64_cells 0 (scalar62_exprs to62)) true (Some(scalar62_size to62));
   free_region(mkreg(u64_cells 0 (scalar62_vars(negb to62))) true None)(scalar62_size(negb to62))].
Lemma scalar62_run_eq to62 : scalar62_run to62=Some(RDone(scalar62_state to62) ONormal).
Proof. destruct to62;reflexivity. Qed.
Lemma scalar62_return to62 : (stemps(scalar62_state to62))!1%positive=None.
Proof. destruct to62;reflexivity. Qed.
Lemma scalar62_output_shape to62 : sregs(scalar62_state to62)=scalar62_out_regs to62.
Proof. destruct to62;reflexivity. Qed.
Lemma scalar62_output_den to62 w beta : map(den w(lay beta))(scalar62_exprs to62)=
  map Vlong(scalar62_values to62 (scalar62_words to62 w)).
Proof. destruct to62;reflexivity. Qed.

Theorem eval_scalar62_symbolic to62 w beta m : rep w beta (scalar62_regs to62) m -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal(scalar62_function to62))
    [Vptr(blk beta 0)(Ptrofs.repr(bas beta 0));Vptr(blk beta 1)(Ptrofs.repr(bas beta 1))] E0 mf Vundef /\
  rep w beta (scalar62_out_regs to62) mf /\
  lframe (fun b pos=>~foot beta (map rshape(scalar62_regs to62)) b pos) m mf.
Proof.
  intro Initial.
  destruct(xfun_pure secp_ge secp_pure secp_pure_ok 160 (scalar62_function to62)
    [XP 0 0;XP 1 0] (scalar62_regs to62) 5 _ (scalar62_run_eq to62)
    ltac:(destruct to62;reflexivity) w beta m Initial)
    as (mf & result & Call & Final & Return & Shape & Frame).
  cbn [rsel fst] in Final,Return;rewrite scalar62_return in Return;subst result.
  change(map(den w(lay beta))[XP 0 0;XP 1 0]) with
    [Vptr(blk beta 0)(Ptrofs.repr(bas beta 0+0));Vptr(blk beta 1)(Ptrofs.repr(bas beta 1+0))] in Call.
  rewrite !Z.add_0_r in Call;rewrite scalar62_output_shape in Final.
  exists mf;split;[exact Call|];split;assumption.
Qed.

Lemma scalar62_empty_region signed rho beta m r : bas beta r=0 ->
  Mem.range_perm m (blk beta r) 0 (scalar62_size signed) Cur Freeable ->
  region_ok rho beta m r (free_region(scalar62_undef signed)(scalar62_size signed)).
Proof.
  intros Base Free;destruct signed.
  - apply region_with_freeable.
    + apply region_fe_undefined_from_storage;rewrite Base;
        [lia|exists 0;reflexivity|change(40<=18446744073709551615);lia|].
      apply freeable_range_writable;exact Free.
    + exact Base.
    + reflexivity.
    + exact Free.
    + apply fe_undef_storage_size.
  - exact(C.jet_secp_scalar_split128_storage.scalar_split128_empty_region rho beta m r Base Free).
Qed.

Lemma scalar62_initial to62 w m bout bin : bout<>bin ->
  Mem.range_perm m bout 0 (scalar62_size to62) Cur Freeable ->
  scalar62_storage (negb to62) w m bin ->
  Mem.range_perm m bin 0 (scalar62_size(negb to62)) Cur Freeable ->
  rep w [(bout,0);(bin,0)] (scalar62_regs to62) m.
Proof.
  intros Separate Out Input InFree;apply two_region_rep_separate;[reflexivity|exact Separate| |].
  - apply scalar62_empty_region;[reflexivity|exact Out].
  - destruct to62.
    + apply scalar_add_region_from_values;[reflexivity|exact Input|exact InFree].
    + apply owned_field_slice_region with (ofs:=0) (size:=40);[reflexivity|lia|lia|exact Input|exact InFree].
Qed.

Lemma scalar62_region_storage signed rho w beta m r :
  region_ok rho beta m r
    (mkreg(u64_cells 0 (map XL(scalar62_values signed w))) true (Some(scalar62_size signed))) ->
  scalar62_storage signed w m (blk beta r).
Proof.
  intro Region;pose proof Region as (_ & _ & _ & _ & Base & _ & Free & _).
  destruct signed.
  - pose proof(u64_region_fe_at rho beta m r w (Some 40) Region) as Field.
    rewrite Base in Field;exact Field.
  - unfold scalar62_storage,scalar_at;split;[reflexivity|];split;[lia|];
      split;[exists 0;reflexivity|];split;[change(32<=18446744073709551615);lia|];split.
    + intros pos Range;eapply Mem.perm_implies;[apply Free;exact Range|constructor].
    + intros i word At;rewrite Z.add_0_l.
      assert(Mapped:nth_error(map XL(scalar62_values false w))i=Some(XL word)).
      { change(nth_error(map XL(scalar_add_values w 0))i=Some(XL word));rewrite nth_error_map,At;reflexivity. }
      pose proof(region_load _ _ _ _ _ _ _ _ Region (u64_cells_nth _ 0 i (XL word) Mapped)) as Load.
      rewrite Base,!Z.add_0_l in Load;exact Load.
Qed.

Lemma scalar62_final to62 w beta m : rep w beta (scalar62_out_regs to62) m ->
  scalar62_storage to62 (scalar62_words to62 w) m (blk beta 0) /\
  scalar62_storage (negb to62) w m (blk beta 1) /\
  Mem.range_perm m (blk beta 0) 0 (scalar62_size to62) Cur Freeable /\
  Mem.range_perm m (blk beta 1) 0 (scalar62_size(negb to62)) Cur Freeable.
Proof.
  intro Final.
  pose proof(rep_region _ _ _ m 0 _ Final eq_refl) as R0.
  pose proof(rep_region _ _ _ m 1 _ Final eq_refl) as R1.
  pose proof R0 as (_ & _ & _ & _ & _ & _ & F0 & _).
  pose proof R1 as (_ & _ & _ & _ & _ & _ & F1 & _).
  pose proof(region_ok_revalue_u64 w beta m 0 (scalar62_exprs to62) true (Some(scalar62_size to62)) R0
    ltac:(destruct to62;reflexivity)) as V0.
  rewrite(revalue_u64_machine_map _ _ _ _ (scalar62_output_den to62 w beta)) in V0.
  pose proof(region_ok_revalue_u64 w beta m 1 (scalar62_vars(negb to62)) true
    (Some(scalar62_size(negb to62))) R1 ltac:(destruct to62;reflexivity)) as V1.
  assert(Den:map(den w(lay beta))(scalar62_vars(negb to62))=map Vlong(scalar62_values(negb to62)w))
    by (destruct to62;reflexivity).
  rewrite(revalue_u64_machine_map _ _ _ _ Den) in V1.
  split;[eapply scalar62_region_storage;exact V0|];split;
    [eapply scalar62_region_storage;exact V1|];split;assumption.
Qed.

Theorem eval_scalar62_from_storage to62 w m bout bin : bout<>bin ->
  Mem.range_perm m bout 0 (scalar62_size to62) Cur Freeable ->
  scalar62_storage(negb to62)w m bin ->
  Mem.range_perm m bin 0 (scalar62_size(negb to62)) Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal(scalar62_function to62))
    [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
  scalar62_storage to62 (scalar62_words to62 w) mf bout /\ scalar62_storage(negb to62)w mf bin /\
  Mem.range_perm mf bout 0 (scalar62_size to62) Cur Freeable /\
  Mem.range_perm mf bin 0 (scalar62_size(negb to62)) Cur Freeable /\
  lframe (fun b _=>b<>bout /\ b<>bin) m mf.
Proof.
  intros Separate Out Input InFree.
  destruct(eval_scalar62_symbolic to62 w [(bout,0);(bin,0)] m
    (scalar62_initial to62 w m bout bin Separate Out Input InFree)) as (mf & Call & Final & Frame).
  destruct(scalar62_final to62 w [(bout,0);(bin,0)] mf Final) as (Output & Source & FO & FI).
  assert(Outside:lframe (fun b _=>b<>bout /\ b<>bin) m mf).
  { eapply curve_frame_two with (regs:=scalar62_regs to62);[reflexivity|exact Frame]. }
  exists mf;repeat first[assumption|split].
Qed.
