(** Original field-storage unpacker, with a readonly source region. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem
  C.jet_sx_rep C.jet_sx_revalue_cells C.jet_secp_fns C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_local_regions C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_b32_exec.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition storage_unpack_args := [XP 0 0;XP 1 0].
Definition storage_unpack_input := [XLv 0;XLv 1;XLv 2;XLv 3].
Definition storage_unpack_regs :=
  [fe_undef;mkreg (u64_cells 0 storage_unpack_input) false None].
Definition storage_unpack_out :=
  [XLb Band (XLv 0) (XLc (Int64.repr (2^52-1)));
   XLb Bor (XLsh Hshru (XLv 0) 52) (XLb Band (XLsh Hshl (XLv 1) 12) (XLc (Int64.repr (2^52-1))));
   XLb Bor (XLsh Hshru (XLv 1) 40) (XLb Band (XLsh Hshl (XLv 2) 24) (XLc (Int64.repr (2^52-1))));
   XLb Bor (XLsh Hshru (XLv 2) 28) (XLb Band (XLsh Hshl (XLv 3) 36) (XLc (Int64.repr (2^52-1))));
   XLsh Hshru (XLv 3) 16].
Definition storage_unpack_words (w : nat->int64) i := nth i
  [Int64.and (w 0%nat) (Int64.repr (2^52-1));
   Int64.or (Int64.shru (w 0%nat) (Int64.repr 52))
     (Int64.and (Int64.shl (w 1%nat) (Int64.repr 12)) (Int64.repr (2^52-1)));
   Int64.or (Int64.shru (w 1%nat) (Int64.repr 40))
     (Int64.and (Int64.shl (w 2%nat) (Int64.repr 24)) (Int64.repr (2^52-1)));
   Int64.or (Int64.shru (w 2%nat) (Int64.repr 28))
     (Int64.and (Int64.shl (w 3%nat) (Int64.repr 36)) (Int64.repr (2^52-1)));
   Int64.shru (w 3%nat) (Int64.repr 16)] Int64.zero.
Definition storage_unpack_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 80
  f_secp256k1_fe_from_storage storage_unpack_args storage_unpack_regs [] 4.
Definition storage_unpack_tree := Eval vm_compute in storage_unpack_run.
Definition storage_unpack_state := match storage_unpack_tree with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition storage_unpack_out_regs :=
  [mkreg (u64_cells 0 storage_unpack_out) true None;
   mkreg (u64_cells 0 storage_unpack_input) false None].

Lemma storage_unpack_run_eq : storage_unpack_run=Some (RDone storage_unpack_state ONormal).
Proof. reflexivity. Qed.
Lemma storage_unpack_return : (stemps storage_unpack_state)!1%positive=None.
Proof. reflexivity. Qed.
Lemma storage_unpack_output_shape : sregs storage_unpack_state=storage_unpack_out_regs.
Proof. reflexivity. Qed.
Lemma storage_unpack_output_den rho beta :
  map (den rho (lay beta)) storage_unpack_out=map Vlong (words5 (storage_unpack_words rho)).
Proof. reflexivity. Qed.

Theorem eval_storage_unpack_symbolic rho beta m : rep rho beta storage_unpack_regs m -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_from_storage)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
  rep rho beta storage_unpack_out_regs mf /\
  lframe (fun b pos => ~foot beta (map rshape storage_unpack_regs) b pos) m mf.
Proof.
  intro HR.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 80 f_secp256k1_fe_from_storage
    storage_unpack_args storage_unpack_regs 4 _ storage_unpack_run_eq eq_refl rho beta m HR)
    as (mf & result & HC & HP & HV & HS & HL).
  cbn [rsel fst] in HP,HV;rewrite storage_unpack_return in HV;subst result.
  change (map (den rho (lay beta)) storage_unpack_args) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0))] in HC.
  rewrite !Z.add_0_r in HC;rewrite storage_unpack_output_shape in HP.
  exists mf;split;[exact HC|];split;assumption.
Qed.

Definition field_storage_readable m b base (w : nat->int64) : Prop :=
  0<=base /\ (8|base) /\ base+32<=Ptrofs.max_unsigned /\
  Mem.range_perm m b base (base+32) Cur Readable /\
  forall i, (i<4)%nat -> Mem.load Mint64 m b (base+8*Z.of_nat i)=Some (Vlong (w i)).

Lemma storage_unpack_initial w m bout dbase bin sbase :
  bout<>bin -> 0<=dbase -> (8|dbase) -> dbase+40<=Ptrofs.max_unsigned ->
  Mem.range_perm m bout dbase (dbase+40) Cur Writable ->
  field_storage_readable m bin sbase w ->
  rep w [(bout,dbase);(bin,sbase)] storage_unpack_regs m.
Proof.
  intros Separate Base Align Max Writable (SBase & SAlign & SMax & Readable & Loads).
  apply two_region_rep_separate;[reflexivity|exact Separate| |].
  - apply region_fe_undefined_from_storage;assumption.
  - apply region_u64.
    + exact SBase.
    + exact SAlign.
    + exact SMax.
    + eapply Mem.perm_valid_block;apply (Readable sbase);lia.
    + exact Readable.
    + intros i x Nth;destruct i as [|[|[|[|i]]]];cbn [storage_unpack_input nth_error] in Nth;
        try (destruct i;discriminate);inversion Nth;subst x;split;try reflexivity;
        apply Loads;lia.
Qed.

Lemma storage_readable_region w beta m r :
  region_ok w beta m r (mkreg (u64_cells 0 storage_unpack_input) false None) ->
  field_storage_readable m (blk beta r) (bas beta r) w.
Proof.
  intros (HB & HV & Sorted & Cells & Owner).
  cbn [storage_unpack_input u64_cells] in Cells.
  inversion Cells as [|? ? C0 T0];subst.
  inversion T0 as [|? ? C1 T1];subst.
  inversion T1 as [|? ? C2 T2];subst.
  inversion T2 as [|? ? C3 T3];subst.
  cbv beta iota zeta delta [cell_ok cofs cchunk cval den] in C0,C1,C2,C3.
  change (size_chunk Mint64) with 8 in C0,C1,C2,C3.
  change (align_chunk Mint64) with 8 in C0.
  destruct C0 as (M0 & A0 & P0 & V0).
  destruct C1 as (M1 & A1 & P1 & V1).
  destruct C2 as (M2 & A2 & P2 & V2).
  destruct C3 as (M3 & A3 & P3 & V3).
  split;[exact HB|];split;[rewrite Z.add_0_r in A0;exact A0|];split;[lia|];split.
  - intros pos Range.
    destruct (Z_lt_dec pos (bas beta r+8));[apply P0;lia|].
    destruct (Z_lt_dec pos (bas beta r+16));[apply P1;lia|].
    destruct (Z_lt_dec pos (bas beta r+24));[apply P2;lia|].
    apply P3;lia.
  - intros i Index;destruct i as [|[|[|[|i]]]];try lia;
      first [exact (proj1 (V0 _ eq_refl))|exact (proj1 (V1 _ eq_refl))|
        exact (proj1 (V2 _ eq_refl))|exact (proj1 (V3 _ eq_refl))].
Qed.

Lemma storage_unpack_fields w beta m : rep w beta storage_unpack_out_regs m ->
  fe_at m (blk beta 0) (bas beta 0) (words5 (storage_unpack_words w)) /\
  field_storage_readable m (blk beta 1) (bas beta 1) w.
Proof.
  intro HR.
  pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof (rep_region _ _ _ m 1 _ HR eq_refl) as H1.
  split;[|apply storage_readable_region;exact H1].
  pose proof (region_ok_revalue_u64 w beta m 0 storage_unpack_out true None H0 eq_refl) as Values.
  rewrite (revalue_u64_machine_map _ _ _ _ (storage_unpack_output_den w beta)) in Values.
  exact (u64_region_fe_at w beta m 0 _ None Values).
Qed.

Theorem eval_fe_from_storage_readonly w m bout dbase bin sbase :
  bout<>bin -> 0<=dbase -> (8|dbase) -> dbase+40<=Ptrofs.max_unsigned ->
  Mem.range_perm m bout dbase (dbase+40) Cur Writable ->
  field_storage_readable m bin sbase w ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_from_storage)
      [Vptr bout (Ptrofs.repr dbase);Vptr bin (Ptrofs.repr sbase)] E0 mf Vundef /\
    fe_at mf bout dbase (words5 (storage_unpack_words w)) /\ field_storage_readable mf bin sbase w /\
    lframe (fun b pos => ~foot [(bout,dbase);(bin,sbase)] (map rshape storage_unpack_regs) b pos) m mf.
Proof.
  intros Separate Base Align Max Writable Readable.
  destruct (eval_storage_unpack_symbolic w [(bout,dbase);(bin,sbase)] m
    (storage_unpack_initial w m bout dbase bin sbase Separate Base Align Max Writable Readable))
    as (mf & Exec & Rep & Frame).
  destruct (storage_unpack_fields w [(bout,dbase);(bin,sbase)] mf Rep) as (Output & Input).
  exists mf;split;[exact Exec|];split;[exact Output|];split;assumption.
Qed.
