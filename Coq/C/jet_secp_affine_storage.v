(** Original affine storage decoder, with a readonly table source and an
    owned 88-byte affine destination. The two field calls are executed, not
    assumed or replaced by a reference implementation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure
 C.jet_sx_mem C.jet_sx_rep C.jet_sx_rename C.jet_secp_fns C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_b32_exec
 C.jet_secp_storage_unpack C.jet_secp_storage_numeric C.jet_secp_multiply_normalize_bridge.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition affine_storage_undef := mkreg
 [mkcell 0 Mint64 None;mkcell 8 Mint64 None;mkcell 16 Mint64 None;
  mkcell 24 Mint64 None;mkcell 32 Mint64 None;mkcell 40 Mint64 None;
  mkcell 48 Mint64 None;mkcell 56 Mint64 None;mkcell 64 Mint64 None;
  mkcell 72 Mint64 None;mkcell 80 Mint32 None] true (Some 88).
Definition affine_storage_input := map XLv (seq 0 8).
Definition affine_storage_regs :=
 [affine_storage_undef;mkreg (u64_cells 0 affine_storage_input) false None].
Definition affine_storage_cells :=
 u64_cells 0 storage_unpack_out ++
 u64_cells 40 (map (sx_rename (fun n => (n+4)%nat)) storage_unpack_out) ++
 [mkcell 80 Mint32 (Some (XIc Int.zero))].
Definition affine_storage_out_regs :=
 [mkreg affine_storage_cells true (Some 88);
  mkreg (u64_cells 0 affine_storage_input) false None].
Definition affine_storage_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160
 f_secp256k1_ge_from_storage [XP 0 0;XP 1 0] affine_storage_regs [] 8.
Definition affine_storage_tree := Eval vm_compute in affine_storage_run.
Definition affine_storage_state := match affine_storage_tree with
 | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.

Lemma affine_storage_run_eq : affine_storage_run=Some (RDone affine_storage_state ONormal).
Proof. reflexivity. Qed.
Lemma affine_storage_return : (stemps affine_storage_state)!1%positive=None.
Proof. reflexivity. Qed.
Lemma affine_storage_shape : sregs affine_storage_state=affine_storage_out_regs.
Proof. reflexivity. Qed.

Theorem eval_affine_storage_symbolic rho beta m : rep rho beta affine_storage_regs m ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_from_storage)
 [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
 rep rho beta affine_storage_out_regs mf /\
 lframe (fun b pos => ~foot beta (map rshape affine_storage_regs) b pos) m mf.
Proof.
 intro HR.
 destruct (xfun_pure secp_ge secp_pure secp_pure_ok 160 f_secp256k1_ge_from_storage
   [XP 0 0;XP 1 0] affine_storage_regs 8 _ affine_storage_run_eq eq_refl rho beta m HR)
   as (mf & result & HC & HP & HV & HS & HL).
 cbn [rsel fst] in HP,HV;rewrite affine_storage_return in HV;subst result.
 change (map (den rho (lay beta)) [XP 0 0;XP 1 0]) with
   [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0))] in HC.
 rewrite !Z.add_0_r in HC;rewrite affine_storage_shape in HP.
 exists mf;split;[exact HC|];split;assumption.
Qed.

Definition affine_storage_coord (w : nat->int64) (k : bool) :=
 storage_unpack_words (fun i => w ((if k then 4 else 0)+i)%nat).

Lemma affine_storage_output_fields w beta m : rep w beta affine_storage_out_regs m ->
 Mem.range_perm m (blk beta 0) 0 88 Cur Freeable /\
 (forall k : bool,fe_at m (blk beta 0) (if k then 40 else 0) (words5 (affine_storage_coord w k))) /\
 Mem.load Mint32 m (blk beta 0) 80=Some (Vint Int.zero).
Proof.
 intro HR.
 pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as R0.
 pose proof R0 as (HB & HV & Sorted & Cells & Owner).
 cbn [affine_storage_out_regs rfree rw] in Owner.
 destruct Owner as (Base & RW & Free & Size).
 split;[exact Free|];split.
 - intro k;unfold fe_at.
   split;[destruct k;lia|];split.
   + destruct k;[exists 5|exists 0];reflexivity.
   + split;[destruct k;change Ptrofs.max_unsigned with 18446744073709551615;lia|].
     split.
     * intros pos HP;eapply Mem.perm_implies;[apply Free;destruct k;lia|constructor].
     * intros i x HI.
       assert (BI : (i<5)%nat).
       { change (i<length (words5 (affine_storage_coord w k)))%nat;
         apply nth_error_Some;rewrite HI;discriminate. }
       set (xs := if k then map (sx_rename (fun n => (n+4)%nat)) storage_unpack_out
                  else storage_unpack_out).
       assert (Hin : In (mkcell ((if k then 40 else 0)+8*Z.of_nat i) Mint64
                      (Some (nth i xs (XL Int64.zero)))) affine_storage_cells).
       { unfold xs,affine_storage_cells;destruct k.
         - apply in_or_app;right;apply in_or_app;left.
           apply u64_cells_nth;apply nth_error_nth';exact BI.
         - apply in_or_app;left.
           apply u64_cells_nth;apply nth_error_nth';exact BI. }
       pose proof (region_load w beta m 0 _ _ _ _ R0 Hin) as Load.
       rewrite Base,Z.add_0_l in Load.
       unfold xs in Load.
       destruct k;destruct i as [|[|[|[|[|i]]]]];try lia;
         cbn [words5 affine_storage_coord storage_unpack_words nth_error nth] in HI;
         inversion HI;subst x;exact Load.
 - pose proof (region_load w beta m 0 _ 80 Mint32 (XIc Int.zero) R0) as Load.
   rewrite Base,Z.add_0_l in Load;apply Load.
   unfold affine_storage_cells;apply in_or_app;right;apply in_or_app;right;left;reflexivity.
Qed.

Definition affine_storage_readable m b base (w : nat->int64) : Prop :=
 0<=base /\ (8|base) /\ base+64<=Ptrofs.max_unsigned /\
 Mem.range_perm m b base (base+64) Cur Readable /\
 forall i,(i<8)%nat -> Mem.load Mint64 m b (base+8*Z.of_nat i)=Some (Vlong (w i)).

Lemma affine_storage_initial w m bout bin sbase :
 bout<>bin -> Mem.range_perm m bout 0 88 Cur Freeable ->
 affine_storage_readable m bin sbase w ->
 rep w [(bout,0);(bin,sbase)] affine_storage_regs m.
Proof.
 intros Sep Free (SB & SA & SM & Read & Loads).
 apply two_region_rep_separate;[reflexivity|exact Sep| |].
 - unfold region_ok;cbn [affine_storage_undef rcells rw rfree].
   unfold blk,bas,lay;cbn [nth fst snd].
   split;[lia|];split.
   + eapply Mem.perm_valid_block;apply (Free 0);lia.
   + split;[reflexivity|];split.
     * apply Forall_forall;intros c Hin;cbn in Hin.
       repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
         try contradiction;
         (cbv beta iota zeta delta [cell_ok cofs cchunk cval blk bas lay nth fst snd];
         cbn [size_chunk align_chunk];
         split;[change Ptrofs.max_unsigned with 18446744073709551615;lia|];
         split;[apply Z.mod_divide;[lia|reflexivity]|];split;
         [intros pos HP;eapply Mem.perm_implies;[apply Free;lia|constructor]
         |intros x HX;discriminate]).
     * split;[reflexivity|];split;[reflexivity|];split;[exact Free|].
       apply Forall_forall;intros c Hin;cbn in Hin.
       repeat match goal with H : _ \/ _ |- _ => destruct H as [<-|H] end;
         try contradiction;cbn [cofs cchunk size_chunk];lia.
 - apply region_u64.
   + exact SB.
   + exact SA.
   + exact SM.
   + eapply Mem.perm_valid_block;apply (Read sbase);lia.
   + exact Read.
   + intros i x HI.
     assert (BI : (i<8)%nat).
     { change (i<length affine_storage_input)%nat;apply nth_error_Some;rewrite HI;discriminate. }
     destruct i as [|[|[|[|[|[|[|[|i]]]]]]]];try lia;
       cbn [affine_storage_input map seq nth_error] in HI;inversion HI;subst x;
       (split;[apply Loads;lia|reflexivity]).
Qed.

Lemma affine_storage_source w beta m r :
 region_ok w beta m r (mkreg (u64_cells 0 affine_storage_input) false None) ->
 affine_storage_readable m (blk beta r) (bas beta r) w.
Proof.
 intros (HB & HV & Sorted & Cells & Owner).
 assert (Cell : forall i,(i<8)%nat ->
   cell_ok w beta m r false (mkcell (8*Z.of_nat i) Mint64 (Some (XLv i)))).
 { intros i HI;apply (proj1 (Forall_forall _ _) Cells).
   change (In (mkcell (0+8*Z.of_nat i) Mint64 (Some (XLv i)))
     (u64_cells 0 affine_storage_input)).
   apply u64_cells_nth.
   destruct i as [|[|[|[|[|[|[|[|i]]]]]]]];try lia;reflexivity. }
 pose proof (Cell 0%nat ltac:(lia)) as C0.
 pose proof (Cell 1%nat ltac:(lia)) as C1.
 pose proof (Cell 2%nat ltac:(lia)) as C2.
 pose proof (Cell 3%nat ltac:(lia)) as C3.
 pose proof (Cell 4%nat ltac:(lia)) as C4.
 pose proof (Cell 5%nat ltac:(lia)) as C5.
 pose proof (Cell 6%nat ltac:(lia)) as C6.
 pose proof (Cell 7%nat ltac:(lia)) as C7.
 cbv beta iota zeta delta [cell_ok cofs cchunk cval] in C0,C1,C2,C3,C4,C5,C6,C7.
 change (size_chunk Mint64) with 8 in C0,C1,C2,C3,C4,C5,C6,C7.
 change (align_chunk Mint64) with 8 in C0.
 destruct C0 as (M0 & A0 & P0 & V0).
 destruct C1 as (M1 & A1 & P1 & V1).
 destruct C2 as (M2 & A2 & P2 & V2).
 destruct C3 as (M3 & A3 & P3 & V3).
 destruct C4 as (M4 & A4 & P4 & V4).
 destruct C5 as (M5 & A5 & P5 & V5).
 destruct C6 as (M6 & A6 & P6 & V6).
 destruct C7 as (M7 & A7 & P7 & V7).
 split;[exact HB|];split;[replace (8*Z.of_nat 0) with 0 in A0 by reflexivity;
   rewrite Z.add_0_r in A0;exact A0|];split;[lia|];split.
 - intros pos HP.
   destruct (Z_lt_dec pos (bas beta r+8));[apply P0;lia|].
   destruct (Z_lt_dec pos (bas beta r+16));[apply P1;lia|].
   destruct (Z_lt_dec pos (bas beta r+24));[apply P2;lia|].
   destruct (Z_lt_dec pos (bas beta r+32));[apply P3;lia|].
   destruct (Z_lt_dec pos (bas beta r+40));[apply P4;lia|].
   destruct (Z_lt_dec pos (bas beta r+48));[apply P5;lia|].
   destruct (Z_lt_dec pos (bas beta r+56));[apply P6;lia|].
   apply P7;lia.
 - intros i HI;pose proof (Cell i HI) as (_ & _ & _ & Load).
   exact (proj1 (Load _ eq_refl)).
Qed.

Theorem eval_ge_from_storage_readonly w m bout bin sbase :
 bout<>bin -> Mem.range_perm m bout 0 88 Cur Freeable ->
 affine_storage_readable m bin sbase w ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_from_storage)
   [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr sbase)] E0 mf Vundef /\
 Mem.range_perm mf bout 0 88 Cur Freeable /\
 (forall k : bool,fe_at mf bout (if k then 40 else 0) (words5 (affine_storage_coord w k))) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\
 affine_storage_readable mf bin sbase w /\
 lframe (fun b pos => ~foot [(bout,0);(bin,sbase)] (map rshape affine_storage_regs) b pos) m mf.
Proof.
 intros Sep Free Input.
 destruct (eval_affine_storage_symbolic w [(bout,0);(bin,sbase)] m
   (affine_storage_initial w m bout bin sbase Sep Free Input))
   as (mf & Exec & Rep & Frame).
 destruct (affine_storage_output_fields w [(bout,0);(bin,sbase)] mf Rep)
   as (Owned & Fields & Infinity).
 pose proof (rep_region _ _ _ mf 1 _ Rep eq_refl) as Source.
 pose proof (affine_storage_source w [(bout,0);(bin,sbase)] mf 1 Source) as Readable.
 exists mf;split;[exact Exec|];split;[exact Owned|];split;[exact Fields|];
   split;[exact Infinity|];split;assumption.
Qed.

Theorem affine_storage_exact_coordinate w k :
 map Int64.unsigned (words5 (affine_storage_coord w k))=
   C.jet_secp_fe_math.fe_limbs_of (field_storage_value (fun i => w ((if k then 4 else 0)+i)%nat)).
Proof. apply storage_unpack_exact_limbs. Qed.
