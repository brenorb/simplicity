(** Exact original normalize_62 C call on owned signed62 storage and a
    read-only modulus. Numeric modular-normalization and public inversion
    composition remain separate obligations; this adds no jet coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_local_regions.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition norm62_regs :=
 [free_region (fe_reg (vars5 0)) 40; mkreg (u64_cells 0 (vars5 5)) false None].
Definition norm62_args := [XP 0 0; XLv 10; XP 1 0].
Definition norm62_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 240
 f_secp256k1_modinv64_normalize_62 norm62_args norm62_regs [] 11.
Definition norm62_tree := Eval vm_compute in norm62_run.
Definition norm62_state := match norm62_tree with
 | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.

Lemma norm62_run_eq : norm62_run = Some (RDone norm62_state ONormal).
Proof. reflexivity. Qed.
Lemma norm62_return : (stemps norm62_state)!1%positive = None.
Proof. reflexivity. Qed.

Definition norm62_mask := XLsh Hshru (XLc (Int64.repr (-1))) 2.
Definition norm62_add (xs : list sx) :=
 map (fun i => XLb Badd (nth i xs (XLc Int64.zero))
   (XLb Band (XLv (5+i)%nat) (XLsh Hshr (nth 4 xs (XLc Int64.zero)) 63)))
   [0;1;2;3;4]%nat.
Definition norm62_neg (xs : list sx) :=
 map (fun x => XLb Bsub (XLb Bxor x (XLsh Hshr (XLv 10) 63))
   (XLsh Hshr (XLv 10) 63)) xs.
Definition norm62_carry (xs : list sx) :=
 let r0 := nth 0 xs (XLc Int64.zero) in
 let r1 := XLb Badd (nth 1 xs (XLc Int64.zero)) (XLsh Hshr r0 62) in
 let r2 := XLb Badd (nth 2 xs (XLc Int64.zero)) (XLsh Hshr r1 62) in
 let r3 := XLb Badd (nth 3 xs (XLc Int64.zero)) (XLsh Hshr r2 62) in
 let r4 := XLb Badd (nth 4 xs (XLc Int64.zero)) (XLsh Hshr r3 62) in
 [XLb Band r0 norm62_mask; XLb Band r1 norm62_mask;
  XLb Band r2 norm62_mask; XLb Band r3 norm62_mask; r4].
Definition norm62_out := norm62_carry (norm62_add (norm62_carry (norm62_neg (norm62_add (vars5 0))))).
Definition norm62_out_regs :=
 [mkreg (u64_cells 0 norm62_out) true (Some 40); mkreg (u64_cells 0 (vars5 5)) false None].

Lemma norm62_output_shape : sregs norm62_state = norm62_out_regs.
Proof. reflexivity. Qed.

Definition norm62_add_words (w modulus : nat -> int64) i :=
 Int64.add (w i) (Int64.and (modulus i) (Int64.shr (w 4%nat) (Int64.repr 63))).
Definition norm62_neg_words (w : nat -> int64) (sign : int64) i :=
 Int64.sub (Int64.xor (w i) (Int64.shr sign (Int64.repr 63))) (Int64.shr sign (Int64.repr 63)).
Definition norm62_carry_words (w : nat -> int64) i :=
 let r0 := w 0%nat in
 let r1 := Int64.add (w 1%nat) (Int64.shr r0 (Int64.repr 62)) in
 let r2 := Int64.add (w 2%nat) (Int64.shr r1 (Int64.repr 62)) in
 let r3 := Int64.add (w 3%nat) (Int64.shr r2 (Int64.repr 62)) in
 let r4 := Int64.add (w 4%nat) (Int64.shr r3 (Int64.repr 62)) in
 nth i [Int64.and r0 (Int64.repr (2^62-1)); Int64.and r1 (Int64.repr (2^62-1));
  Int64.and r2 (Int64.repr (2^62-1)); Int64.and r3 (Int64.repr (2^62-1)); r4] Int64.zero.
Definition norm62_machine w modulus sign :=
 norm62_carry_words (norm62_add_words (norm62_carry_words
   (norm62_neg_words (norm62_add_words w modulus) sign)) modulus).

Require Import C.jet_secp_multiply_normalize_bridge.
Lemma norm62_output_den rho beta :
 map (den rho (lay beta)) norm62_out =
 map Vlong (words5 (norm62_machine rho (fun i => rho (5+i)%nat) (rho 10%nat))).
Proof. reflexivity. Qed.

Theorem eval_norm62_symbolic rho beta m : rep rho beta norm62_regs m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_normalize_62)
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0)); Vlong (rho 10%nat);
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
 rep rho beta norm62_out_regs mf /\
 lframe (fun b o => ~ foot beta (map rshape norm62_regs) b o) m mf.
Proof.
 intro HR.
 destruct (xfun_pure secp_ge secp_pure secp_pure_ok 240 f_secp256k1_modinv64_normalize_62
   norm62_args norm62_regs 11 _ norm62_run_eq eq_refl rho beta m HR)
   as (mf & result & Call & Out & Ret & Shapes & Frame).
 cbn [rsel fst] in Out, Ret. rewrite norm62_return in Ret. subst result.
 change (map (den rho (lay beta)) norm62_args) with
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0));Vlong (rho 10%nat);
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0))] in Call.
 rewrite !Z.add_0_r in Call. rewrite norm62_output_shape in Out.
 exists mf. exact (conj Call (conj Out Frame)).
Qed.


Require Import C.jet_secp_field_add_initial C.jet_secp_b32_exec C.jet_sx_revalue_cells.

Definition norm62_modulus_at (m : mem) b (w : nat -> int64) : Prop :=
 Mem.range_perm m b 0 40 Cur Readable /\
 forall i, (i<5)%nat -> Mem.load Mint64 m b (8*Z.of_nat i) = Some (Vlong (w i)).

Lemma norm62_initial rho m br bm : br <> bm ->
 fe_at m br 0 (words5 rho) -> Mem.range_perm m br 0 40 Cur Freeable ->
 norm62_modulus_at m bm (fun i => rho (5+i)%nat) ->
 rep rho [(br,0);(bm,0)] norm62_regs m.
Proof.
 intros NE Field Free (Read & Words).
 apply two_region_rep_separate; [reflexivity|exact NE| |].
 - apply region_with_freeable.
   + apply field_region_from_values; exact Field.
   + reflexivity.
   + reflexivity.
   + exact Free.
   + apply field_region_storage_size.
 - apply region_u64.
   + change (0<=0); lia.
   + exists 0; reflexivity.
   + change (40<=18446744073709551615); lia.
   + eapply Mem.perm_valid_block; apply (Read 0); lia.
   + exact Read.
   + intros i x At. destruct i as [|[|[|[|[|i]]]]];
      try (destruct i; discriminate);
      (injection At as <-; split; [apply Words;lia|reflexivity]).
Qed.

Lemma norm62_words_readable m b (w : nat -> int64) :
 (forall i, (i<5)%nat -> Mem.load Mint64 m b (8*Z.of_nat i) = Some (Vlong (w i))) ->
 Mem.range_perm m b 0 40 Cur Readable.
Proof.
 intros Loads pos Range.
 set (i := Z.to_nat (pos/8)).
 assert (Q : 0<=pos/8<5) by (split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]).
 assert (I : (i<5)%nat) by (unfold i;lia).
 pose proof (Mem.load_valid_access _ _ _ _ _ (Loads i I)) as (Perm & Align).
 apply Perm. change (8*Z.of_nat i <= pos < 8*Z.of_nat i+8).
 unfold i. rewrite Z2Nat.id by lia.
 pose proof (Z.div_mod pos 8 ltac:(lia)); pose proof (Z.mod_pos_bound pos 8 ltac:(lia));lia.
Qed.

Lemma norm62_foot br bm b pos :
 foot [(br,0);(bm,0)] (map rshape norm62_regs) b pos ->
 (b=br /\ 0<=pos<40) \/ (b=bm /\ 0<=pos<40).
Proof.
 intros (r & sh & d & ch & Nth & Cell & Block & Offset).
 destruct r as [|[|r]].
 - left. split; [exact Block|].
   cbn [norm62_regs free_region fe_reg vars5 u64_cells rshape rcells rw rfree map nth_error] in Nth.
   injection Nth as <-.
   cbn [fst map cshape cofs cchunk] in Cell.
   destruct Cell as [C|[C|[C|[C|[C|C]]]]]; [| | | | |contradiction];
    inversion C; subst d ch; cbn [bas lay nth snd] in Offset;
    change (size_chunk Mint64) with 8 in Offset; lia.
 - right. split; [exact Block|].
   cbn [norm62_regs free_region fe_reg vars5 u64_cells rshape rcells rw rfree map nth_error] in Nth.
   injection Nth as <-.
   cbn [fst map cshape cofs cchunk] in Cell.
   destruct Cell as [C|[C|[C|[C|[C|C]]]]]; [| | | | |contradiction];
    inversion C; subst d ch; cbn [bas lay nth snd] in Offset;
    change (size_chunk Mint64) with 8 in Offset; lia.
 - destruct r; discriminate Nth.
Qed.

Definition norm62_outside (br bm b : block) (pos : Z) :=
 (b<>br \/ pos<0 \/ 40<=pos) /\ (b<>bm \/ pos<0 \/ 40<=pos).

Theorem eval_norm62_from_storage rho m br bm : br<>bm ->
 fe_at m br 0 (words5 rho) -> Mem.range_perm m br 0 40 Cur Freeable ->
 norm62_modulus_at m bm (fun i => rho (5+i)%nat) -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_normalize_62)
  [Vptr br Ptrofs.zero;Vlong (rho 10%nat);Vptr bm Ptrofs.zero] E0 mf Vundef /\
 fe_at mf br 0 (words5 (norm62_machine rho (fun i => rho (5+i)%nat) (rho 10%nat))) /\
 Mem.range_perm mf br 0 40 Cur Freeable /\
 norm62_modulus_at mf bm (fun i => rho (5+i)%nat) /\
 lframe (norm62_outside br bm) m mf.
Proof.
 intros NE Field Free Modulus.
 destruct (eval_norm62_symbolic rho [(br,0);(bm,0)] m
   (norm62_initial rho m br bm NE Field Free Modulus)) as (mf & Call & Out & Frame).
 pose proof (rep_region _ _ _ mf 0 _ Out eq_refl) as R0.
 pose proof (rep_region _ _ _ mf 1 _ Out eq_refl) as R1.
 pose proof R0 as (_ & _ & _ & _ & FreeR).
 pose proof (region_ok_revalue_u64 rho [(br,0);(bm,0)] mf 0 norm62_out true (Some 40)
   R0 eq_refl) as Output.
 rewrite (revalue_u64_machine_map _ _ _ _ (norm62_output_den rho [(br,0);(bm,0)])) in Output.
 pose proof (u64_region_fe_at _ _ _ _ _ _ Output) as FieldR.
 assert (Words : forall i, (i<5)%nat ->
   Mem.load Mint64 mf bm (8*Z.of_nat i) = Some (Vlong (rho (5+i)%nat))).
 { intros i I.
   assert (At : nth_error (vars5 5) i = Some (XLv (5+i)%nat)).
   { destruct i as [|[|[|[|[|i]]]]]; [reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|lia]. }
   exact (region_load rho [(br,0);(bm,0)] mf 1 _ (8*Z.of_nat i) Mint64 (XLv (5+i)%nat)
     R1 (u64_cells_nth (vars5 5) 0 i _ At)). }
 exists mf. split; [exact Call|]. split; [exact FieldR|]. split.
 - exact (proj1 (proj2 (proj2 FreeR))).
 - split.
   + split; [apply (norm62_words_readable mf bm (fun i=>rho (5+i)%nat) Words)|exact Words].
   + eapply lframe_implies; [exact Frame|].
     intros b pos Outside Valid Foot.
     destruct (norm62_foot br bm b pos Foot) as [(-> & Range)|(-> & Range)];
      unfold norm62_outside in Outside; destruct Outside as (A & B);
      destruct A as [A|[A|A]]; destruct B as [B|[B|B]]; congruence || lia.
Qed.
