(** Actual original fe_half, with exact five machine-word results.  Numeric
    field-halving under derived bounds is a separate caller obligation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_sx_revalue_cells C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
  C.jet_secp_local_regions C.jet_secp_field_add_initial C.jet_secp_owned_slice_fields
  C.jet_secp_multiply_normalize_bridge C.jet_secp_curve_frame.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition half_regs := [free_region (fe_reg (vars5 0)) 40].
Definition half_one := XI2L Signed (XIc (Int.repr 1)).
Definition half_mask_expr := XLsh Hshru (XLneg (XLb Band (XLv 0) half_one)) 12.
Definition half_adjust_expr i := XLb Badd (XLv i)
  (if Nat.eqb i 0 then XLb Band (XLc (Int64.repr 4503595332402223)) half_mask_expr
   else if Nat.eqb i 4 then XLsh Hshru half_mask_expr 4 else half_mask_expr).
Definition half_out_expr i := if Nat.eqb i 4 then XLsh Hshru (half_adjust_expr i) 1
  else XLb Badd (XLsh Hshru (half_adjust_expr i) 1)
    (XLsh Hshl (XLb Band (half_adjust_expr (S i)) half_one) 51).
Definition half_out := map half_out_expr [0;1;2;3;4]%nat.
Definition half_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 96
  f_secp256k1_fe_half [XP 0 0] half_regs [] 5.
Definition half_tree := Eval vm_compute in half_run.
Definition half_state := match half_tree with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.

Definition half_mask (w : nat -> int64) :=
  Int64.shru (Int64.neg (Int64.and (w 0%nat) Int64.one)) (Int64.repr 12).
Definition half_adjust_words (w : nat -> int64) (i : nat) := Int64.add (w i)
  (if Nat.eqb i 0 then Int64.and (Int64.repr 4503595332402223) (half_mask w)
   else if Nat.eqb i 4 then Int64.shru (half_mask w) (Int64.repr 4) else half_mask w).
Definition half_words (w : nat -> int64) (i : nat) :=
  if Nat.eqb i 4 then Int64.shru (half_adjust_words w i) (Int64.repr 1)
  else Int64.add (Int64.shru (half_adjust_words w i) (Int64.repr 1))
    (Int64.shl (Int64.and (half_adjust_words w (S i)) Int64.one) (Int64.repr 51)).

Lemma half_run_eq : half_run=Some (RDone half_state ONormal).
Proof. vm_compute;reflexivity. Qed.
Lemma half_return : (stemps half_state)!1%positive=None.
Proof. reflexivity. Qed.
Lemma half_output_shape : sregs half_state=[mkreg (u64_cells 0 half_out) true (Some 40)].
Proof. reflexivity. Qed.
Lemma half_output_den rho beta : map (den rho (lay beta)) half_out=map Vlong (words5 (half_words rho)).
Proof. reflexivity. Qed.

Theorem eval_field_half_symbolic rho beta m : rep rho beta half_regs m ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_half)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0))] E0 mf Vundef /\
  rep rho beta [mkreg (u64_cells 0 half_out) true (Some 40)] mf /\
  lframe (fun b pos => ~foot beta (map rshape half_regs) b pos) m mf.
Proof.
  intro HR;destruct (xfun_pure secp_ge secp_pure secp_pure_ok 96 f_secp256k1_fe_half
    [XP 0 0] half_regs 5 _ half_run_eq eq_refl rho beta m HR)
    as (mf & result & HC & HP & HV & HS & HF).
  cbn [rsel fst] in HP,HV;rewrite half_return in HV;subst result.
  change (map (den rho (lay beta)) [XP 0 0]) with
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0))] in HC;rewrite Z.add_0_r in HC.
  rewrite half_output_shape in HP.
  exists mf;split;[exact HC|];split;assumption.
Qed.

Lemma half_initial rho m b :
  fe_at m b 0 (words5 rho) -> Mem.range_perm m b 0 40 Cur Freeable -> rep rho [(b,0)] half_regs m.
Proof.
  intros HI HF;apply (rep_add rho [] [] m b 0);[apply rep_nil|cbn;tauto|].
  apply region_with_freeable.
  - apply field_region_from_values;exact HI.
  - reflexivity.
  - reflexivity.
  - exact HF.
  - apply field_region_storage_size.
Qed.

Lemma half_result rho beta m :
  rep rho beta [mkreg (u64_cells 0 half_out) true (Some 40)] m ->
  fe_at m (blk beta 0) (bas beta 0) (words5 (half_words rho)) /\
  Mem.range_perm m (blk beta 0) 0 40 Cur Freeable.
Proof.
  intro HR;pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HF & _).
  pose proof (region_ok_revalue_u64 rho beta m 0 half_out true (Some 40) H0 eq_refl) as HV.
  rewrite (revalue_u64_machine_map _ _ _ _ (half_output_den rho beta)) in HV.
  split;[exact (u64_region_fe_at _ _ _ _ _ _ HV)|exact HF].
Qed.

Theorem eval_field_half_from_storage rho m b :
  fe_at m b 0 (words5 rho) -> Mem.range_perm m b 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_half) [Vptr b Ptrofs.zero] E0 mf Vundef /\
  fe_at mf b 0 (words5 (half_words rho)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
  lframe (fun bx _ => bx<>b) m mf.
Proof.
  intros HI HF;destruct (eval_field_half_symbolic rho [(b,0)] m (half_initial rho m b HI HF))
    as (mf & HC & HP & HL).
  destruct (half_result rho [(b,0)] mf HP) as [FO FF].
  exists mf;split;[exact HC|]. split;[exact FO|]. split;[exact FF|].
  exact (curve_frame_one half_regs b m mf eq_refl HL).
Qed.
