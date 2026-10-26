(** Original weak normalization at an arbitrary field slice. Reuse the
    existing carry-pass evaluation and numeric lemmas, retaining caller owners. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep C.jet_sx_pure
 C.jet_sx_zval C.jet_sx_zrep C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv
 C.jet_secp_field_add_initial C.jet_secp_field_weak_loose C.jet_secp_field_weak_tight
 C.jet_secp_curve_weak C.jet_secp_curve_weak_math C.jet_secp_fe_math C.jet_secp_field_mul_small
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_double_coordinate_numeric C.jet_secp_slice_permissions C.jet_clight_internal_permissions
 C.jet_secp_closed_helpers C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition field_slice_weak_regs := [fe_reg (vars5 1)].
Definition field_slice_weak_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160
 f_secp256k1_fe_normalize_weak [XP 0 0] field_slice_weak_regs [] 6.
Definition field_slice_weak_tree := Eval vm_compute in field_slice_weak_run.
Definition field_slice_weak_state := match field_slice_weak_tree with
 | Some (RDone st _) => st | _=>mkst (PTree.empty sx) [] [] 0 end.
Lemma field_slice_weak_run_eq : field_slice_weak_run=Some (RDone field_slice_weak_state ONormal).
Proof. reflexivity. Qed.
Lemma field_slice_weak_return : (stemps field_slice_weak_state)!1%positive=None.
Proof. reflexivity. Qed.
Lemma field_slice_weak_log_nil : leaves_log_nil (RDone field_slice_weak_state ONormal)=true.
Proof. reflexivity. Qed.
Lemma field_slice_weak_region : nth_error (sregs field_slice_weak_state) 0=
 Some (mkreg (cells0 curve_weak_state) true None).
Proof. reflexivity. Qed.
Local Opaque field_slice_weak_state.

Theorem eval_field_slice_weak_symbolic rho beta m : rep rho beta field_slice_weak_regs m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0))] E0 mf Vundef /\
 rep rho beta (sregs field_slice_weak_state) mf /\
 lframe (fun b pos=>~foot beta (map rshape field_slice_weak_regs) b pos) m mf.
Proof.
 intro Initial.
 destruct (xfun_pure secp_ge secp_pure secp_pure_ok 160 f_secp256k1_fe_normalize_weak
   [XP 0 0] field_slice_weak_regs 6 _ field_slice_weak_run_eq field_slice_weak_log_nil rho beta m Initial)
  as (mf & result & Call & Rep & Ret & Shape & Frame).
 cbn [rsel fst] in Rep,Ret;rewrite field_slice_weak_return in Ret;subst result.
 change (map (den rho (lay beta)) [XP 0 0]) with [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+0))] in Call.
 rewrite Z.add_0_r in Call;exists mf;split;[exact Call|];split;assumption.
Qed.

Lemma field_slice_weak_foot beta bx pos : foot beta (map rshape field_slice_weak_regs) bx pos ->
 bx=blk beta 0 /\ bas beta 0<=pos<bas beta 0+40.
Proof.
 intros (r & sh & d & ch & Nth & Cell & Block & Range).
 destruct r as [|r];[|destruct r;discriminate Nth].
 cbn [field_slice_weak_regs map nth_error rshape rcells rw rfree] in Nth;injection Nth as <-.
 split;[exact Block|].
 cbn [fe_reg rshape rcells rw rfree fst map cshape cofs cchunk u64_cells vars5 In] in Cell;
  repeat match type of Cell with _ \/ _=>destruct Cell as [Cell|Cell] end;
  try contradiction;inversion Cell;subst d ch;change (size_chunk Mint64) with 8 in Range;lia.
Qed.

Theorem eval_field_slice_weak w m b base :
 (forall i,(i<5)%nat -> Int64.unsigned (w i)<=2^60) -> fe_at m b base (words5 w) -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
  [Vptr b (Ptrofs.repr base)] E0 mf Vundef /\
 fe_at mf b base (words5 (weak_loose_words w)) /\
 radix_value (weak_loose_words w) mod feP=radix_value w mod feP /\
 square_input_bounds (weak_loose_words w) /\ keeps_permissions m mf /\
 lframe (fun bx pos=>bx<>b \/ pos<base \/ base+40<=pos) m mf /\ readonly_preserved m mf.
Proof.
 intros Bound Field.
 assert (Shift:forall n,(1<=n<=5)%nat -> Int64.unsigned (weak_shift_words w n)<=2^60).
 { intros [|i] Range;[lia|cbn [weak_shift_words];apply Bound;lia]. }
 assert (Initial:rep (weak_shift_words w) [(b,base)] field_slice_weak_regs m).
 { apply (rep_add _ [] [] m b base);[apply rep_nil|cbn;tauto|].
   apply field_region_from_values;rewrite weak_shift_values;exact Field. }
 destruct (eval_field_slice_weak_symbolic (weak_shift_words w) [(b,base)] m Initial)
  as (mf & Call & Rep & Frame).
 pose proof (rep_region _ _ _ mf 0 _ Rep field_slice_weak_region) as Region.
 destruct Region as (_ & _ & _ & Cells & _).
 change (Forall (cell_ok (weak_shift_words w) [(b,base)] mf 0 true) (cells0 curve_weak_state)) in Cells.
 destruct (zreg_load (weak_shift_words w) curve_weak_bounds [(b,base)]
   (curve_weak_bounds_holds _ Shift) mf 0 true (cells0 curve_weak_state) 0 curve_weak_cells_checked Cells)
  as [Loads _].
 rewrite curve_weak_cells_values in Loads.
 change (forall i z,nth_error (curve_weak_math_list (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
   (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat))) i=Some z ->
   Mem.load Mint64 mf b (base+(0+8*Z.of_nat i))=Some (Vlong (Int64.repr z))) in Loads.
 assert (Keep:keeps_permissions m mf) by
  (eapply (secp_internal_keeps_permissions f_secp256k1_fe_normalize_weak);[reflexivity|reflexivity|exact Call]).
 destruct (weak_loose_numeric w Bound) as [Numeric Tight].
 exists mf;split;[exact Call|];split.
 - destruct Field as (Base & Align & Max & Space & OldLoads).
   split;[exact Base|];split;[exact Align|];split;[exact Max|];split.
   + eapply keeps_range_permissions;[exact Keep|exact Space].
   + rewrite weak_loose_words_list;intros i v Nth;rewrite nth_error_map in Nth.
     destruct (nth_error _ i) as [z|] eqn:NthZ;[|discriminate];injection Nth as <-.
     rewrite <-Z.add_0_l at 1;apply Loads;exact NthZ.
 - split;[exact Numeric|];split;[apply double_tight_loose;exact Tight|];split;[exact Keep|];split.
   + eapply lframe_implies;[exact Frame|];intros bx pos Outside Valid Foot.
     destruct (field_slice_weak_foot [(b,base)] bx pos Foot) as [Same Range].
     cbn [blk bas lay nth fst snd] in Same,Range;subst bx;destruct Outside;intuition lia.
   + eapply (secp_closed_function_preserved f_secp256k1_fe_normalize_weak);[reflexivity|reflexivity|exact Call].
Qed.
