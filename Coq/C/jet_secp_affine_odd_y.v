(** Actual fe_is_odd on affine Y, retaining the enclosing allocation and
    the exact source field for a possible subsequent magnitude-one negation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_affine_normalize_y C.jet_secp_point_mul_storage C.jet_secp_owned_slice_fields
 C.jet_secp_multiply_normalize_bridge C.jet_secp_local_regions C.jet_secp_canonical_odd.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition affine_odd_y_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 40
 f_secp256k1_fe_is_odd [XP 0 40] affine_nv_y_regs [] 5.
Definition affine_odd_y_tree := Eval vm_compute in affine_odd_y_run.
Definition affine_odd_y_state := match affine_odd_y_tree with Some (RDone st _) => st
 | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition affine_odd_y_ret := XL2I (XLb Band (XLv 0) (XI2L Signed (XIc Int.one))).
Lemma affine_odd_y_run_eq : affine_odd_y_run=Some (RDone affine_odd_y_state ONormal).
Proof. reflexivity. Qed.
Lemma affine_odd_y_return : (stemps affine_odd_y_state)!1%positive=Some affine_odd_y_ret.
Proof. reflexivity. Qed.
Lemma affine_odd_y_regions : sregs affine_odd_y_state=affine_nv_y_regs.
Proof. reflexivity. Qed.

Theorem eval_affine_odd_y_words w m b : fe_at m b 40 (words5 w) ->
 Mem.range_perm m b 0 88 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_odd)
  [Vptr b (Ptrofs.repr 40)] E0 mf
  (Vint (Int.repr (Int64.unsigned (Int64.and (w 0%nat) Int64.one)))) /\
 fe_at mf b 40 (words5 w) /\ Mem.range_perm mf b 0 88 Cur Freeable /\
 lframe (fun bx pos=>bx<>b \/ pos<40 \/ 80<=pos) m mf.
Proof.
 intros Field Free.
 assert (Initial : rep w [(b,0)] affine_nv_y_regs m).
 { apply (rep_add _ [] [] m b 0);[apply rep_nil|cbn;tauto|].
   apply owned_field_slice_region;[reflexivity|lia|lia|exact Field|exact Free]. }
 destruct (xfun_pure secp_ge secp_pure secp_pure_ok 40 f_secp256k1_fe_is_odd [XP 0 40]
  affine_nv_y_regs 5 _ affine_odd_y_run_eq eq_refl w [(b,0)] m Initial)
  as (mf & result & Call & Rep & Return & Shape & Frame).
 cbn [rsel fst] in Rep,Return;rewrite affine_odd_y_regions in Rep.
 rewrite affine_odd_y_return in Return.
 change (result=Vint (Int.repr (Int64.unsigned (Int64.and (w 0%nat) Int64.one)))) in Return;subst result.
 pose proof (rep_region _ _ _ _ 0 _ Rep eq_refl) as Region.
 pose proof Region as (_ & _ & _ & _ & _ & _ & Owned & _).
 exists mf;split;[exact Call|];split.
 - eapply owned_region_field_slice with (rho:=w) (beta:=[(b,0)]) (r:=0%nat) (size:=88) (exprs:=vars5 0).
   + exact Region.
   + lia.
   + exists 5;reflexivity.
   + lia.
   + change (88<=18446744073709551615);lia.
   + reflexivity.
   + reflexivity.
   + intros c HC;exact HC.
   + reflexivity.
 - split;[exact Owned|].
   eapply lframe_implies;[exact Frame|].
   intros bx pos Outside _ (r & sh & d & ch & NS & HC & HB & Range).
   destruct r;[|destruct r;discriminate NS].
   injection NS as <-;cbn [affine_nv_y_regs rshape fst snd rcells u64_cells vars5 map cshape In] in HC.
   repeat destruct HC as [HC|HC];try contradiction;injection HC as <- <-;
    cbn [bas blk lay nth fst snd size_chunk] in HB,Range;
    destruct Outside as [Outside|[Outside|Outside]];congruence || lia.
Qed.

Theorem eval_affine_odd_y_value m b value :
 fe_at m b 40 (map Int64.repr (fe_limbs_of value)) -> Mem.range_perm m b 0 88 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_odd)
  [Vptr b (Ptrofs.repr 40)] E0 mf (Vint (Int.repr (Z.b2z (Z.testbit value 0)))) /\
 fe_at mf b 40 (map Int64.repr (fe_limbs_of value)) /\ Mem.range_perm mf b 0 88 Cur Freeable /\
 lframe (fun bx pos=>bx<>b \/ pos<40 \/ 80<=pos) m mf.
Proof.
 intros Field Free.
 destruct (eval_affine_odd_y_words (fun n=>Int64.repr (nth n (fe_limbs_of value) 0)) m b Field Free)
  as (mf & Call & Out & Owned & Frame).
 change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_odd) [Vptr b (Ptrofs.repr 40)] E0 mf
  (Vint (Int.repr (Int64.unsigned (Int64.and (Int64.repr (value mod 2^52)) Int64.one))))) in Call.
 rewrite field_low_limb_odd_value in Call.
 exists mf;split;[exact Call|];split;[exact Out|];split;assumption.
Qed.
