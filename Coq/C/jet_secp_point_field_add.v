(** Original fe_add between a coordinate of an owned point and a private
    field, in either argument order.  Reuse the existing slice representation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_local_regions
  C.jet_secp_point_write_run C.jet_secp_point_mul_run C.jet_secp_point_mul_storage
  C.jet_secp_point_mul_preservation C.jet_secp_owned_slice_fields
  C.jet_secp_multiply_normalize_bridge C.jet_secp_field_add_scaled.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition point_add_args (point_dest : bool) k :=
  if point_dest then [XP 0 (point_coordinate_offset k);XP 1 0]
  else [XP 1 0;XP 0 (point_coordinate_offset k)].
Definition point_add_run d k := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 96
  f_secp256k1_fe_add (point_add_args d k) (point_mul_regs k) [] 10.
Definition point_add_tree := Eval vm_compute in fun d k => match d,k with
  | true,PointX => point_add_run true PointX | true,PointY => point_add_run true PointY
  | true,PointZ => point_add_run true PointZ | false,PointX => point_add_run false PointX
  | false,PointY => point_add_run false PointY | false,PointZ => point_add_run false PointZ end.
Definition point_add_state d k := match point_add_tree d k with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition point_add_sums (reverse : bool) := map (fun i =>
  if reverse then XLb Badd (XLv (5+i)%nat) (XLv i) else XLb Badd (XLv i) (XLv (5+i)%nat)) [0;1;2;3;4]%nat.
Definition point_add_point_exprs (d : bool) := if d then point_add_sums false else vars5 0.
Definition point_add_field_exprs (d : bool) := if d then vars5 5 else point_add_sums true.
Definition point_add_out_regs d k :=
  [mkreg (u64_cells (point_coordinate_offset k) (point_add_point_exprs d)) true (Some 128);
   mkreg (u64_cells 0 (point_add_field_exprs d)) true (Some 40)].
Definition point_add_point_words (d : bool) a b := if d then field_sum_words a b else a.
Definition point_add_field_words (d : bool) a b := if d then b else field_sum_words b a.
Definition point_add_frame k (bp bs bx : block) (pos : Z) :=
  bx<>bs /\ (bx<>bp \/ pos<point_coordinate_offset k \/ point_coordinate_offset k+40<=pos).

Lemma point_add_run_eq d k : point_add_run d k=Some (RDone (point_add_state d k) ONormal).
Proof. destruct d,k;reflexivity. Qed.
Lemma point_add_return d k : (stemps (point_add_state d k))!1%positive=None.
Proof. destruct d,k;reflexivity. Qed.
Lemma point_add_output_shape d k : sregs (point_add_state d k)=point_add_out_regs d k.
Proof. destruct d,k;reflexivity. Qed.
Lemma point_add_log_nil d k : leaves_log_nil (RDone (point_add_state d k) ONormal)=true.
Proof. destruct d,k;reflexivity. Qed.
Lemma point_add_point_den d a b beta :
  map (den (point_mul_valuation a b) (lay beta)) (point_add_point_exprs d)=
    map Vlong (words5 (point_add_point_words d a b)).
Proof. destruct d;reflexivity. Qed.
Lemma point_add_field_den d a b beta :
  map (den (point_mul_valuation a b) (lay beta)) (point_add_field_exprs d)=
    map Vlong (words5 (point_add_field_words d a b)).
Proof. destruct d;reflexivity. Qed.

Theorem eval_point_add_symbolic (d : bool) k rho beta m : rep rho beta (point_mul_regs k) m ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
    (if d then [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+point_coordinate_offset k));
                Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))]
     else [Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
           Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+point_coordinate_offset k))]) E0 mf Vundef /\
  rep rho beta (point_add_out_regs d k) mf /\
  lframe (fun b pos => ~foot beta (map rshape (point_mul_regs k)) b pos) m mf.
Proof.
  intro HR.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 96 f_secp256k1_fe_add
    (point_add_args d k) (point_mul_regs k) 10 _ (point_add_run_eq d k) (point_add_log_nil d k) rho beta m HR)
    as (mf & result & HC & HP & HV & HS & HL).
  cbn [rsel fst] in HP,HV;rewrite point_add_return in HV;subst result.
  rewrite point_add_output_shape in HP.
  exists mf;split.
  - destruct d.
    + change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
        [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+point_coordinate_offset k));
         Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0))] E0 mf Vundef) in HC.
      rewrite Z.add_0_r in HC;exact HC.
    + change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
        [Vptr (blk beta 1) (Ptrofs.repr (bas beta 1+0));
         Vptr (blk beta 0) (Ptrofs.repr (bas beta 0+point_coordinate_offset k))] E0 mf Vundef) in HC.
      rewrite Z.add_0_r in HC;exact HC.
  - split;assumption.
Qed.

Lemma point_add_fields d k a b m bp bs :
  rep (point_mul_valuation a b) [(bp,0);(bs,0)] (point_add_out_regs d k) m ->
  fe_at m bp (point_coordinate_offset k) (words5 (point_add_point_words d a b)) /\
  fe_at m bs 0 (words5 (point_add_field_words d a b)) /\
  Mem.range_perm m bp 0 128 Cur Freeable /\ Mem.range_perm m bs 0 40 Cur Freeable.
Proof.
  intro HR.
  pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof (rep_region _ _ _ m 1 _ HR eq_refl) as H1.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HF0 & _).
  pose proof H1 as (_ & _ & _ & _ & _ & _ & HF1 & _).
  split.
  - eapply owned_region_field_slice with
      (rho:=point_mul_valuation a b) (beta:=[(bp,0);(bs,0)]) (r:=0%nat) (size:=128)
      (cs:=u64_cells (point_coordinate_offset k) (point_add_point_exprs d))
      (exprs:=point_add_point_exprs d).
    + exact H0.
    + destruct k;cbn;lia.
    + destruct k;cbn;[exists 0|exists 5|exists 10];lia.
    + pose proof (point_coordinate_offset_bounds k);lia.
    + change (128<=18446744073709551615);lia.
    + destruct d;reflexivity.
    + reflexivity.
    + intros c HC;exact HC.
    + exact (point_add_point_den d a b [(bp,0);(bs,0)]).
  - split.
    + eapply owned_region_field_slice with
        (rho:=point_mul_valuation a b) (beta:=[(bp,0);(bs,0)]) (r:=1%nat) (size:=40)
        (cs:=u64_cells 0 (point_add_field_exprs d)) (exprs:=point_add_field_exprs d).
      * exact H1.
      * lia.
      * exists 0;lia.
      * lia.
      * change (40<=18446744073709551615);lia.
      * destruct d;reflexivity.
      * reflexivity.
      * intros c HC;exact HC.
      * exact (point_add_field_den d a b [(bp,0);(bs,0)]).
    + split;assumption.
Qed.

Theorem eval_point_field_add (d : bool) k a b m bp bs :
  bp<>bs -> fe_at m bp (point_coordinate_offset k) (words5 a) ->
  Mem.range_perm m bp 0 128 Cur Freeable ->
  fe_at m bs 0 (words5 b) -> Mem.range_perm m bs 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
    (if d then [Vptr bp (Ptrofs.repr (point_coordinate_offset k));Vptr bs Ptrofs.zero]
     else [Vptr bs Ptrofs.zero;Vptr bp (Ptrofs.repr (point_coordinate_offset k))]) E0 mf Vundef /\
  fe_at mf bp (point_coordinate_offset k) (words5 (point_add_point_words d a b)) /\
  fe_at mf bs 0 (words5 (point_add_field_words d a b)) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  lframe (point_add_frame k bp bs) m mf.
Proof.
  intros HNe HA HFA HB HFB.
  destruct (eval_point_add_symbolic d k (point_mul_valuation a b) [(bp,0);(bs,0)] m
    (point_mul_initial_from_storage k a b m bp bs HNe HA HFA HB HFB)) as (mf & HC & HP & HL).
  destruct (point_add_fields d k a b mf bp bs HP) as (FO & FI & FOF & FIF).
  exists mf;split;[exact HC|];split;[exact FO|];split;[exact FI|];
    split;[exact FOF|];split;[exact FIF|].
  eapply lframe_implies;[exact HL|]. intros bx pos [NS HP'] HV HFoot.
  destruct (point_mul_foot_bounds k bp bs bx pos HFoot) as [[HE HR]|HE];[|congruence].
  subst bx;destruct HP' as [HN|[HN|HN]];[contradiction|lia|lia].
Qed.
