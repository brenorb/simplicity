(** Reuse the checked set_b32 arithmetic for both halves of the actual
    generator loader; byte inputs are unrestricted within 0..255. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_rename C.jet_sx_zval C.jet_sx_zrep
  C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_fe_math C.jet_secp_b32_exec C.jet_secp_generator_load.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma generator_zreg_den rho bnd beta cs :
  (forall n,fst (bnd n)<=Int64.unsigned (rho n)<=snd (bnd n)) -> forall ofs,
  zreg_okb bnd ofs cs=true ->
  map (fun c=>den rho beta (match cval c with Some x=>x | None=>XL Int64.zero end)) cs=
    map (fun z=>Vlong (Int64.repr z)) (zcells (zrho rho) cs).
Proof.
  intros Bounds;induction cs as [|c cs IH];intros ofs Checked;[reflexivity|].
  cbn [zreg_okb] in Checked;apply andb_true_iff in Checked;destruct Checked as [Head Tail].
  apply andb_true_iff in Head;destruct Head as [Shape Value].
  destruct (cval c) as [x|] eqn:CV;[|discriminate Value].
  apply andb_true_iff in Value;destruct Value as [Kind Numeric].
  destruct (zb bnd x) as [[lo hi]|] eqn:ZN;[|discriminate Numeric].
  cbn [map zcells];rewrite CV;cbn.
  rewrite (proj1 (den_zval_long rho bnd beta Bounds x lo hi ZN Kind)).
  f_equal;eapply IH;exact Tail.
Qed.
Lemma generator_field_den bytes beta : length bytes=32%nat ->
  Forall (fun x=>0<=x<=255) bytes ->
  map (den (byte_rho bytes) (lay beta)) generator_field_exprs=
    map Vlong (map Int64.repr (fe_limbs_of (be_val bytes))).
Proof.
  intros Len Bounds;unfold generator_field_exprs;rewrite map_map.
  rewrite (generator_zreg_den (byte_rho bytes) byte_bnd (lay beta) (cells0 sb_leaf)
    (byte_rho_bound bytes Bounds) 0 sb_output_checked).
  rewrite (proj1 (sb_output_numeric bytes Len Bounds)),map_map;reflexivity.
Qed.
Definition generator_byte_pair (xs ys:list Z) n :=
  if (n<?32)%nat then byte_rho xs n else byte_rho ys (n-32)%nat.
Lemma generator_pair_bound xs ys : Forall (fun x=>0<=x<=255) xs -> Forall (fun y=>0<=y<=255) ys ->
  forall n,fst (byte_bnd n)<=Int64.unsigned (generator_byte_pair xs ys n)<=snd (byte_bnd n).
Proof.
  intros X Y n;unfold generator_byte_pair;destruct (n<?32)%nat.
  - exact (byte_rho_bound xs X n).
  - exact (byte_rho_bound ys Y (n-32)%nat).
Qed.
Lemma generator_pair_left xs ys beta :
  map (den (generator_byte_pair xs ys) (lay beta)) generator_field_exprs=
    map (den (byte_rho xs) (lay beta)) generator_field_exprs.
Proof. reflexivity. Qed.
Lemma generator_pair_right xs ys beta :
  map (den (generator_byte_pair xs ys) (lay beta))
    (map (sx_rename (fun n=>(n+32)%nat)) generator_field_exprs)=
    map (den (byte_rho ys) (lay beta)) generator_field_exprs.
Proof. reflexivity. Qed.
Lemma generator_pair_as_bytes xs ys : length xs=32%nat -> forall n,
  generator_byte_pair xs ys n=byte_rho (xs++ys) n.
Proof.
  intros Len n;unfold generator_byte_pair,byte_rho;destruct (n<?32)%nat eqn:Less.
  - apply Nat.ltb_lt in Less;rewrite app_nth1 by lia;reflexivity.
  - apply Nat.ltb_ge in Less;rewrite app_nth2 by lia;rewrite Len;reflexivity.
Qed.
