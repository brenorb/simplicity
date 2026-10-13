(** Recover a typed output region from small metadata checks, without reducing
    its potentially large symbolic value expressions. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_secp_frame.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Fixpoint initialized_u64_cells (ofs : Z) (cs : list cell) : bool :=
  match cs with
  | [] => true
  | mkcell d Mint64 (Some _) :: tail => Z.eqb d ofs && initialized_u64_cells (ofs + 8) tail
  | _ => false
  end.
Lemma initialized_u64_rebuild cs : forall ofs,
  initialized_u64_cells ofs cs = true -> u64_cells ofs (map cell_sx cs) = cs.
Proof.
  induction cs as [|[d ch v] tail IH]; intros ofs H; [reflexivity|].
  destruct ch; cbn [initialized_u64_cells] in H; try discriminate.
  destruct v as [x|]; [|discriminate].
  apply Bool.andb_true_iff in H; destruct H as [Hd Htail].
  apply Z.eqb_eq in Hd; subst d.
  cbn [map cell_sx u64_cells]; rewrite (IH _ Htail); reflexivity.
Qed.
Lemma two_owned_u64_rebuild regs src sz :
  length regs = 2%nat -> nth_error regs 1 = Some src ->
  rw (hd (mkreg [] false None) regs) = true ->
  rfree (hd (mkreg [] false None) regs) = Some sz ->
  initialized_u64_cells 0 (rcells (hd (mkreg [] false None) regs)) = true ->
  regs = [mkreg (u64_cells 0 (map cell_sx (rcells (hd (mkreg [] false None) regs)))) true (Some sz); src].
Proof.
  intros Hlen Hsrc Hw Hsz Hcells.
  destruct regs as [|r0 [|r1 [|r2 tail]]]; cbn [length] in Hlen; try lia.
  cbn [nth_error] in Hsrc; injection Hsrc as Hsrc; subst src.
  destruct r0 as [cs w free]. cbn [hd rw rfree rcells] in Hw,Hsz,Hcells |- *.
  subst w free; rewrite (initialized_u64_rebuild cs 0 Hcells); reflexivity.
Qed.
