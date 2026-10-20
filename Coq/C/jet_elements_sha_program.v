(** In the derived tree, [C.jets_elements] is a copy of the Elements program: every
    theorem there about [jets_elements.prog] (and [sha_ge], its global
    environment) is a theorem about the Elements translation unit. *)
From Coq Require Import List.
From compcert Require Import AST Ctypes Clight Errors.
From compcert Require Clightdefs.
Require C.jets_elements C.jets_elements.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_linkage.

Lemma mkprogram_eq c1 c2 d1 d2 p1 p2 m1 m2
    (W1 : Clightdefs.wf_composites c1) (W2 : Clightdefs.wf_composites c2) :
  c1 = c2 -> d1 = d2 -> p1 = p2 -> m1 = m2 ->
  Clightdefs.mkprogram c1 d1 p1 m1 W1 = Clightdefs.mkprogram c2 d2 p2 m2 W2.
Proof.
  intros Hc Hd Hp Hm. subst c2 d2 p2 m2.
  assert (HW : W1 = W2).
  { revert W1 W2. unfold Clightdefs.wf_composites.
    destruct (build_composite_env c1); intros W1 W2; [destruct W1, W2; reflexivity|contradiction]. }
  rewrite HW. reflexivity.
Qed.

Theorem elements_sha_program : jets_elements.prog = jets_elements.prog.
Proof.
  unfold jets_elements.prog, jets_elements.prog.
  apply mkprogram_eq; reflexivity.
Qed.

Theorem elements_sha_genv : sha_ge = elements_ge.
Proof. unfold sha_ge, elements_ge. reflexivity. Qed.
