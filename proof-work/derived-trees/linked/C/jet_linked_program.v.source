(** The linked core program is CompCert's link of the accepted jets program
    with the concrete memcpy translation unit.

    [C.jets_unlinked] is the accepted generated program [Coq/C/jets.v]
    (unchanged, under another module name); [C.jets] is the linked program
    used by every proof of this tree.  CompCert's linker for Clight programs
    ([Ctypes.Linker_program]) succeeds on the accepted program and
    [memcpy_exact.prog], and its result has the same definition for every
    identifier, the same composite definitions, the same entry point and the
    same set of public identifiers as [C.jets.prog]. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Maps AST Linking Ctypes Clight.
Require C.jets_unlinked C.memcpy_exact C.jets.
Import ListNotations.
Set Default Timeout 600.

Definition unlinked_ast := program_of_program jets_unlinked.prog.
Definition memcpy_ast := program_of_program memcpy_exact.prog.
Definition linked_ast := program_of_program jets.prog.

Definition ast_link : option (AST.program Clight.fundef type) :=
  link unlinked_ast memcpy_ast.

Lemma ast_link_defs :
  option_map (fun p => AST.prog_defs p) ast_link =
    Some (PTree.elements (prog_defmap linked_ast)).
Proof. timeout 10 (vm_compute; reflexivity). Qed.

Lemma ast_link_main :
  option_map (fun p => AST.prog_main p) ast_link = Some (AST.prog_main linked_ast).
Proof. vm_compute. reflexivity. Qed.

Lemma ast_link_public :
  option_map (fun p => AST.prog_public p) ast_link =
    Some (AST.prog_public unlinked_ast ++ AST.prog_public memcpy_ast).
Proof. vm_compute. reflexivity. Qed.

Lemma memcpy_public_included :
  forallb (fun id => existsb (Pos.eqb id) (AST.prog_public unlinked_ast))
    (AST.prog_public memcpy_ast) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma unlinked_public : AST.prog_public unlinked_ast = AST.prog_public linked_ast.
Proof. vm_compute. reflexivity. Qed.

Lemma types_link :
  link (prog_types jets_unlinked.prog) (prog_types memcpy_exact.prog) =
    Some (prog_types jets.prog).
Proof. vm_compute. reflexivity. Qed.

(** Injectivity of [Some] as a lemma: the [injection] tactic would normalize
    the (large) definition lists. *)
Lemma some_inj {T : Type} (a b : T) : Some a = Some b -> a = b.
Proof. intros H. injection H as H. exact H. Qed.

Lemma linked_public_equiv id l :
  l = AST.prog_public unlinked_ast ++ AST.prog_public memcpy_ast ->
  (In id l <-> In id (AST.prog_public linked_ast)).
Proof.
  intros ->. rewrite unlinked_public.
  split; [|intros H; apply in_or_app; left; exact H].
  intros H. apply in_app_or in H. destruct H as [H|H]; [exact H|].
  pose proof memcpy_public_included as Hall. rewrite forallb_forall in Hall.
  specialize (Hall id H). apply existsb_exists in Hall.
  destruct Hall as [y [Hy Heq]]. apply Pos.eqb_eq in Heq. subst y.
  rewrite <- unlinked_public. exact Hy.
Qed.

(** Linking of the definitions (CompCert's generic program linker with the
    Clight function-definition and type linkers).  This statement uses no
    assumption at all. *)
Theorem linked_ast_is_compcert_link :
  exists pp,
    link unlinked_ast memcpy_ast = Some pp /\
    (forall id, (prog_defmap pp)!id = (prog_defmap linked_ast)!id) /\
    AST.prog_main pp = AST.prog_main linked_ast /\
    (forall id, In id (AST.prog_public pp) <-> In id (AST.prog_public linked_ast)).
Proof.
  pose proof ast_link_defs as Hdefs. pose proof ast_link_main as Hmain.
  pose proof ast_link_public as Hpub.
  unfold ast_link in Hdefs, Hmain, Hpub.
  destruct (link unlinked_ast memcpy_ast) as [pp|]; [|discriminate Hdefs].
  cbn [option_map] in Hdefs, Hmain, Hpub.
  apply some_inj in Hdefs. apply some_inj in Hmain. apply some_inj in Hpub.
  exists pp. split; [reflexivity|split; [|split; [exact Hmain|]]].
  - intros id.
    etransitivity; [|apply (PTree_Properties.of_list_elements (prog_defmap linked_ast) id)].
    apply (f_equal (fun l => (PTree_Properties.of_list l)!id)). exact Hdefs.
  - intros id. exact (linked_public_equiv id _ Hpub).
Qed.

(** The same for whole Clight programs, including composite definitions.
    CompCert's definition of [link_program] itself depends on its axiom
    [Axioms.proof_irr] (through [link_build_composite_env]), so this
    statement, and only this one, inherits that axiom from CompCert. *)
Lemma linked_program_is_link_program :
  exists p,
    link_program jets_unlinked.prog memcpy_exact.prog = Some p /\
    (forall id, (prog_defmap (program_of_program p))!id = (prog_defmap linked_ast)!id) /\
    prog_types p = prog_types jets.prog /\
    prog_main p = prog_main jets.prog /\
    (forall id, In id (prog_public p) <-> In id (prog_public jets.prog)).
Proof.
  pose proof ast_link_defs as Hdefs. pose proof ast_link_main as Hmain.
  pose proof ast_link_public as Hpub.
  unfold ast_link in Hdefs, Hmain, Hpub.
  unfold link_program.
  fold unlinked_ast memcpy_ast.
  destruct (link unlinked_ast memcpy_ast) as [pp|]; [|discriminate Hdefs].
  cbn [option_map] in Hdefs, Hmain, Hpub.
  apply some_inj in Hdefs. apply some_inj in Hmain. apply some_inj in Hpub.
  destruct (lift_option (link (prog_types jets_unlinked.prog) (prog_types memcpy_exact.prog)))
    as [[typs EQ]|EQ]; [|rewrite types_link in EQ; discriminate EQ].
  match goal with
  | |- context [link_build_composite_env ?a ?b ?c ?d ?e ?f ?g ?h] =>
      destruct (link_build_composite_env a b c d e f g h) as [env [P Q]]
  end.
  eexists. split; [reflexivity|].
  rewrite types_link in EQ. apply some_inj in EQ. subst typs.
  cbn [prog_types prog_main prog_public program_of_program].
  split; [|split; [reflexivity|split; [exact Hmain|]]].
  - intros id.
    change ((PTree_Properties.of_list (AST.prog_defs pp))!id = (prog_defmap linked_ast)!id).
    etransitivity; [|apply (PTree_Properties.of_list_elements (prog_defmap linked_ast) id)].
    apply (f_equal (fun l => (PTree_Properties.of_list l)!id)). exact Hdefs.
  - intros id. exact (linked_public_equiv id _ Hpub).
Qed.

Theorem linked_program_is_compcert_link :
  exists p,
    link jets_unlinked.prog memcpy_exact.prog = Some p /\
    (forall id, (prog_defmap (program_of_program p))!id = (prog_defmap linked_ast)!id) /\
    prog_types p = prog_types jets.prog /\
    prog_main p = prog_main jets.prog /\
    (forall id, In id (prog_public p) <-> In id (prog_public jets.prog)).
Proof. exact linked_program_is_link_program. Qed.
