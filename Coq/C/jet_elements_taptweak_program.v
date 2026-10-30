(** Actual CompCert AST and composite linking of the frozen Elements unit
    with selected crypto definitions. The typed artifact uses the exact linked
    AST and a directly checked composite environment. This avoids the extra
    proof-irrelevance axiom used by Ctypes.link_program's generic bridge.
    Execution transport is not yet proved. *)
From Coq Require Import List Bool ZArith.
From compcert Require Import AST Ctypes Clight Globalenvs Maps Errors Linking.
Require Import C.jets_elements C.jets_secp C.jet_elements_taptweak_link C.jet_elements_taptweak_import.
Import ListNotations Ctypes.
Set Default Timeout 10.
Local Transparent Linker_fundef Linker_def.
Lemma taptweak_filter_fold {A:Type} (keep:ident->bool) defs:
 forall (before after:PTree.t A),
 (forall id,after!id=if keep id then before!id else None) ->
 forall id,
 (fold_left (fun m entry=>PTree.set (fst entry) (snd entry) m)
 (filter (fun entry=>keep(fst entry)) defs) after)!id=
 if keep id then
 (fold_left (fun m entry=>PTree.set (fst entry) (snd entry) m) defs before)!id else None.
Proof.
 induction defs as [|[key val] rest IH];intros before after Agree id;[apply Agree|].
 cbn [filter fst snd fold_left].
 destruct (keep key) eqn:Kept.
 - apply IH;intro i;cbn [fst snd];rewrite !PTree.gsspec.
   destruct (Coqlib.peq i key);[subst i;rewrite Kept;reflexivity|apply Agree].
 - apply IH;intro i;cbn [fst snd];rewrite Agree,PTree.gsspec.
   destruct (Coqlib.peq i key);[subst i;rewrite Kept;reflexivity|reflexivity].
Qed.
Lemma taptweak_filter_defmap {A:Type} (defs:list(ident*A)) keep id:
 (PTree_Properties.of_list (filter (fun entry=>keep(fst entry)) defs))!id=
 if keep id then (PTree_Properties.of_list defs)!id else None.
Proof.
 unfold PTree_Properties.of_list;apply taptweak_filter_fold.
 intro i;rewrite !PTree.gempty;destruct (keep i);reflexivity.
Qed.

Definition taptweak_fragment_composites:=filter
 (fun cd=>existsb (Pos.eqb (name_composite_def cd))
 (taptweak_shared_composite_names++taptweak_crypto_composite_names)) jets_secp.composites.
Definition taptweak_fragment_composite_result:=build_composite_env taptweak_fragment_composites.
Lemma taptweak_fragment_composite_success:
 match taptweak_fragment_composite_result with OK _=>True|Error _=>False end.
Proof. vm_compute;exact I. Qed.
Definition taptweak_fragment_composite_env:composite_env:=
 match taptweak_fragment_composite_result with OK ce=>ce|Error _=>PTree.empty composite end.
Lemma taptweak_fragment_composite_env_correct:
 build_composite_env taptweak_fragment_composites=OK taptweak_fragment_composite_env.
Proof.
 unfold taptweak_fragment_composite_env.
 pose proof taptweak_fragment_composite_success as Success.
 unfold taptweak_fragment_composite_result in *.
 destruct (build_composite_env taptweak_fragment_composites);[reflexivity|contradiction].
Qed.
Definition taptweak_fragment_keep id:=Pos.eqb id jets_secp._simplicity_generic_taptweak ||
 match taptweak_host_defmap!id with None=>true|Some _=>false end.
Definition taptweak_fragment_definitions:=filter
 (fun entry=>taptweak_fragment_keep (fst entry)) taptweak_import_definitions.
Definition taptweak_fragment_public:=filter
 (fun id=>existsb (Pos.eqb id) (map fst taptweak_fragment_definitions)) jets_secp.public_idents.
Definition taptweak_fragment_program:Clight.program:={|
 prog_defs:=taptweak_fragment_definitions;
 prog_public:=taptweak_fragment_public;
 prog_main:=jets_elements._main;
 prog_types:=taptweak_fragment_composites;
 prog_comp_env:=taptweak_fragment_composite_env;
 prog_comp_env_eq:=taptweak_fragment_composite_env_correct|}.

Lemma taptweak_fragment_types_link:
 link_composite_defs jets_elements.composites taptweak_fragment_composites=
 Some elements_taptweak_linked_composites.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_globals_link_success:
 match Linking.link_prog (Ctypes.program_of_program jets_elements.prog)
 (Ctypes.program_of_program taptweak_fragment_program) with Some _=>True|None=>False end.
Proof. vm_compute;exact I. Qed.

Definition elements_taptweak_linked_ast:=
 match Linking.link_prog (Ctypes.program_of_program jets_elements.prog)
 (Ctypes.program_of_program taptweak_fragment_program) with
 |Some p=>p|None=>Ctypes.program_of_program jets_elements.prog end.
Lemma elements_taptweak_linked_ast_correct:
 Linking.link_prog (Ctypes.program_of_program jets_elements.prog)
 (Ctypes.program_of_program taptweak_fragment_program)=Some elements_taptweak_linked_ast.
Proof.
 pose proof elements_taptweak_globals_link_success as Success.
 unfold elements_taptweak_linked_ast.
 destruct (Linking.link_prog (Ctypes.program_of_program jets_elements.prog)
 (Ctypes.program_of_program taptweak_fragment_program));[reflexivity|contradiction].
Qed.
Definition taptweak_typed_program (a:AST.program Clight.fundef type)
 (types:list composite_definition) (ce:composite_env) (correct:build_composite_env types=OK ce):Clight.program:={|
 prog_defs:=AST.prog_defs a;prog_public:=AST.prog_public a;prog_main:=AST.prog_main a;
 prog_types:=types;prog_comp_env:=ce;prog_comp_env_eq:=correct|}.
Definition elements_taptweak_linked_program:=taptweak_typed_program elements_taptweak_linked_ast
 elements_taptweak_linked_composites elements_taptweak_composite_env elements_taptweak_composite_env_correct.
Lemma taptweak_typed_program_ast a types ce correct:
 Ctypes.program_of_program (taptweak_typed_program a types ce correct)=a.
Proof. destruct a;reflexivity. Qed.
Lemma elements_taptweak_program_ast_exact:
 Ctypes.program_of_program elements_taptweak_linked_program=elements_taptweak_linked_ast.
Proof. exact (taptweak_typed_program_ast _ _ _ _). Qed.
Lemma elements_taptweak_program_composites_exact:
 prog_types elements_taptweak_linked_program=elements_taptweak_linked_composites /\
 prog_comp_env elements_taptweak_linked_program=elements_taptweak_composite_env.
Proof. split;reflexivity. Qed.
Definition elements_taptweak_linked_defmap:=AST.prog_defmap elements_taptweak_linked_ast.
Lemma taptweak_ast_link_lookup (p q r:AST.program Clight.fundef type) id:
 Linking.link_prog p q=Some r ->
 (AST.prog_defmap r)!id=Linking.link_prog_merge ((AST.prog_defmap p)!id) ((AST.prog_defmap q)!id).
Proof.
 intro Linked;destruct (Linking.link_prog_inv _ _ _ Linked) as (_ & _ & Defs);subst r.
 rewrite Linking.prog_defmap_elements.
 apply PTree.gcombine;reflexivity.
Qed.

Definition taptweak_fragment_defmap:=AST.prog_defmap (Ctypes.program_of_program taptweak_fragment_program).
Lemma elements_taptweak_linked_lookup id:
 elements_taptweak_linked_defmap!id=Linking.link_prog_merge (taptweak_host_defmap!id) (taptweak_fragment_defmap!id).
Proof.
 exact (taptweak_ast_link_lookup _ _ _ id elements_taptweak_linked_ast_correct).
Qed.
Local Opaque elements_taptweak_linked_defmap.
Lemma elements_taptweak_generic_resolves:
 elements_taptweak_linked_defmap!jets_elements._simplicity_generic_taptweak=
 Some (Gfun (Internal jets_secp.f_simplicity_generic_taptweak)).
Proof.
 rewrite elements_taptweak_linked_lookup.
 vm_compute;reflexivity.
Qed.
Lemma elements_taptweak_wrapper_retained:
 elements_taptweak_linked_defmap!jets_elements._simplicity_build_taptweak=
 Some (Gfun (Internal jets_elements.f_simplicity_build_taptweak)).
Proof.
 rewrite elements_taptweak_linked_lookup.
 vm_compute;reflexivity.
Qed.
Lemma elements_taptweak_tag_retained:
 elements_taptweak_linked_defmap!jets_elements._taptweak=Some (Gvar jets_elements.v_taptweak).
Proof.
 rewrite elements_taptweak_linked_lookup.
 vm_compute;reflexivity.
Qed.

Lemma taptweak_source_generic:
 taptweak_source_defmap!jets_secp._simplicity_generic_taptweak=
 Some (Gfun (Internal jets_secp.f_simplicity_generic_taptweak)).
Proof. vm_compute;reflexivity. Qed.
Local Opaque jets_secp.global_definitions taptweak_import_names taptweak_host_defmap taptweak_source_defmap.
Lemma taptweak_fragment_lookup id:
 taptweak_fragment_defmap!id=
 if taptweak_fragment_keep id then
 if existsb (Pos.eqb id) taptweak_import_names then taptweak_source_defmap!id else None
 else None.
Proof.
 eapply eq_trans.
 - exact (taptweak_filter_defmap taptweak_import_definitions taptweak_fragment_keep id).
 - destruct (taptweak_fragment_keep id);[|reflexivity].
   exact (taptweak_filter_defmap jets_secp.global_definitions
    (fun id=>existsb (Pos.eqb id) taptweak_import_names) id).
Qed.
Lemma elements_taptweak_host_preserved id gd:
 id<>jets_secp._simplicity_generic_taptweak ->
 taptweak_host_defmap!id=Some gd ->elements_taptweak_linked_defmap!id=Some gd.
Proof.
 intros Other Host;rewrite elements_taptweak_linked_lookup,taptweak_fragment_lookup.
 unfold taptweak_fragment_keep;rewrite Host.
 apply Pos.eqb_neq in Other;rewrite Other;reflexivity.
Qed.
Lemma elements_taptweak_import_preserved id:
 In id taptweak_import_names ->
 elements_taptweak_linked_defmap!id=taptweak_source_defmap!id.
Proof.
 intro Member.
 destruct (Pos.eq_dec id jets_secp._simplicity_generic_taptweak) as [Root|Other].
 - subst id;exact (eq_trans elements_taptweak_generic_resolves (eq_sym taptweak_source_generic)).
 - rewrite elements_taptweak_linked_lookup,taptweak_fragment_lookup.
   assert (Present:existsb (Pos.eqb id) taptweak_import_names=true).
   { apply existsb_exists;exists id;split;[exact Member|apply Pos.eqb_refl]. }
   unfold taptweak_fragment_keep;rewrite Present.
   apply Pos.eqb_neq in Other;rewrite Other;cbn [orb].
   destruct (taptweak_host_defmap!id) as [gd|] eqn:Host;[|reflexivity].
   assert (Common:In id taptweak_common_import_names).
   { unfold taptweak_common_import_names;apply filter_In;split;[exact Member|].
     rewrite Other,Host;reflexivity. }
   pose proof (taptweak_common_definition_identical id Common) as Same.
   rewrite Host in Same;exact (eq_sym Same).
Qed.

Lemma taptweak_fragment_definition_source entry:
 In entry taptweak_fragment_definitions ->In entry jets_secp.global_definitions.
Proof.
 intro Member;exact (taptweak_import_definition_source entry
 (proj1 (proj1 (@filter_In _ (fun entry=>taptweak_fragment_keep(fst entry))
 entry taptweak_import_definitions) Member))).
Qed.
Local Opaque jets_secp.composites.
Lemma taptweak_fragment_composite_source cd:
 In cd taptweak_fragment_composites ->In cd jets_secp.composites.
Proof.
 intro Member;exact (proj1 (proj1 (@filter_In _
 (fun cd=>existsb (Pos.eqb (name_composite_def cd))
 (taptweak_shared_composite_names++taptweak_crypto_composite_names)) cd jets_secp.composites) Member)).
Qed.
Lemma elements_taptweak_named_references_closed id:
 In id taptweak_import_names ->
 exists gd,elements_taptweak_linked_defmap!id=Some gd /\
 forall ref,In ref (taptweak_definition_references gd) ->In ref taptweak_import_names.
Proof.
 intro Member;destruct (taptweak_named_imports_closed id Member) as (gd & Found & Refs).
 exists gd;split;[exact (eq_trans (elements_taptweak_import_preserved id Member) Found)|exact Refs].
Qed.
