(** Named-reference slice of the real generic implementation.
    Dynamic function-pointer resolution and linked execution remain separate
    obligations; this slice follows expression references and data initializers. *)
From Coq Require Import List ZArith Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps.
Require Import C.jets_secp C.jets_elements C.jet_elements_taptweak_link C.jet_secp_linkage.
Import ListNotations Ctypes.
Set Default Timeout 10.
Fixpoint taptweak_expr_references (e:expr):list ident:=
 match e with
 |Evar id _=>[id]
 |Ederef a _|Eaddrof a _|Eunop _ a _|Ecast a _|Efield a _ _=>taptweak_expr_references a
 |Ebinop _ a b _=>taptweak_expr_references a++taptweak_expr_references b
 |_=>[] end.
Fixpoint taptweak_stmt_references (s:statement):list ident:=
 match s with
 |Sassign a b=>taptweak_expr_references a++taptweak_expr_references b
 |Sset _ a=>taptweak_expr_references a
 |Scall _ f args=>taptweak_expr_references f++flat_map taptweak_expr_references args
 |Sbuiltin _ _ _ args=>flat_map taptweak_expr_references args
 |Ssequence a b|Sloop a b=>taptweak_stmt_references a++taptweak_stmt_references b
 |Sifthenelse a b c=>taptweak_expr_references a++taptweak_stmt_references b++taptweak_stmt_references c
 |Sreturn (Some a)=>taptweak_expr_references a
 |Sswitch a labels=>taptweak_expr_references a++taptweak_label_references labels
 |Slabel _ a=>taptweak_stmt_references a
 |_=>[] end
with taptweak_label_references (labels:labeled_statements):list ident:=
 match labels with LSnil=>[]|LScons _ s rest=>taptweak_stmt_references s++taptweak_label_references rest end.
Definition taptweak_definition_references (gd:globdef Clight.fundef type):list ident:=
 match gd with
 |Gfun (Internal f)=>filter (fun id=>negb (existsb (Pos.eqb id) (map fst (fn_vars f))))
   (taptweak_stmt_references (fn_body f))
 |Gfun (External _ _ _ _)=>[]
 |Gvar v=>flat_map (fun init=>match init with Init_addrof id _=>[id]|_=>[] end) (gvar_init v)
 end.
Definition taptweak_source_defmap:=AST.prog_defmap (Ctypes.program_of_program jets_secp.prog).
Definition taptweak_host_defmap:=AST.prog_defmap (Ctypes.program_of_program jets_elements.prog).
Definition taptweak_references id:=
 match taptweak_source_defmap!id with Some gd=>taptweak_definition_references gd|None=>[] end.
Fixpoint taptweak_reference_walk (fuel:nat) (seen queue:list ident):list ident:=
 match fuel,queue with
 |O,_=>seen
 |S n,[]=>seen
 |S n,id::rest=>
   if existsb (Pos.eqb id) seen then taptweak_reference_walk n seen rest
   else taptweak_reference_walk n (id::seen) (taptweak_references id++rest)
 end.
Definition taptweak_import_names:=nodup Pos.eq_dec
 (taptweak_reference_walk 5000 [] [jets_secp._simplicity_generic_taptweak]).
Lemma taptweak_import_names_unique:NoDup taptweak_import_names.
Proof. apply NoDup_nodup. Qed.
Lemma taptweak_import_has_generic:
 existsb (Pos.eqb jets_secp._simplicity_generic_taptweak) taptweak_import_names=true.
Proof. vm_compute;reflexivity. Qed.
Lemma taptweak_named_imports_closedb:
 forallb (fun id=>match taptweak_source_defmap!id with
 |Some gd=>forallb (fun ref=>existsb (Pos.eqb ref) taptweak_import_names) (taptweak_definition_references gd)
 |None=>false end) taptweak_import_names=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque taptweak_import_names taptweak_source_defmap jets_secp.global_definitions.
Lemma taptweak_named_imports_closed id:In id taptweak_import_names ->
 exists gd,taptweak_source_defmap!id=Some gd /\
 forall ref,In ref (taptweak_definition_references gd) ->In ref taptweak_import_names.
Proof.
 intro Member;pose proof taptweak_named_imports_closedb as Closed.
 rewrite forallb_forall in Closed;specialize (Closed id Member).
 destruct (taptweak_source_defmap!id) as [gd|] eqn:Found;[|discriminate].
 exists gd;split;[reflexivity|].
 intros ref Used;rewrite forallb_forall in Closed;specialize (Closed ref Used).
 apply existsb_exists in Closed as (other & Present & Equal);apply Pos.eqb_eq in Equal;subst other;exact Present.
Qed.
Definition taptweak_import_definitions:=filter
 (fun entry=>existsb (Pos.eqb (fst entry)) taptweak_import_names) jets_secp.global_definitions.
Lemma taptweak_import_definition_source entry:
 In entry taptweak_import_definitions ->In entry jets_secp.global_definitions.
Proof.
 intro Member;exact (proj1 (proj1 (@filter_In _
 (fun pair=>existsb (Pos.eqb (fst pair)) taptweak_import_names) entry jets_secp.global_definitions) Member)).
Qed.
Local Transparent taptweak_import_names taptweak_source_defmap jets_secp.global_definitions.
Definition taptweak_common_import_names:=filter
 (fun id=>negb (Pos.eqb id jets_secp._simplicity_generic_taptweak) &&
 match taptweak_host_defmap!id with Some _=>true|None=>false end) taptweak_import_names.
Lemma taptweak_common_definitions_identical:
 map (fun id=>taptweak_source_defmap!id) taptweak_common_import_names=
 map (fun id=>taptweak_host_defmap!id) taptweak_common_import_names.
Proof. vm_compute;reflexivity. Qed.

Lemma taptweak_common_definition_identical id:
 In id taptweak_common_import_names ->
 taptweak_source_defmap!id=taptweak_host_defmap!id.
Proof. apply (secp_map_eq_in _ _ _ taptweak_common_definitions_identical). Qed.
(** The generic callee takes its tag from its caller. Its named dependency
    closure does not import the Bitcoin wrapper's private tag. *)
Lemma taptweak_bitcoin_tag_not_imported:
 existsb (Pos.eqb jets_secp._taptweak) taptweak_import_names=false.
Proof. vm_compute;reflexivity. Qed.
