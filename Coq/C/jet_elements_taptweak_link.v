(** Link-interface facts for the frozen Elements declaration and real generic C body.
    These are syntactic compatibility results, not an external-call assumption
    or a complete linked-program execution theorem. *)
From Coq Require Import ZArith List Strings.String.
From compcert Require Import Integers AST Ctypes Clight Clightdefs Globalenvs Maps Errors Linking.
Require Import C.jets_elements C.jets_secp C.jet_elements_linkage C.jet_secp_linkage
 C.jet_secp_taptweak_public_support.
Import ListNotations Ctypes.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope list_scope.
Set Default Timeout 10.
Definition elements_taptweak_declaration:Clight.fundef:=
 External (EF_external "simplicity_generic_taptweak"
 (mksignature [AST.Tlong;AST.Tlong;AST.Tlong;AST.Tlong] AST.Tint8unsigned cc_default))
 (Tcons (tptr (Tstruct jets_elements._frameItem noattr))
 (Tcons (tptr (Tstruct jets_elements._frameItem noattr))
 (Tcons (tptr tuchar) (Tcons tulong Tnil)))) tbool cc_default.
Lemma elements_taptweak_external_lookup:
 Genv.find_funct_ptr elements_ge (elements_symbol_block jets_elements._simplicity_generic_taptweak)=
 Some elements_taptweak_declaration.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_internal_lookup:
 Genv.find_funct_ptr secp_ge (secp_symbol_block jets_elements._simplicity_generic_taptweak)=
 Some (Internal jets_secp.f_simplicity_generic_taptweak).
Proof. exact taptweak_generic_function. Qed.
Lemma elements_taptweak_generic_type_compatible:
 Clight.type_of_fundef elements_taptweak_declaration=
 Clight.type_of_function jets_secp.f_simplicity_generic_taptweak.
Proof. reflexivity. Qed.
Lemma elements_taptweak_generic_signature:
 signature_of_type (type_of_params (fn_params jets_secp.f_simplicity_generic_taptweak))
 (fn_return jets_secp.f_simplicity_generic_taptweak) (fn_callconv jets_secp.f_simplicity_generic_taptweak)=
 mksignature [AST.Tlong;AST.Tlong;AST.Tlong;AST.Tlong] AST.Tint8unsigned cc_default.
Proof. reflexivity. Qed.
Lemma elements_taptweak_declaration_links:
 Ctypes.link_fundef elements_taptweak_declaration (Internal jets_secp.f_simplicity_generic_taptweak)=
 Some (Internal jets_secp.f_simplicity_generic_taptweak).
Proof. reflexivity. Qed.
Lemma elements_taptweak_declaration_links_reverse:
 Ctypes.link_fundef (Internal jets_secp.f_simplicity_generic_taptweak) elements_taptweak_declaration=
 Some (Internal jets_secp.f_simplicity_generic_taptweak).
Proof. reflexivity. Qed.
Definition taptweak_composite_layout (co:composite):=
 (co_su co,co_members co,co_attr co,co_sizeof co,co_alignof co,co_rank co).
Definition taptweak_shared_composite_names:=
 [jets_elements._bitstring;jets_elements._sha256_midstate;jets_elements._sha256_context;
 jets_elements._frameItem;jets_elements._secp256k1_uint128].
Lemma taptweak_shared_composites:
 map (fun id=>option_map taptweak_composite_layout ((genv_cenv elements_ge)!id)) taptweak_shared_composite_names=
 map (fun id=>option_map taptweak_composite_layout ((genv_cenv secp_ge)!id)) taptweak_shared_composite_names.
Proof. vm_compute;reflexivity. Qed.
Lemma taptweak_shared_composite id:In id taptweak_shared_composite_names ->
 option_map taptweak_composite_layout ((genv_cenv elements_ge)!id)=
 option_map taptweak_composite_layout ((genv_cenv secp_ge)!id).
Proof. apply (secp_map_eq_in _ _ _ taptweak_shared_composites). Qed.
Lemma elements_taptweak_frame_size:
 sizeof (genv_cenv elements_ge) (Tstruct jets_elements._frameItem noattr)=16 /\
 sizeof (genv_cenv secp_ge) (Tstruct jets_secp._frameItem noattr)=16 /\
 alignof (genv_cenv elements_ge) (Tstruct jets_elements._frameItem noattr)=8 /\
 alignof (genv_cenv secp_ge) (Tstruct jets_secp._frameItem noattr)=8.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma elements_taptweak_whole_composites_conflict:
 link_composite_defs jets_elements.composites jets_secp.composites=None.
Proof. vm_compute;reflexivity. Qed.
(** Import the actual crypto-only declarations, preserving the Elements types.
    This filters existing frozen declarations; no replacement layout is supplied. *)
Definition taptweak_crypto_composite_names:=
 [jets_secp.__2078;jets_secp.__5467;jets_secp.__5469;
 jets_secp._secp256k1_modinv64_signed62;jets_secp._secp256k1_modinv64_modinfo;
 jets_secp._secp256k1_modinv64_trans2x2;jets_secp.__5826;jets_secp.__6121;
 jets_secp.__6123;jets_secp.__6125;jets_secp._secp256k1_strauss_point_state;
 jets_secp._secp256k1_strauss_state;jets_secp.__6478;jets_secp.__6563].
Definition taptweak_crypto_composites:=filter
 (fun cd=>existsb (Pos.eqb (name_composite_def cd)) taptweak_crypto_composite_names) jets_secp.composites.
Lemma taptweak_crypto_composite_source cd:
 In cd taptweak_crypto_composites ->In cd jets_secp.composites.
Proof. intro Member;apply filter_In in Member;exact (proj1 Member). Qed.
Lemma taptweak_crypto_composite_names_exact:
 map name_composite_def taptweak_crypto_composites=taptweak_crypto_composite_names.
Proof. vm_compute;reflexivity. Qed.
Definition elements_taptweak_linked_composites:=jets_elements.composites++taptweak_crypto_composites.
Lemma elements_taptweak_composites_link:
 link_composite_defs jets_elements.composites taptweak_crypto_composites=Some elements_taptweak_linked_composites.
Proof. vm_compute;reflexivity. Qed.
Definition elements_taptweak_composite_result:=build_composite_env elements_taptweak_linked_composites.
Lemma elements_taptweak_composite_success:
 match elements_taptweak_composite_result with OK _=>True|Error _=>False end.
Proof. vm_compute;exact I. Qed.
Definition elements_taptweak_composite_env:composite_env:=
 match elements_taptweak_composite_result with OK ce=>ce|Error _=>PTree.empty composite end.
Lemma elements_taptweak_composite_env_correct:
 build_composite_env elements_taptweak_linked_composites=OK elements_taptweak_composite_env.
Proof.
 unfold elements_taptweak_composite_env.
 pose proof elements_taptweak_composite_success as Success.
 unfold elements_taptweak_composite_result in *.
 destruct (build_composite_env elements_taptweak_linked_composites);[reflexivity|contradiction].
Qed.
Lemma elements_taptweak_host_layouts_preserved:
 map (fun id=>option_map taptweak_composite_layout (elements_taptweak_composite_env!id))
 (map name_composite_def jets_elements.composites)=
 map (fun id=>option_map taptweak_composite_layout ((genv_cenv elements_ge)!id))
 (map name_composite_def jets_elements.composites).
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_crypto_layouts_preserved:
 map (fun id=>option_map taptweak_composite_layout (elements_taptweak_composite_env!id))
 (taptweak_shared_composite_names++taptweak_crypto_composite_names)=
 map (fun id=>option_map taptweak_composite_layout ((genv_cenv secp_ge)!id))
 (taptweak_shared_composite_names++taptweak_crypto_composite_names).
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_host_layout id:In id (map name_composite_def jets_elements.composites) ->
 option_map taptweak_composite_layout (elements_taptweak_composite_env!id)=
 option_map taptweak_composite_layout ((genv_cenv elements_ge)!id).
Proof. apply (secp_map_eq_in _ _ _ elements_taptweak_host_layouts_preserved). Qed.
Lemma elements_taptweak_crypto_layout id:In id (taptweak_shared_composite_names++taptweak_crypto_composite_names) ->
 option_map taptweak_composite_layout (elements_taptweak_composite_env!id)=
 option_map taptweak_composite_layout ((genv_cenv secp_ge)!id).
Proof. apply (secp_map_eq_in _ _ _ elements_taptweak_crypto_layouts_preserved). Qed.
