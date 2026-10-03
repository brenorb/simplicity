(** Checked old-composite preservation in the extended Bitcoin program.
    Layout transport applies only to complete old types, not the old undefined
    txEnv. These facts prepare helper execution transport, not public coverage. *)
From Coq Require Import ZArith List PArith.BinPos.
From compcert Require Import AST Ctypes Maps.
Require Import C.jets C.jets_bitcoin C.jet_bitcoin_linkage.
Import ListNotations Ctypes.
Set Default Timeout 10.

Definition bitcoin_core_composite_ids : list ident :=
  [jets._sha256_midstate; jets._sha256_context; jets._frameItem; jets._secp256k1_uint128].

Lemma bitcoin_core_composite_domain_checked :
  forallb (fun id => existsb (Pos.eqb id) bitcoin_core_composite_ids)
    (map fst (PTree.elements (prog_comp_env jets.prog))) = true.
Proof. vm_compute; reflexivity. Qed.

Lemma bitcoin_core_composite_lookups_checked :
  Forall (fun id => (Clight.genv_cenv bitcoin_ge)!id = (prog_comp_env jets.prog)!id)
    bitcoin_core_composite_ids.
Proof.
  unfold bitcoin_core_composite_ids.
  repeat (apply Forall_cons; [vm_compute; reflexivity|]).
  apply Forall_nil.
Qed.

Lemma bitcoin_composite_env_extends id co :
  (prog_comp_env jets.prog)!id = Some co ->
  (Clight.genv_cenv bitcoin_ge)!id = Some co.
Proof.
  intro HCo.
  pose proof (PTree.elements_correct _ _ HCo) as HI.
  assert (HId : In id (map fst (PTree.elements (prog_comp_env jets.prog)))).
  { apply in_map with (f := fst) in HI; exact HI. }
  pose proof bitcoin_core_composite_domain_checked as HD.
  apply forallb_forall with (x := id) in HD; [|exact HId].
  apply existsb_exists in HD as (other & HO & HE).
  apply Pos.eqb_eq in HE; subst other.
  pose proof bitcoin_core_composite_lookups_checked as HL.
  apply Forall_forall with (x := id) in HL; [|exact HO].
  rewrite HL; exact HCo.
Qed.

Lemma bitcoin_sizeof_complete_type ty :
  complete_type (prog_comp_env jets.prog) ty = true ->
  sizeof (Clight.genv_cenv bitcoin_ge) ty = sizeof (prog_comp_env jets.prog) ty.
Proof. apply sizeof_stable, bitcoin_composite_env_extends. Qed.

Lemma bitcoin_field_offset_complete_members field members :
  complete_members (prog_comp_env jets.prog) members = true ->
  field_offset (Clight.genv_cenv bitcoin_ge) field members =
    field_offset (prog_comp_env jets.prog) field members.
Proof. apply field_offset_stable, bitcoin_composite_env_extends. Qed.
