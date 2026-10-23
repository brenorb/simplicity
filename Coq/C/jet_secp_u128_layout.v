(** Cache the original secp composite lookup once, without changing its layout. *)
From Coq Require Import List.
From compcert Require Import AST Ctypes Clight Clightdefs Maps Integers.
Require Import C.jet_secp_linkage C.jets_secp.
Import ListNotations.
Set Default Timeout 10.
Lemma secp_u128_composite_fields :
  exists co,
    (genv_cenv secp_ge)!jets_secp._secp256k1_uint128 = Some co /\
    co_su co = Struct /\
    co_members co = [Member_plain jets_secp._lo tulong; Member_plain jets_secp._hi tulong].
Proof.
  (* Compute just the relevant metadata, not the dependent consistency
     certificate stored in the generated composite record. *)
  assert (View : option_map (fun co => (co_su co, co_members co))
    ((genv_cenv secp_ge)!jets_secp._secp256k1_uint128) =
    Some (Struct, [Member_plain jets_secp._lo tulong; Member_plain jets_secp._hi tulong])).
  { vm_compute; reflexivity. }
  destruct ((genv_cenv secp_ge)!jets_secp._secp256k1_uint128) as [co|] eqn:Lookup;
    [|discriminate].
  exists co; split; [reflexivity|].
  cbn [option_map] in View; inversion View; split; reflexivity.
Qed.
