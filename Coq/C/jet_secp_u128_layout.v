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
  eexists; split.
  - (* Closed lookup: materializing the dependent composite includes its
       environment consistency certificate, whose prior check exceeded 10s. *)
    Timeout 60 vm_compute; reflexivity.
  - split; reflexivity.
Set Default Timeout 60.
Qed.
Set Default Timeout 10.
