(** Checked primality of the scalar order used by the original C global and
    literal Simplicity program. The two large certificate data records come
    from pinned CoqPrime's examples/russell2.v; its unchecked proof is NOT
    imported. Ordinary VM conversion checks these data and all support data. *)
From Coq Require Import ZArith ZArith.Znumtheory List.
From Coqprime Require Import PocklingtonCertificat.
Require Import C.jet_secp_canonical_scalar.
Import ListNotations.
Local Open Scope positive_scope.
Set Default Timeout 10.

Definition secp256k1_scalar_prime_certificate : singleCertif :=
 Pock_certif 115792089237316195423570985008687907852837564279074904382605163141518161494337
  5 [(174723607534414371449,1);(631,1);(149,1);(2,6)] 1122621917055392771987235982.
Definition secp256k1_scalar_prime_support : Certif :=
 [Pock_certif 174723607534414371449 3 [(4051,1);(59,1);(17,1);(2,3)] 53130590;
  Pock_certif 4051 10 [(2,1);(3,4);(5,2)] 1;
  Pock_certif 631 3 [(2,1);(3,2);(5,1);(7,1)] 1;
  Pock_certif 149 2 [(2,2);(37,1)] 1;
  Pock_certif 59 2 [(2,1);(29,1)] 1;
  Pock_certif 37 2 [(2,2);(3,2)] 1;
  Pock_certif 29 2 [(2,2);(7,1)] 1;
  Pock_certif 17 3 [(2,4)] 1;
  Pock_certif 7 3 [(2,1);(3,1)] 1;
  Pock_certif 5 2 [(2,2)] 1;
  Pock_certif 3 2 [(2,1)] 1;
  Proof_certif 2 prime_2].

Theorem secp256k1_scalar_prime : prime canonical_group_order.
Proof.
 change (prime (Zpos(nprim secp256k1_scalar_prime_certificate))).
 apply (Pocklington_refl secp256k1_scalar_prime_certificate secp256k1_scalar_prime_support).
 vm_compute;reflexivity.
Qed.
