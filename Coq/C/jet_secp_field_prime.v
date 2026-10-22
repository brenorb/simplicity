(** A checked Pocklington certificate for the fixed secp256k1 field modulus.
    Candidate factors are untrusted data: ordinary VM conversion checks every
    certificate equation, and the resulting proof is checked by the kernel. *)
From Coq Require Import ZArith ZArith.Znumtheory List Lia.
From Coqprime Require Import PocklingtonCertificat.
Require Import C.jet_secp_fe_math.
Import ListNotations.
Local Open Scope positive_scope.
Set Default Timeout 10.

Definition secp256k1_prime_certificate : singleCertif :=
 (Pock_certif 115792089237316195423570985008687907853269984665640564039457584007908834671663 3 [(2,1);(3,1);(7,1);(13441,1);(205115282021455665897114700593932402728804164701536103180137503955397371,1)] 1).
Definition secp256k1_prime_support : Certif :=
 [(Pock_certif 205115282021455665897114700593932402728804164701536103180137503955397371 10 [(2,1);(3,1);(5,1);(29,2);(31,1);(7723,1);(132896956044521568488119,1);(255515944373312847190720520512484175977,1)] 1);
  (Pock_certif 255515944373312847190720520512484175977 3 [(2,3);(7,2);(11,1);(1627,1);(2657,1);(4423,1);(96557,1);(41201,1);(107590001,1);(7240687,1)] 1);
  (Pock_certif 7240687 3 [(2,1);(3,1);(1206781,1)] 1);
  (Pock_certif 1206781 10 [(2,2);(3,1);(5,1);(20113,1)] 1);
  (Pock_certif 20113 10 [(2,4);(3,1);(419,1)] 1);
  (Pock_certif 419 2 [(2,1);(11,1);(19,1)] 1);
  (Pock_certif 19 2 [(2,1);(3,2)] 1);
  (Pock_certif 107590001 3 [(2,4);(5,4);(7,1);(29,1);(53,1)] 1);
  (Pock_certif 53 2 [(2,2);(13,1)] 1);
  (Pock_certif 41201 3 [(2,4);(5,2);(103,1)] 1);
  (Pock_certif 103 5 [(2,1);(3,1);(17,1)] 1);
  (Pock_certif 96557 2 [(2,2);(101,1);(239,1)] 1);
  (Pock_certif 239 7 [(2,1);(7,1);(17,1)] 1);
  (Pock_certif 101 2 [(2,2);(5,2)] 1);
  (Pock_certif 4423 3 [(2,1);(3,1);(11,1);(67,1)] 1);
  (Pock_certif 67 2 [(2,1);(3,1);(11,1)] 1);
  (Pock_certif 2657 3 [(2,5);(83,1)] 1);
  (Pock_certif 83 2 [(2,1);(41,1)] 1);
  (Pock_certif 41 6 [(2,3);(5,1)] 1);
  (Pock_certif 1627 3 [(2,1);(3,1);(271,1)] 1);
  (Pock_certif 271 6 [(2,1);(3,3);(5,1)] 1);
  (Pock_certif 132896956044521568488119 6 [(2,1);(3,1);(22149492674086928081353,1)] 1);
  (Pock_certif 22149492674086928081353 5 [(2,3);(3,1);(5323,1);(173378833005251801,1)] 1);
  (Pock_certif 173378833005251801 6 [(2,3);(5,2);(2621,1);(24809,1);(13331831,1)] 1);
  (Pock_certif 13331831 13 [(2,1);(5,1);(971,1);(1373,1)] 1);
  (Pock_certif 1373 2 [(2,2);(7,3)] 1);
  (Pock_certif 971 6 [(2,1);(5,1);(97,1)] 1);
  (Pock_certif 97 5 [(2,5);(3,1)] 1);
  (Pock_certif 24809 6 [(2,3);(7,1);(443,1)] 1);
  (Pock_certif 2621 2 [(2,2);(5,1);(131,1)] 1);
  (Pock_certif 131 2 [(2,1);(5,1);(13,1)] 1);
  (Pock_certif 5323 5 [(2,1);(3,1);(887,1)] 1);
  (Pock_certif 887 5 [(2,1);(443,1)] 1);
  (Pock_certif 443 2 [(2,1);(13,1);(17,1)] 1);
  (Pock_certif 17 3 [(2,4)] 1);
  (Pock_certif 7723 3 [(2,1);(3,3);(11,1);(13,1)] 1);
  (Pock_certif 13 2 [(2,2);(3,1)] 1);
  (Pock_certif 11 2 [(2,1);(5,1)] 1);
  (Pock_certif 31 3 [(2,1);(3,1);(5,1)] 1);
  (Pock_certif 29 2 [(2,2);(7,1)] 1);
  (Pock_certif 13441 11 [(2,7);(3,1);(5,1);(7,1)] 1);
  (Pock_certif 5 2 [(2,2)] 1);
  (Pock_certif 7 3 [(2,1);(3,1)] 1);
  (Pock_certif 3 2 [(2,1)] 1);
  (Proof_certif 2 prime_2)].

Theorem secp256k1_field_prime : prime feP.
Proof.
 change (prime (Zpos (nprim secp256k1_prime_certificate))).
 apply (Pocklington_refl secp256k1_prime_certificate secp256k1_prime_support).
 vm_compute;reflexivity.
Qed.
Local Open Scope Z_scope.

Lemma secp256k1_nonzero_product a b :
 a mod feP<>0 -> b mod feP<>0 -> (a*b) mod feP<>0.
Proof.
 intros HA HB HC.
 assert (HP : feP<>0) by (unfold feP,feR;lia).
 apply (proj1 (Z.mod_divide (a*b) feP HP)) in HC.
 destruct (prime_mult feP secp256k1_field_prime a b HC) as [HD|HD].
 - apply HA;apply (proj2 (Z.mod_divide a feP HP));exact HD.
 - apply HB;apply (proj2 (Z.mod_divide b feP HP));exact HD.
Qed.

Lemma secp256k1_nonzero_negative_product a b :
 a mod feP<>0 -> b mod feP<>0 -> (a*b*(feP-1)) mod feP<>0.
Proof.
 intros HA HB;apply secp256k1_nonzero_product.
 - apply secp256k1_nonzero_product;assumption.
 - rewrite Z.mod_small by (unfold feP,feR;lia).
   unfold feP,feR;lia.
Qed.
Print Assumptions secp256k1_nonzero_negative_product.
