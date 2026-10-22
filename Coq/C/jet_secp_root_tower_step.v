(** Routing of the fixed tower, in the same stage order as the C helper. *)
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_square_execution C.jet_secp_negate_literal_contract
 C.jet_secp_rescale_literal C.jet_secp_root_literal.
Set Default Timeout 10.
Local Opaque literal_fe_square literal_fe_multiply literal_fe_squares.
Local Notation sq := (@literal_fe_square Alg.CoreFunSem).
Local Notation mul := (@literal_fe_multiply Alg.CoreFunSem).
Local Notation squares n := (@literal_fe_squares n Alg.CoreFunSem).

Lemma literal_fe_tower_step (x : Ty.tySem (Word 8)) :
 let x2 := mul (x,sq x) in
 let x3 := mul (x,sq x2) in
 let x6 := mul (x3,sq (sq (sq x3))) in
 let x9 := mul (x3,sq (sq (sq x6))) in
 let x11 := mul (x2,sq (sq x9)) in
 let x22 := mul (x11,squares 11 x11) in
 let x44 := mul (x22,squares 22 x22) in
 let x88 := mul (x44,squares 44 x44) in
 let x176 := mul (x88,squares 88 x88) in
 let x220 := mul (x44,squares 44 x176) in
 let x223 := mul (x3,sq (sq (sq x220))) in
 let t1 := mul (x22,squares 23 x223) in
 @literal_fe_tower Alg.CoreFunSem x=(x2,squares 5 t1).
Proof. reflexivity. Qed.
