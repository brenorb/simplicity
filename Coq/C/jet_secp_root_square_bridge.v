(** Original repeated-square execution against the exact repeated literal tree. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_square_numeric C.jet_secp_square_separate_numeric C.jet_secp_square_execution
 C.jet_secp_curve_statements C.jet_secp_double_coordinate_numeric
 C.jet_secp_root_literal C.jet_secp_root_square_loop.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words literal_fe_square.

Lemma literal_fe_squares_successor n (a : Ty.tySem (Word 8)) :
 @literal_fe_squares (S n) Alg.CoreFunSem a=
 @literal_fe_squares n Alg.CoreFunSem (@literal_fe_square Alg.CoreFunSem a).
Proof.
 destruct n as [|n].
 - change (@literal_fe_square Alg.CoreFunSem a=@literal_fe_square Alg.CoreFunSem a);reflexivity.
 - rewrite literal_fe_squares_comp.
   reflexivity.
Qed.

Theorem root_square_words_match n : forall w (a : Ty.tySem (Word 8)),
 square_input_bounds w -> radix_value w mod feP=@toZ (WordToZ 8) a mod feP ->
 square_input_bounds (root_square_words n w) /\
 radix_value (root_square_words n w) mod feP=@toZ (WordToZ 8) (@literal_fe_squares n Alg.CoreFunSem a) mod feP.
Proof.
 induction n as [|n IH];intros w a BW HW.
 - change (square_input_bounds w /\ radix_value w mod feP=@toZ (WordToZ 8) a mod feP);split;assumption.
 - cbn [root_square_words];rewrite literal_fe_squares_successor.
   apply IH;[apply square_result_reusable;exact BW|].
   apply double_match_mod;apply double_square_matches;assumption.
Qed.

Theorem exec_root_square_for_literal n id e le m b w (a : Ty.tySem (Word 8)) :
 Z.of_nat n<=88 -> e!id=Some (b,curve_fe_type) -> e!jets_secp._secp256k1_fe_sqr=None ->
 square_input_bounds w -> radix_value w mod feP=@toZ (WordToZ 8) a mod feP ->
 fe_at m b 0 (words5 w) -> Mem.range_perm m b 0 40 Cur Freeable ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m (root_square_for id (Z.of_nat n)) E0 lef mf Out_normal /\
 fe_at mf b 0 (words5 (root_square_words n w)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
 square_input_bounds (root_square_words n w) /\
 radix_value (root_square_words n w) mod feP=@toZ (WordToZ 8) (@literal_fe_squares n Alg.CoreFunSem a) mod feP /\
 lef!jets_secp._j=Some (Vint (Int.repr (Z.of_nat n))) /\
 (forall k, k<>jets_secp._j -> lef!k=le!k) /\ lframe (fun bx _=>bx<>b) m mf.
Proof.
 intros HN EL EG BW HW W F.
 destruct (exec_root_square_for_owned n id e le m b w HN EL EG BW W F)
   as (mf & lef & Loop & WF & FF & BF & JF & Temps & Frame).
 destruct (root_square_words_match n w a BW HW) as [BRes RRes].
 exists mf,lef;split;[exact Loop|];split;[exact WF|];split;[exact FF|];split;[exact BF|].
 split;[exact RRes|];split;[exact JF|];split;assumption.
Qed.
