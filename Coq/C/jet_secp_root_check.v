(** The actual helper's equality test selects the literal program's branch.
    No mathematical square-root or primality theorem is used. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Clightdefs Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math C.jet_secp_fe_nv
 C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge C.jet_secp_canonical_normalize
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_square_execution
 C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric C.jet_secp_negate_literal_contract
 C.jet_secp_canonical_zero C.jet_secp_curve_literal C.jet_secp_x_equiv_literal
 C.jet_secp_root_literal C.jet_secp_root_chain_numeric C.jet_secp_root_chain_owned
 C.jet_secp_curve_statements C.jet_secp_equal_loose C.jet_secp_fns.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words root_chain_candidate literal_root_candidate
 literal_fe_square literal_fe_negate literal_fe_add canonical_fe_is_zero.

Definition root_check_flag w := Z.eqb (radix_value (square_words (root_chain_candidate w)) mod feP)
 (radix_value w mod feP).
Definition literal_root_check (x : Ty.tySem (Word 8)) :=
 @canonical_fe_is_zero Alg.CoreFunSem
  (@literal_fe_add Alg.CoreFunSem (@literal_fe_negate Alg.CoreFunSem x,
    @literal_fe_square Alg.CoreFunSem (literal_root_candidate x))).
Lemma literal_root_check_numeric x : Bit.toBool (literal_root_check x)=
 Z.eqb (@toZ (WordToZ 8) (@literal_fe_square Alg.CoreFunSem (literal_root_candidate x)) mod feP)
       (@toZ (WordToZ 8) x mod feP).
Proof.
 unfold literal_root_check;rewrite literal_curve_zero_numeric,literal_fe_add_numeric,
   canonical_field_order_matches_limb_model,literal_curve_negate_numeric.
 rewrite Z.mod_mod by (unfold feP,feR;lia).
 rewrite <-Z.add_mod_idemp_r by (unfold feP,feR;lia).
 rewrite x_equiv_mod_neg_add,Z.eqb_sym;reflexivity.
Qed.
Lemma root_check_flag_matches w x : root_words_match w x ->
 root_check_flag w=Bit.toBool (literal_root_check x).
Proof.
 intro HW;pose proof (root_chain_check_matches w x HW) as [_ HC];destruct HW as [_ HX].
 unfold root_check_flag;rewrite HC,HX;rewrite literal_root_check_numeric;reflexivity.
Qed.
Theorem root_result_matches w x : root_words_match w x ->
 @literal_fe_square_root Alg.CoreFunSem x=
 if root_check_flag w then inr (literal_root_candidate x) else inl tt.
Proof.
 intro HW;rewrite literal_root_result_step,(root_check_flag_matches w x HW).
 change (match literal_root_check x with inl _=>inl tt | inr _=>inr (literal_root_candidate x) end=
   if Bit.toBool (literal_root_check x) then inr (literal_root_candidate x) else inl tt).
 destruct (literal_root_check x) as [u|u];destruct u;reflexivity.
Qed.

Definition root_final_equal := curve_call _secp256k1_fe_equal_var f_secp256k1_fe_equal_var (Some _t'1)
 [curve_local_address _t1;Etempvar _a (tptr curve_fe_type)].
Definition root_final_check := Ssequence root_final_equal (Sreturn (Some (Etempvar _t'1 tint))).
Lemma root_final_check_source : root_drop_statements 40 (fn_body f_secp256k1_fe_sqrt_var)=root_final_check.
Proof. reflexivity. Qed.

Theorem exec_root_final_check e le m bt ba w x :
 root_words_match w x -> bt<>ba -> le!_a=Some (Vptr ba Ptrofs.zero) ->
 e!_t1=Some (bt,curve_fe_type) -> e!_secp256k1_fe_equal_var=None ->
 fe_at m bt 0 (words5 (square_words (root_chain_candidate w))) -> fe_at m ba 0 (words5 w) ->
 Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m ba 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m root_final_check E0
  (PTree.set _t'1 (Vint (if root_check_flag w then Int.one else Int.zero)) le) mf
  (Out_return (Some (Vint (if root_check_flag w then Int.one else Int.zero),tint))) /\
 Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf ba 0 40 Cur Freeable /\
 lframe (fun b _=>b<>bt /\ b<>ba) m mf.
Proof.
 intros HW Sep HA ET EE T A FT FA.
 pose proof (root_chain_candidate_matches w x HW) as [BC RC];destruct HW as [BW RW].
 destruct (eval_field_equal_loose_owned (square_words (root_chain_candidate w)) w m bt ba
   Sep (fun i HI=>proj2 (square_output_bounds _ BC i HI)) BW T A FT FA) as (mf & Equal & FTF & FAF & Frame).
 change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_equal_var)
   [Vptr bt Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf
   (Vint (if root_check_flag w then Int.one else Int.zero))) in Equal.
 assert (Call : Clight2.exec_stmt secp_ge e le m root_final_equal E0
   (PTree.set _t'1 (Vint (if root_check_flag w then Int.one else Int.zero)) le) mf Out_normal).
 { unfold root_final_equal;eapply exec_curve_call with
   (vargs:=[Vptr bt Ptrofs.zero;Vptr ba Ptrofs.zero])
   (v:=Vint (if root_check_flag w then Int.one else Int.zero)).
   - unfold secp_pure;repeat (first [left;reflexivity|right]).
   - exact EE.
   - eapply eval_Econs;[apply eval_curve_local;exact ET|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;exact HA|reflexivity|constructor].
   - exact Equal. }
 exists mf;split.
 - unfold root_final_check;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Call|].
   apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
 - split;[exact FTF|];split;assumption.
Qed.
