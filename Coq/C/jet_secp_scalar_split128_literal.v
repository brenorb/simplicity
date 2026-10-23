(** Bridge the original C split_128 output to the literal normalized split
    used by generate. Normalized input is an internal reader obligation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Simplicity.Bit.
Require Import C.jet_toZ C.jet_word_repr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_scalar_split128.
Require Import C.jet_secp_canonical_scalar C.jet_secp_scalar_canonical_parametric.
Require Import C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage.
Require Import C.jet_secp_scalar_limb_bridge C.jet_secp_scalar_reader_value.
Require Import C.jet_secp_scalar_overflow_numeric C.jet_secp_wrapper_run C.jet_secp_input_bytes.
Require Import C.jet_input_layout C.jet_secp_scalar_reader_lifecycle.
Import ListNotations Values.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_scalar_split128 {term : Alg.Core.Algebra} :
 term (Word 8) (Ty.Prod (Ty.Prod Bit.Bit (Word 7)) (Ty.Prod Bit.Bit (Word 7))) :=
 @canonical_scalar_normalize term >>>
  ((@Bit.false (Word 8) term &&& I H) &&& (@Bit.false (Word 8) term &&& O H)).
Definition literal_split128_low value := snd (fst (@literal_scalar_split128 Alg.CoreFunSem value)).
Definition literal_split128_high value := snd (snd (@literal_scalar_split128 Alg.CoreFunSem value)).

Lemma literal_scalar_split128_step value : @literal_scalar_split128 Alg.CoreFunSem value=
 ((inl tt,snd (@canonical_scalar_normalize Alg.CoreFunSem value)),
  (inl tt,fst (@canonical_scalar_normalize Alg.CoreFunSem value))).
Proof. reflexivity. Qed.

Lemma literal_scalar_split128_parametric : Alg.Core.Parametric (@literal_scalar_split128).
Proof.
 intros t1 t2 R;unfold literal_scalar_split128,Bit.false.
 repeat first [apply canonical_scalar_normalize_parametric|apply Alg.comp_Parametric|
  apply Alg.pair_Parametric|apply Alg.injl_Parametric|apply Alg.unit_Parametric|
  apply Alg.drop_Parametric|apply Alg.take_Parametric|apply Alg.iden_Parametric].
Qed.

Lemma literal_scalar_split128_numeric value :
 @toZ (WordToZ 7) (literal_split128_low value)=
  @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value) mod 2^128 /\
 @toZ (WordToZ 7) (literal_split128_high value)=
  @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value) / 2^128.
Proof.
 unfold literal_split128_low,literal_split128_high;rewrite literal_scalar_split128_step.
 destruct (@canonical_scalar_normalize Alg.CoreFunSem value) as [hi lo].
 change (@toZ (WordToZ 7) lo=(@toZ (WordToZ 7) hi*2^128+@toZ (WordToZ 7) lo) mod 2^128 /\
  @toZ (WordToZ 7) hi=(@toZ (WordToZ 7) hi*2^128+@toZ (WordToZ 7) lo) /2^128).
 pose proof (word_toZ_range 7 lo) as Low;change (0<=@toZ (WordToZ 7) lo<2^128) in Low.
 replace (@toZ (WordToZ 7) hi*2^128+@toZ (WordToZ 7) lo) with
  (@toZ (WordToZ 7) lo+@toZ (WordToZ 7) hi*2^128) by ring.
 split.
 - rewrite Z.mod_add by lia;rewrite Z.mod_small by exact Low;reflexivity.
 - rewrite Z.div_add by lia;rewrite Z.div_small by exact Low;lia.
Qed.

Lemma scalar_split128_literal_values rho value :
 scalar_split128_input_value rho=@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value) ->
 scalar_split128_low rho=@toZ (WordToZ 7) (literal_split128_low value) /\
 scalar_split128_high rho=@toZ (WordToZ 7) (literal_split128_high value).
Proof.
 intro Input;destruct (scalar_split128_values rho) as (_ & _ & Low & High).
 destruct (literal_scalar_split128_numeric value) as [L H].
 rewrite Input in Low,High;split;congruence.
Qed.

Lemma scalar_split128_two_word_limbs w0 w1 :
 map Int64.repr (scalar_limbs_of (Int64.unsigned w0+2^64*Int64.unsigned w1))=
 [w0;w1;Int64.zero;Int64.zero].
Proof.
 replace (Int64.unsigned w0+2^64*Int64.unsigned w1) with
  (Int64.unsigned w0+2^64*Int64.unsigned w1+2^128*Int64.unsigned Int64.zero+
   2^192*Int64.unsigned Int64.zero) by (rewrite Int64.unsigned_zero;ring).
 rewrite scalar_limbs_of_four_words;cbn [map];rewrite !Int64.repr_unsigned;reflexivity.
Qed.

Lemma scalar_split128_output_storage owned rho beta mf :
 rep rho beta (scalar_split128_output_regs owned) mf ->
 Mem.range_perm mf (blk beta 0) 0 32 Cur Freeable ->
 Mem.range_perm mf (blk beta 1) 0 32 Cur Freeable ->
 scalar_at mf (blk beta 0) (bas beta 0)
  (map Int64.repr (scalar_limbs_of (scalar_split128_low rho))) /\
 scalar_at mf (blk beta 1) (bas beta 1)
  (map Int64.repr (scalar_limbs_of (scalar_split128_high rho))).
Proof.
 intros Rep F0 F1.
 pose proof (rep_region rho beta _ mf 0 _ Rep eq_refl) as R0.
 pose proof (rep_region rho beta _ mf 1 _ Rep eq_refl) as R1.
 destruct R0 as (_ & _ & _ & _ & (Base0 & _));destruct R1 as (_ & _ & _ & _ & (Base1 & _)).
 unfold scalar_split128_low,scalar_split128_high;rewrite !scalar_split128_two_word_limbs.
 split;unfold scalar_at;split;[reflexivity| |reflexivity|].
 - split;[rewrite Base0;lia|];split;[rewrite Base0;exists 0;lia|];split.
   + rewrite Base0;change (32<=18446744073709551615);lia.
   + split.
     * rewrite Base0;intros pos Range;eapply Mem.perm_implies;[apply F0;exact Range|constructor].
     * exact (scalar_split128_low_loads owned rho beta mf Rep).
 - split;[rewrite Base1;lia|];split;[rewrite Base1;exists 0;lia|];split.
   + rewrite Base1;change (32<=18446744073709551615);lia.
   + split.
     * rewrite Base1;intros pos Range;eapply Mem.perm_implies;[apply F1;exact Range|constructor].
     * exact (scalar_split128_high_loads owned rho beta mf Rep).
Qed.

Theorem eval_scalar_split128_normalized_literal owned rho beta m value :
 rep rho beta (scalar_split128_regs owned) m ->
 scalar_split128_input_value rho=@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value) ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_split_128)
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
   Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef /\
 rep rho beta (scalar_split128_output_regs owned) mf /\
 scalar_at mf (blk beta 0) (bas beta 0)
  (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (literal_split128_low value)))) /\
 scalar_at mf (blk beta 1) (bas beta 1)
  (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (literal_split128_high value)))) /\
 Mem.range_perm mf (blk beta 0) 0 32 Cur Freeable /\
 Mem.range_perm mf (blk beta 1) 0 32 Cur Freeable /\
 (owned=true -> Mem.range_perm mf (blk beta 2) 0 32 Cur Freeable) /\
 lframe (fun b pos=>~foot beta (map rshape (scalar_split128_regs owned)) b pos) m mf.
Proof.
 intros Rep Input.
 destruct (eval_scalar_split128_owned owned rho beta m Rep)
  as (mf & Call & Final & Loads0 & Loads1 & Free0 & Free1 & Free2 & Low & High & Mod & Div & Frame).
 destruct (scalar_split128_output_storage owned rho beta mf Final Free0 Free1) as [Storage0 Storage1].
 destruct (scalar_split128_literal_values rho value Input) as [LowerValue UpperValue].
 rewrite LowerValue in Storage0;rewrite UpperValue in Storage1.
 exists mf;split;[exact Call|];split;[exact Final|];split;[exact Storage0|];
 split;[exact Storage1|];split;[exact Free0|];split;[exact Free1|];split;assumption.
Qed.

Lemma scalar_reader_split128_value value rc layout :
 scalar_split128_input_value (scalar_reader_limb (read_fe_rho (frame_input_word_bits value) rc) layout)=
 @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value).
Proof.
 change (scalar_limb_value (scalar_reader_limb (read_fe_rho (frame_input_word_bits value) rc) layout)=
  @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)).
 rewrite scalar_reader_value_mod_group by (rewrite frame_input_word_bits_length;reflexivity).
 rewrite input_bytes_word256_value,canonical_scalar_normalize_numeric;reflexivity.
Qed.
