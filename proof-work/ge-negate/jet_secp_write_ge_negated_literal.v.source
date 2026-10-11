(** Actual affine writer output equals the literal canonical Simplicity program. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Ty Simplicity.Alg Simplicity.Translate.
Require Import C.jet_toZ C.jet_word_repr C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_frame C.jet_frame_inv C.jet_output_layout.
Require Import C.jet_secp_canonical_normalize C.jet_secp_write_fe_numeric C.jet_secp_field_negate_storage.
Require Import C.jet_secp_canonical_negate C.jet_secp_negate_literal_contract.
Require Import C.jet_secp_point_field_bridge C.jet_secp_point_write_field C.jet_secp_gej_negate_literal.
Require Import C.jet_secp_write_ge_general.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize Simplicity.Translate.encode.

Lemma literal_ge_negate_step (x y : Ty.tySem (Word 8)) :
  @literal_ge_negate Alg.CoreFunSem (x,y) =
    (@canonical_fe_normalize Alg.CoreFunSem x,@literal_fe_negate Alg.CoreFunSem y).
Proof. unfold literal_ge_negate; reflexivity. Qed.

Lemma literal_ge_negate_writer_encoding (x y : Ty.tySem (Word 8)) :
  (Simplicity.Translate.encode (point_field_output (point_canonical_field
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem x)))) ++
   Simplicity.Translate.encode (point_field_output (point_negative_field
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem y))))) =
  Simplicity.Translate.encode (@literal_ge_negate Alg.CoreFunSem (x,y)).
Proof.
  rewrite (point_normalized_field_output x), (point_normalized_negative_field_output y),
    literal_ge_negate_step.
  symmetry; apply point_encode_pair.
Qed.

Theorem eval_write_ge_negated_literal m0 bd dbase bw edge cursor N bi (rc : Z) m b
    (x y : Ty.tySem (Word 8)) :
  write_frame_at m0 bd dbase bw edge cursor N -> 512 <= N ->
  finv m0 bd dbase bw edge cursor N bi m false [] ->
  fe_at m b 0 (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem x)))) ->
  fe_at m b 40 (negate_values (write_fe_rho
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem y)) 0)) ->
  Mem.range_perm m b 0 88 Cur Freeable -> xsep (extA m0 bd bw bi) [(b,0)] ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_ge)
      [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 0)] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_ge_negate Alg.CoreFunSem (x,y))) /\
    Mem.range_perm mf b 0 88 Cur Freeable /\
    lframe (fun bx _ => bx <> b /\ ~ extA m0 bd bw bi bx) m mf.
Proof.
  intros HO HN HI HX HY HFree HS.
  rewrite <- point_canonical_field_limbs in HX.
  rewrite <- point_negative_field_limbs in HY.
  destruct (eval_write_ge_general m0 bd dbase bw edge cursor N bi rc m b
    (point_canonical_field (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem x)))
    (point_negative_field (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem y)))
    HO HN HI
    (point_canonical_field_bounded _ (word_toZ_range 8 _))
    (point_negative_field_bounded _ (word_toZ_range 8 _))
    HX HY HFree HS) as (mf & HCall & HFin & HFreeF & HFrame).
  rewrite literal_ge_negate_writer_encoding in HFin.
  exists mf; split;[exact HCall|];split;[exact HFin|];split;assumption.
Qed.
Print Assumptions literal_ge_negate_step.
Print Assumptions literal_ge_negate_writer_encoding.
Timeout 60 Print Assumptions eval_write_ge_negated_literal.
