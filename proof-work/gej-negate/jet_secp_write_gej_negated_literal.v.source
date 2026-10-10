(** Actual original point writer on derived negation storage, against literal
    gej_negate output. Reader/helper/public lifecycle is composed separately. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Ty Simplicity.Alg Simplicity.Translate.
Require Import C.jet_toZ C.jet_word_repr C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_frame C.jet_frame_inv C.jet_output_layout.
Require Import C.jet_secp_canonical_normalize C.jet_secp_write_fe_numeric C.jet_secp_field_negate_storage.
Require Import C.jet_secp_point_field_bridge C.jet_secp_point_write_field.
Require Import C.jet_secp_point_three_general_writes C.jet_secp_gej_negate_literal.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize Simplicity.Translate.encode.

Theorem eval_write_gej_negated_literal m0 bd dbase bw edge cursor N bi (rc : Z) m b
    (x y z : Ty.tySem (Word 8)) :
  write_frame_at m0 bd dbase bw edge cursor N -> 768 <= N ->
  finv m0 bd dbase bw edge cursor N bi m false [] ->
  fe_at m b 0 (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem x)))) ->
  fe_at m b 40 (negate_values (write_fe_rho
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem y)) 0)) ->
  fe_at m b 80 (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem z)))) ->
  Mem.range_perm m b 0 128 Cur Freeable -> xsep (extA m0 bd bw bi) [(b,0)] ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_gej)
      [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 0)] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_gej_negate Alg.CoreFunSem ((x,y),z))) /\
    Mem.range_perm mf b 0 128 Cur Freeable /\
    lframe (fun bx _ => bx <> b /\ ~ extA m0 bd bw bi bx) m mf.
Proof.
  intros HO HN HI HX HY HZ HFree HS.
  rewrite <- point_canonical_field_limbs in HX,HZ.
  rewrite <- point_negative_field_limbs in HY.
  destruct (eval_write_gej_general m0 bd dbase bw edge cursor N bi rc m b
    (point_canonical_field (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem x)))
    (point_negative_field (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem y)))
    (point_canonical_field (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem z)))
    HO HN HI
    (point_canonical_field_bounded _ (word_toZ_range 8 _))
    (point_negative_field_bounded _ (word_toZ_range 8 _))
    (point_canonical_field_bounded _ (word_toZ_range 8 _))
    HX HY HZ HFree HS) as (mf & HCall & HFin & HFreeF & HFrame).
  rewrite literal_gej_negate_writer_encoding in HFin.
  exists mf; split; [exact HCall|]; split; [exact HFin|]; split; assumption.
Qed.
Timeout 60 Print Assumptions eval_write_gej_negated_literal.
