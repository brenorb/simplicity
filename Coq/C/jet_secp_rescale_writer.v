(** The original write_gej on the derived rescale storage.  This supplies
    actual serialization, not only an equality of abstract field values. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_frame_inv C.jet_output_layout C.jet_secp_fe_nv
  C.jet_secp_linkage C.jets_secp C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_point_write_field C.jet_secp_point_three_general_writes.
Require Import C.jet_secp_gej_negate_literal.
Require Import C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric
  C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_square_spec_bridge
  C.jet_secp_square_separate_numeric C.jet_secp_rescale_literal.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words literal_gej_rescale Simplicity.Translate.encode.

Definition rescale_point_field (w : nat -> int64) :=
  mkpointfield (w 0%nat) (w 1%nat) (w 2%nat) (w 3%nat) (w 4%nat).
Lemma rescale_point_limbs w : point_field_limbs (rescale_point_field w) = words5 w.
Proof. reflexivity. Qed.
Lemma rescale_point_bounds w : square_input_bounds w -> point_field_bounds (rescale_point_field w).
Proof.
  intro HB; unfold point_field_bounds, rescale_point_field; cbn [pf0 pf1 pf2 pf3 pf4].
  repeat split; (eapply rescale_writer_bounds; [exact HB|lia]).
Qed.
Lemma rescale_point_output w : point_field_output (rescale_point_field w) = rescale_field_output w.
Proof. reflexivity. Qed.

Lemma rescale_output_encoding (x y z s : tySem (Word 8)) :
  ((Simplicity.Translate.encode (rescale_field_output
      (point_mul_words (square_reader_rho x) (square_words (square_reader_rho s)))) ++
    Simplicity.Translate.encode (rescale_field_output
      (point_mul_words (point_mul_words (square_reader_rho y) (square_words (square_reader_rho s)))
        (square_reader_rho s)))) ++
    Simplicity.Translate.encode (rescale_field_output (point_mul_words (square_reader_rho z) (square_reader_rho s)))) =
  Simplicity.Translate.encode (@literal_gej_rescale Alg.CoreFunSem (((x,y),z),s)).
Proof.
  pose proof (f_equal (@Simplicity.Translate.encode (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)))
    (rescale_reader_outputs_literal x y z s)) as HE.
  rewrite (@point_encode_pair (Ty.Prod (Word 8) (Word 8)) (Word 8)) in HE.
  rewrite (@point_encode_pair (Word 8) (Word 8)) in HE; exact HE.
Qed.

Theorem eval_write_gej_rescaled_literal m0 bd dbase bw edge cursor N bi (rc : Z) m bp
    (x y z s : tySem (Word 8)) :
  write_frame_at m0 bd dbase bw edge cursor N -> 768 <= N ->
  finv m0 bd dbase bw edge cursor N bi m false [] ->
  fe_at m bp 0 (words5 (point_mul_words (square_reader_rho x) (square_words (square_reader_rho s)))) ->
  fe_at m bp 40 (words5 (point_mul_words
    (point_mul_words (square_reader_rho y) (square_words (square_reader_rho s))) (square_reader_rho s))) ->
  fe_at m bp 80 (words5 (point_mul_words (square_reader_rho z) (square_reader_rho s))) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> xsep (extA m0 bd bw bi) [(bp,0)] ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_gej)
      [Vptr bd (Ptrofs.repr dbase);Vptr bp Ptrofs.zero] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_gej_rescale Alg.CoreFunSem (((x,y),z),s))) /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\
    lframe (fun b _ => b <> bp /\ ~ extA m0 bd bw bi b) m mf.
Proof.
  intros HO HN HI HX HY HZ HF HS.
  pose proof (square_result_reusable (square_reader_rho s) (square_reader_bounds s)) as BSS.
  pose proof (proj2 (point_mul_value_and_bounds _ _ (square_reader_bounds x) BSS)) as BX.
  pose proof (proj2 (point_mul_value_and_bounds _ _ (square_reader_bounds y) BSS)) as BY1.
  pose proof (proj2 (point_mul_value_and_bounds _ _ BY1 (square_reader_bounds s))) as BY.
  pose proof (proj2 (point_mul_value_and_bounds _ _ (square_reader_bounds z) (square_reader_bounds s))) as BZ.
  rewrite <- rescale_point_limbs in HX, HY, HZ.
  destruct (eval_write_gej_general m0 bd dbase bw edge cursor N bi rc m bp
    (rescale_point_field (point_mul_words (square_reader_rho x) (square_words (square_reader_rho s))))
    (rescale_point_field (point_mul_words
      (point_mul_words (square_reader_rho y) (square_words (square_reader_rho s))) (square_reader_rho s)))
    (rescale_point_field (point_mul_words (square_reader_rho z) (square_reader_rho s)))
    HO HN HI (rescale_point_bounds _ BX) (rescale_point_bounds _ BY) (rescale_point_bounds _ BZ)
    HX HY HZ HF HS) as (mf & HCall & HFin & HFree & HFrame).
  rewrite !rescale_point_output, rescale_output_encoding in HFin.
  exists mf; split; [exact HCall|]; split; [exact HFin|]; split; assumption.
Qed.
