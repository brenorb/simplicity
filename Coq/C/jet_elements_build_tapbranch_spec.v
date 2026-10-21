(** Literal port of Programs.Elements.buildTapbranch
      buildTapbranch = ((unit >>> tapbranchPrefix)
                    &&& (lt word256 &&& iden >>> cond iden (ih &&& oh))
                    >>> hashBlock)
                    &&& (unit >>> scribe (toWord512 $ 2^511 + 1024)) >>> hashBlock
    and its value.  No C execution here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Simplicity.Alg Simplicity.SHA256.
Require Import C.jet_word_repr C.jet_buffer_input C.jet_read8s_layout C.jet_read32s_layout C.jet_word32_chunks.
Require Import C.jet_order_spec C.jet_sha_ctx8_model C.jet_elements_support_sha_finalize_exec.
Require Import C.jet_sha_tapdata_spec.
Import ListNotations.
Require Import C.jet_elements_tap_tags.
Local Open Scope Z_scope.
Set Default Timeout 10.

Module AC := Alg.Core.Combinators.

Definition el_tapbranch_prefix : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) 114263694252184772880787512168443418545102503793510752740155459060743883240588.
Definition el_tapbranch_tag_word : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) 72467471652795983392102958712465387133823812133035191840482760359472060527558.
Definition el_tapbranch_tag_block : Ty.tySem (Word 9) :=
  @fromZ (WordToZ 9) 4419371621777418713668968785755975466456634992571949198094180134647787309897038044043048421949944770650201509248730180031032202822044656739855673939984528.
Definition el_tapbranch_tag_bytes : list int := map Int.repr [84; 97; 112; 66; 114; 97; 110; 99; 104; 47; 101; 108; 101; 109; 101; 110; 116; 115].

Lemma el_tapbranch_tag_hash_eval :
  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, el_tapbranch_tag_block) = el_tapbranch_tag_word.
Proof. vm_compute. reflexivity. Qed.

Lemma el_tapbranch_prefix_eval :
  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, (el_tapbranch_tag_word, el_tapbranch_tag_word)) =
    el_tapbranch_prefix.
Proof. vm_compute. reflexivity. Qed.

Lemma el_tapbranch_tag_block_bytes :
  map Int.unsigned (map word8_array_value (vector_values (Word 3) 6 el_tapbranch_tag_block)) =
  map Int.unsigned (el_tapbranch_tag_bytes ++ sha_pad (Int64.repr 18)).
Proof. vm_compute. reflexivity. Qed.

Definition el_tb_padblock : Ty.tySem (Word 9) := @fromZ (WordToZ 9) (2 ^ 511 + 1024).

Lemma el_tb_padblock_words :
  map Int.unsigned (map word32_array_value (word32_chunks 4 el_tb_padblock)) =
  map Int.unsigned (be_words (sha_pad (Int64.repr 128))).
Proof. vm_compute. reflexivity. Qed.

Definition el_build_tapbranch_spec {term : Alg.Core.Algebra} : @Alg.Core.domain term (Word 9) (Word 8) :=
  AC.comp
    (AC.pair
      (AC.comp
        (AC.pair (AC.comp AC.unit (Alg.scribe el_tapbranch_prefix))
          (AC.comp (AC.pair (@lt_word_spec term 8) AC.iden)
            (Bit.cond AC.iden (AC.pair (AC.drop AC.iden) (AC.take AC.iden)))))
        (@Simplicity.SHA256.hashBlock term))
      (AC.comp AC.unit (Alg.scribe el_tb_padblock)))
    (@Simplicity.SHA256.hashBlock term).

Lemma el_build_tapbranch_spec_parametric : Alg.Core.Parametric (@el_build_tapbranch_spec).
Proof.
  intros alg1 alg2 R. unfold el_build_tapbranch_spec.
  assert (US : forall A B (v : Ty.tySem B),
    @Alg.Core.Parametric.rel _ _ R A B (AC.comp AC.unit (Alg.scribe v)) (AC.comp AC.unit (Alg.scribe v))).
  { intros A B v. apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply Alg.scribe_Parametric]. }
  apply Alg.comp_Parametric; [|apply Simplicity.SHA256.hashBlock_Parametric].
  apply Alg.pair_Parametric; [|apply US].
  apply Alg.comp_Parametric; [|apply Simplicity.SHA256.hashBlock_Parametric].
  apply Alg.pair_Parametric; [apply US|].
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply (lt_word_spec_parametric 8)|apply Alg.iden_Parametric].
  - apply Bit.cond_Parametric; [apply Alg.iden_Parametric|].
    apply Alg.pair_Parametric; [apply Alg.drop_Parametric|apply Alg.take_Parametric]; apply Alg.iden_Parametric.
Qed.

Definition el_tapbranch_order (a b : Ty.tySem (Word 8)) : Ty.tySem (Word 9) :=
  if @toZ (WordToZ 8) a <? @toZ (WordToZ 8) b then (a, b) else (b, a).

Lemma el_build_tapbranch_spec_value (a b : Ty.tySem (Word 8)) :
  @el_build_tapbranch_spec Alg.CoreFunSem (a, b) =
    @Simplicity.SHA256.hashBlock Alg.CoreFunSem
      (@Simplicity.SHA256.hashBlock Alg.CoreFunSem (el_tapbranch_prefix, el_tapbranch_order a b), el_tb_padblock).
Proof.
  unfold el_build_tapbranch_spec, el_tapbranch_order.
  pose proof (lt_word_spec_numeric 8 a b) as HLt.
  set (ab := ((a, b) : Ty.tySem (Word 9))).
  match goal with |- _ = ?R => change (@Simplicity.SHA256.hashBlock Alg.CoreFunSem
    (@Simplicity.SHA256.hashBlock Alg.CoreFunSem
      (@Alg.scribe (Word 9) (Word 8) el_tapbranch_prefix Alg.CoreFunSem ab,
       @Bit.cond (Word 9) (Word 9) Alg.CoreFunSem AC.iden (AC.pair (AC.drop AC.iden) (AC.take AC.iden))
         ((@lt_word_spec Alg.CoreFunSem 8 ab, ab) : Ty.tySem (Ty.Prod Bit (Word 9)))),
     @Alg.scribe (Word 9) (Word 9) el_tb_padblock Alg.CoreFunSem ab) = R) end.
  rewrite !Alg.scribe_correct. rewrite <- HLt. fold ab.
  destruct (@lt_word_spec Alg.CoreFunSem 8 ab) as [[]|[]]; reflexivity.
Qed.
