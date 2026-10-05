(** Literal port of Programs.Bitcoin.buildTapbranch
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
Require Import C.jet_order_spec C.jet_sha_ctx8_model C.jet_sha_finalize_exec.
Require Import C.jet_sha_tapdata_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

Module AC := Alg.Core.Combinators.

Definition tapbranch_prefix : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) 16128481659354054051886650070918308588707920384911815168968115687213851879122.
Definition tapbranch_tag_word : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) 11423784003423245473257913154601382734653671235488771667104991518695318003733.
Definition tapbranch_tag_block : Ty.tySem (Word 9) :=
  @fromZ (WordToZ 9) 4419371621777418713669862736773585009732451909885880897487510725603506506676440551277137483196335502719270104272573258040306099979007799678344122037436488.
Definition tapbranch_tag_bytes : list int := map Int.repr [84; 97; 112; 66; 114; 97; 110; 99; 104].

Lemma tapbranch_tag_hash_eval :
  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, tapbranch_tag_block) = tapbranch_tag_word.
Proof. vm_compute. reflexivity. Qed.

Lemma tapbranch_prefix_eval :
  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, (tapbranch_tag_word, tapbranch_tag_word)) =
    tapbranch_prefix.
Proof. vm_compute. reflexivity. Qed.

Lemma tapbranch_tag_block_bytes :
  map Int.unsigned (map word8_array_value (vector_values (Word 3) 6 tapbranch_tag_block)) =
  map Int.unsigned (tapbranch_tag_bytes ++ sha_pad (Int64.repr 9)).
Proof. vm_compute. reflexivity. Qed.

Definition tb_padblock : Ty.tySem (Word 9) := @fromZ (WordToZ 9) (2 ^ 511 + 1024).

Lemma tb_padblock_words :
  map Int.unsigned (map word32_array_value (word32_chunks 4 tb_padblock)) =
  map Int.unsigned (be_words (sha_pad (Int64.repr 128))).
Proof. vm_compute. reflexivity. Qed.

Definition build_tapbranch_spec {term : Alg.Core.Algebra} : @Alg.Core.domain term (Word 9) (Word 8) :=
  AC.comp
    (AC.pair
      (AC.comp
        (AC.pair (AC.comp AC.unit (Alg.scribe tapbranch_prefix))
          (AC.comp (AC.pair (@lt_word_spec term 8) AC.iden)
            (Bit.cond AC.iden (AC.pair (AC.drop AC.iden) (AC.take AC.iden)))))
        (@Simplicity.SHA256.hashBlock term))
      (AC.comp AC.unit (Alg.scribe tb_padblock)))
    (@Simplicity.SHA256.hashBlock term).

Lemma build_tapbranch_spec_parametric : Alg.Core.Parametric (@build_tapbranch_spec).
Proof.
  intros alg1 alg2 R. unfold build_tapbranch_spec.
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

Definition tapbranch_order (a b : Ty.tySem (Word 8)) : Ty.tySem (Word 9) :=
  if @toZ (WordToZ 8) a <? @toZ (WordToZ 8) b then (a, b) else (b, a).

Lemma build_tapbranch_spec_value (a b : Ty.tySem (Word 8)) :
  @build_tapbranch_spec Alg.CoreFunSem (a, b) =
    @Simplicity.SHA256.hashBlock Alg.CoreFunSem
      (@Simplicity.SHA256.hashBlock Alg.CoreFunSem (tapbranch_prefix, tapbranch_order a b), tb_padblock).
Proof.
  unfold build_tapbranch_spec, tapbranch_order.
  pose proof (lt_word_spec_numeric 8 a b) as HLt.
  set (ab := ((a, b) : Ty.tySem (Word 9))).
  match goal with |- _ = ?R => change (@Simplicity.SHA256.hashBlock Alg.CoreFunSem
    (@Simplicity.SHA256.hashBlock Alg.CoreFunSem
      (@Alg.scribe (Word 9) (Word 8) tapbranch_prefix Alg.CoreFunSem ab,
       @Bit.cond (Word 9) (Word 9) Alg.CoreFunSem AC.iden (AC.pair (AC.drop AC.iden) (AC.take AC.iden))
         ((@lt_word_spec Alg.CoreFunSem 8 ab, ab) : Ty.tySem (Ty.Prod Bit (Word 9)))),
     @Alg.scribe (Word 9) (Word 9) tb_padblock Alg.CoreFunSem ab) = R) end.
  rewrite !Alg.scribe_correct. rewrite <- HLt. fold ab.
  destruct (@lt_word_spec Alg.CoreFunSem 8 ab) as [[]|[]]; reflexivity.
Qed.
