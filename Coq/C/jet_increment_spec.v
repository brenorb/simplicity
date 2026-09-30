(** Width-generic canonical increment program, shared by byte and wide jets. *)
Require Import Simplicity.Word Simplicity.Bit.

Definition full_increment_word_spec {term : Alg.Core.Algebra} (n : nat) :
    @Alg.Core.domain term (Ty.Prod Bit (Word n)) (Ty.Prod Bit (Word n)) :=
  @Alg.Core.Combinators.comp (Ty.Prod Bit (Word n))
    (Ty.Prod Bit (Ty.Prod (Word n) (Word n))) (Ty.Prod Bit (Word n)) term
    (@Alg.Core.Combinators.pair (Ty.Prod Bit (Word n)) Bit
      (Ty.Prod (Word n) (Word n)) term
      (@Alg.Core.Combinators.take Bit (Word n) Bit term
        (@Alg.Core.Combinators.iden Bit term))
      (@Alg.Core.Combinators.pair (Ty.Prod Bit (Word n)) (Word n) (Word n) term
        (@Alg.Core.Combinators.drop Bit (Word n) (Word n) term
          (@Alg.Core.Combinators.iden (Word n) term))
        (@Alg.Core.Combinators.comp (Ty.Prod Bit (Word n)) Ty.Unit (Word n) term
          (@Alg.Core.Combinators.unit (Ty.Prod Bit (Word n)) term)
          (@Word.zero n term))))
    (@Word.fullAdder n term).

Definition increment_word_spec {term : Alg.Core.Algebra} (n : nat) :
    @Alg.Core.domain term (Word n) (Ty.Prod Bit (Word n)) :=
  @Alg.Core.Combinators.comp (Word n) (Ty.Prod Bit (Word n))
    (Ty.Prod Bit (Word n)) term
    (@Alg.Core.Combinators.pair (Word n) Bit (Word n) term
      (@Bit.true (Word n) term) (@Alg.Core.Combinators.iden (Word n) term))
    (@full_increment_word_spec term n).
