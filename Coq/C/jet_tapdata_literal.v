(** The canonical TapData initializer, deriving the scribed prefix from
    the fixed host recipe rather than assuming its published numeral. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_core_pad_spec C.jet_buffer_empty_spec.
Require Import C.jet_sha256_ctx8_init_spec C.jet_sha_tapdata_spec C.jet_tapdata_host_recipe.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_tapdata_one64 {term : Alg.Core.Algebra} : term Ty.Unit (Word 6) :=
  Bit.true >>> @left_pad_low_spec term 0 6.

Lemma literal_tapdata_one64_matches term : @literal_tapdata_one64 term = @one64_spec term.
Proof. reflexivity. Qed.

Definition literal_tapdata_init {term : Alg.Core.Algebra} : term Ty.Unit sha256_ctx8_type :=
  @buffer_empty_spec (Word 3) 5 Ty.Unit term &&&
    (@literal_tapdata_one64 term &&& Alg.scribe tap_host_prefix).

Lemma literal_tapdata_init_matches term : @literal_tapdata_init term = @tapdata_init_spec term.
Proof.
  unfold literal_tapdata_init, tapdata_init_spec.
  rewrite tap_host_prefix_matches, literal_tapdata_one64_matches. reflexivity.
Qed.
