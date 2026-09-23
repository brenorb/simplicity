(** Canonical primitive Simplicity one specifications and physical observations.
    This is the same true >>> left_pad_low word1 wordN program as one_8. *)
From Coq Require Import ZArith.
From compcert Require Import Integers AST Memory.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Util.Monad.
Require Import C.jet_spec C.jet_wide C.jet_output_slice.
Local Open Scope Z_scope.

Definition wide_one_spec s {term : Alg.Core.Algebra} :
    @Alg.Core.domain term Ty.Unit (Word (wide_log s)) :=
  @Alg.Core.Combinators.comp Ty.Unit Bit (Word (wide_log s)) term
    (@Bit.true Ty.Unit term) (@left_pad_low_1_n term (wide_log s)).

Definition decode_wide s w : Ty.tySem (Word (wide_log s)) :=
  @fromZ (WordToZ (wide_log s)) (Int64.unsigned w).

Definition wide_output_at s m bw edge cursor value : Prop :=
  exists payload, slice_output_at (wide_bits s) m bw edge cursor payload /\
    decode_wide s payload = value.

Lemma decode_wide_one s :
  decode_wide s (Int64.zero_ext (wide_bits s) Int64.one) = @wide_one_spec s Alg.CoreFunSem tt.
Proof. destruct s; vm_compute; reflexivity. Qed.

Lemma wide_one_spec_parametric s : Alg.Core.Parametric (@wide_one_spec s).
Proof.
  intros alg1 alg2 R. unfold wide_one_spec.
  apply Alg.comp_Parametric; [apply Bit.true_Parametric|apply left_pad_low_1_n_parametric].
Qed.

Lemma wide_one_spec_initial s (M : CIMonad.type) : forall u,
  @wide_one_spec s (Alg.CoreSem M) u = eta (@wide_one_spec s Alg.CoreFunSem u).
Proof. apply Alg.CoreSem_initial. apply wide_one_spec_parametric. Qed.

Lemma wide_output_at_preserved s m mf bw edge cursor x :
  (forall ofs w, Mem.load Mint64 m bw ofs = Some (Values.Vlong w) ->
    Mem.load Mint64 mf bw ofs = Some (Values.Vlong w)) ->
  wide_output_at s m bw edge cursor x -> wide_output_at s mf bw edge cursor x.
Proof.
  intros HP [w [HW HX]]. exists w. split; [eapply slice_output_at_preserved; eauto|exact HX].
Qed.
