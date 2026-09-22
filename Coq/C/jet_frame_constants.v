(** Evaluate the generated UWORD_BIT expression once, without unfolding a
    symbolic frame computation or assuming a helper contract. *)
From Coq Require Import ZArith.
From compcert Require Import Integers AST Ctypes Cop Clight.
Require Import C.jets.
Import Values Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.

Definition generated_uword_bits : expr :=
  match fn_body f_simplicity_write8 with
  | Ssequence
      (Ssequence _ (Ssequence _
        (Sset _ (Ebinop Oadd _ (Ebinop Odiv _ width _) _)))) _ => width
  | _ => Econst_long Int64.zero tulong
  end.

Ltac eval_closed_frame_constant :=
  lazymatch goal with
  | |- eval_expr _ _ _ _ (Econst_int _ _) _ => apply eval_Econst_int
  | |- eval_expr _ _ _ _ (Econst_long _ _) _ => apply eval_Econst_long
  | |- eval_expr _ _ _ _ (Ecast _ _) _ =>
      eapply eval_Ecast; [eval_closed_frame_constant | cbn; reflexivity]
  | |- eval_expr _ _ _ _ (Eunop _ _ _) _ =>
      eapply eval_Eunop; [eval_closed_frame_constant | cbn; reflexivity]
  | |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ =>
      eapply eval_Ebinop;
        [eval_closed_frame_constant | eval_closed_frame_constant | cbn; reflexivity]
  end.

Lemma eval_generated_uword_bits ge e le m :
  eval_expr ge e le m generated_uword_bits (Vlong (Int64.repr 64)).
Proof.
  unfold generated_uword_bits, f_simplicity_write8; cbn [fn_body].
  timeout 10 eval_closed_frame_constant.
Qed.
