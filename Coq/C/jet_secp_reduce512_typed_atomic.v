(** Source-bound actual second-fold slice with atomic stage inputs and both real casts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Ctypes.
Require Import C.jet_sx_expr C.jets_secp.
Require Import C.jet_secp_scalar_mul512_symbolic C.jet_secp_reduce512_symbolic
  C.jet_secp_reduce512_wide C.jet_secp_reduce512_typed_stage.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Section TYPED.
Variable digits : nat -> int64.
Variable m6 : int.
Definition stage_sy_m6 := XI2L Unsigned (XI m6).
Definition stage_ma_m6 := Int64.repr (Int.unsigned m6).
Definition stage_sy0 := wide_symbolic_muladd_fast (XL (digits 4%nat)) wide_symbolic_C0
  (wide_symbolic_from_word (XL (digits 0%nat))).
Definition stage_sy1 := wide_symbolic_muladd (XL (digits 4%nat)) wide_symbolic_C1
  (wide_symbolic_muladd (XL (digits 5%nat)) wide_symbolic_C0
    (wide_symbolic_sumadd_fast (XL (digits 1%nat)) (wide_symbolic_extract_fast stage_sy0))).
Definition stage_sy2 := wide_symbolic_sumadd (XL (digits 4%nat))
  (wide_symbolic_muladd (XL (digits 5%nat)) wide_symbolic_C1
    (wide_symbolic_muladd stage_sy_m6 wide_symbolic_C0
      (wide_symbolic_sumadd (XL (digits 2%nat)) (wide_symbolic_extract stage_sy1)))).
Definition stage_sy3 := wide_symbolic_sumadd_fast (XL (digits 5%nat))
  (wide_symbolic_muladd_fast stage_sy_m6 wide_symbolic_C1
    (wide_symbolic_sumadd_fast (XL (digits 3%nat)) (wide_symbolic_extract stage_sy2))).
Definition stage_symbolic_outputs := [sc_lo stage_sy0; sc_lo stage_sy1; sc_lo stage_sy2;
  sc_lo stage_sy3; XI2L Unsigned (XL2I (XLb Badd (sc_hi stage_sy3) stage_sy_m6))].
Lemma stage_symbolic_source : (reduce512_typed_stage_limbs digits m6) = stage_symbolic_outputs.
Proof.
  unfold reduce512_typed_stage_limbs,stage_symbolic_outputs.
  apply f_equal2; [timeout 10 reflexivity|].
  apply f_equal2; [timeout 10 reflexivity|].
  apply f_equal2; [timeout 10 reflexivity|].
  apply f_equal2; [timeout 10 reflexivity|].
  apply f_equal2; timeout 10 reflexivity.
Qed.
Definition stage_ma0 := wide_muladd_fast (digits 4%nat) wide_C0
  (wide_from_word (digits 0%nat)).
Definition stage_ma1 := wide_muladd (digits 4%nat) wide_C1
  (wide_muladd (digits 5%nat) wide_C0
    (wide_sumadd_fast (digits 1%nat) (wide_extract_fast stage_ma0))).
Definition stage_ma2 := wide_sumadd (digits 4%nat)
  (wide_muladd (digits 5%nat) wide_C1
    (wide_muladd stage_ma_m6 wide_C0
      (wide_sumadd (digits 2%nat) (wide_extract stage_ma1)))).
Definition stage_ma3 := wide_sumadd_fast (digits 5%nat)
  (wide_muladd_fast stage_ma_m6 wide_C1
    (wide_sumadd_fast (digits 3%nat) (wide_extract stage_ma2))).
Definition stage_machine_outputs := [wlo stage_ma0; wlo stage_ma1;
  wlo stage_ma2; wlo stage_ma3;
  Int64.repr (Int.unsigned (Int64.loword (Int64.add (whi stage_ma3) stage_ma_m6)))].
Lemma stage_m6_den rho beta : den rho beta stage_sy_m6 = Vlong stage_ma_m6.
Proof.
  reflexivity.
Qed.
Lemma stage_columns_rep rho beta :
  wide_rep rho beta stage_sy0 stage_ma0 /\
  wide_rep rho beta stage_sy1 stage_ma1 /\
  wide_rep rho beta stage_sy2 stage_ma2 /\
  wide_rep rho beta stage_sy3 stage_ma3.
Proof.
  assert (F0 : den rho beta (XL (digits 0%nat)) = Vlong (digits 0%nat)) by reflexivity.
  assert (F1 : den rho beta (XL (digits 1%nat)) = Vlong (digits 1%nat)) by reflexivity.
  assert (F2 : den rho beta (XL (digits 2%nat)) = Vlong (digits 2%nat)) by reflexivity.
  assert (F3 : den rho beta (XL (digits 3%nat)) = Vlong (digits 3%nat)) by reflexivity.
  assert (F4 : den rho beta (XL (digits 4%nat)) = Vlong (digits 4%nat)) by reflexivity.
  assert (F5 : den rho beta (XL (digits 5%nat)) = Vlong (digits 5%nat)) by reflexivity.
  pose proof (stage_m6_den rho beta) as FM6.
  assert (H0 : wide_rep rho beta stage_sy0 stage_ma0).
  { apply wide_muladd_fast_rep; [exact F4|apply wide_C0_den|apply wide_from_word_rep; exact F0]. }
  assert (H1 : wide_rep rho beta stage_sy1 stage_ma1).
  { apply wide_muladd_rep; [exact F4|apply wide_C1_den|].
    apply wide_muladd_rep; [exact F5|apply wide_C0_den|].
    apply wide_sumadd_fast_rep; [exact F1|apply wide_extract_fast_rep; exact H0]. }
  assert (H2 : wide_rep rho beta stage_sy2 stage_ma2).
  { apply wide_sumadd_rep; [exact F4|]. apply wide_muladd_rep; [exact F5|apply wide_C1_den|].
    apply wide_muladd_rep; [exact FM6|apply wide_C0_den|].
    apply wide_sumadd_rep; [exact F2|apply wide_extract_rep; exact H1]. }
  assert (H3 : wide_rep rho beta stage_sy3 stage_ma3).
  { apply wide_sumadd_fast_rep; [exact F5|].
    apply wide_muladd_fast_rep; [exact FM6|apply wide_C1_den|].
    apply wide_sumadd_fast_rep; [exact F3|apply wide_extract_rep; exact H2]. }
  exact (conj H0 (conj H1 (conj H2 H3))).
Qed.
Lemma stage_outputs_machine rho beta :
  map (den rho beta) (reduce512_typed_stage_limbs digits m6) = map Vlong stage_machine_outputs.
Proof.
  rewrite stage_symbolic_source.
  destruct (stage_columns_rep rho beta) as [[H0 _] [[H1 _] [[H2 _] [H3 [HH _]]]]].
  change ([den rho beta (sc_lo stage_sy0); den rho beta (sc_lo stage_sy1);
    den rho beta (sc_lo stage_sy2); den rho beta (sc_lo stage_sy3);
    den rho beta (XI2L Unsigned (XL2I (XLb Badd (sc_hi stage_sy3) stage_sy_m6)))] =
    [Vlong (wlo stage_ma0); Vlong (wlo stage_ma1); Vlong (wlo stage_ma2);
      Vlong (wlo stage_ma3);
      Vlong (Int64.repr (Int.unsigned (Int64.loword (Int64.add (whi stage_ma3) stage_ma_m6))))]).
  rewrite H0,H1,H2,H3.
  assert (Hsum : den rho beta (XLb Badd (sc_hi stage_sy3) stage_sy_m6) =
    Vlong (Int64.add (whi stage_ma3) stage_ma_m6))
    by (apply column_ladd_den; [exact HH|apply stage_m6_den]).
  assert (HC : den rho beta (XI2L Unsigned (XL2I (XLb Badd (sc_hi stage_sy3) stage_sy_m6))) =
    Vlong (Int64.repr (Int.unsigned (Int64.loword (Int64.add (whi stage_ma3) stage_ma_m6))))).
  { change (Vlong (Int64.repr (Int.unsigned (Int64.loword
      (il (den rho beta (XLb Badd (sc_hi stage_sy3) stage_sy_m6)))))) =
      Vlong (Int64.repr (Int.unsigned (Int64.loword
        (Int64.add (whi stage_ma3) stage_ma_m6))))).
    rewrite Hsum; reflexivity. }
  rewrite HC; reflexivity.
Qed.
End TYPED.
