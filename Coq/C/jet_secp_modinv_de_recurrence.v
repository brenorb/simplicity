(** Word recurrence compared directly with the actual full call outputs. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Values.
Require Import C.jet_sx_expr C.jet_sx_eval C.jet_secp_modinv_de_exec.
Require Import C.jet_secp_modinv_de_correction C.jet_secp_modinv_de_correction_numeric.
Require Import C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_iteration_prefix.
Require Import C.jet_secp_i128_shift62_rep C.jet_secp_modinv_normalize62_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition de62_shift_sx (p : sx*sx) :=
 (i128_shift62_lo_sx (fst p) (snd p),i128_shift62_hi_sx (snd p)).
Fixpoint de62_acc_sx (high : bool) (k : nat) : sx*sx :=
 match k with
 | O=>fg_iter_accum
   (fg_row_lo (XLv (if high then 12 else 10)) (XLv (if high then 13 else 11)),
    fg_row_hi (XLv (if high then 12 else 10)) (XLv (if high then 13 else 11)))
   (XLc (Int64.repr (-4294968273))) (de62_correction_sx high)
 | S n=>let next:=fg_iter_accum
   (fg_iter_accum (de62_shift_sx (de62_acc_sx high n))
    (XLv (if high then 12 else 10)) (XLv (S n)))
    (XLv (if high then 13 else 11)) (XLv (5+S n)) in
   if Nat.eqb (S n) 4 then fg_iter_accum next (XLc (Int64.repr 256)) (de62_correction_sx high)
   else next
 end.
Definition de62_recurrence_sx high i :=
 if Nat.eqb i 4 then fst (de62_shift_sx (de62_acc_sx high 4))
 else XLb Band (fst (de62_acc_sx high (S i))) norm62_mask.

Lemma de62_recurrence_matches high i : (i<5)%nat ->
 nth i (de62_limbs high) (XLc Int64.zero)=de62_recurrence_sx high i.
Proof.
 destruct high;destruct i as [|[|[|[|[|i]]]]];intro I;try lia.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
(* Closing the ten computed cases takes about nine seconds on the pinned
   toolchain; leave margin beyond the default ten-second tactic budget. *)
Timeout 30 Qed.
