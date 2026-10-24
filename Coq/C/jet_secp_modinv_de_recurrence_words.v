(** Explicit machine words of the complete original coefficient-update call. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jet_sx_expr C.jet_sx_eval C.jet_sx_state C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_de_exec.
Require Import C.jet_secp_modinv_de_correction C.jet_secp_modinv_de_correction_numeric.
Require Import C.jet_secp_modinv_fg_prefix_numeric C.jet_secp_modinv_fg_iteration_arith.
Require Import C.jet_secp_i128_shift62_numeric C.jet_secp_i128_accum_mul_numeric.
Require Import C.jet_secp_i128_shift62.
Require Import C.jet_secp_modinv_fg_iteration_prefix.
Require Import C.jet_secp_modinv_de_recurrence.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition de62_shift_words (p : int64*int64) :=
 (i128_shift62_low (fst p) (snd p),i128_shift62_high (snd p)).
Fixpoint de62_acc_words (rho : nat->int64) (high : bool) (k : nat) : int64*int64 :=
 match k with
 | O=>fg_accum_words
   (fg_row_low rho (if high then 12%nat else 10%nat) (if high then 13%nat else 11%nat),
    fg_row_high rho (if high then 12%nat else 10%nat) (if high then 13%nat else 11%nat))
   (Int64.repr (-4294968273)) (de62_correction_word rho high)
 | S n=>let next:=fg_row_words (de62_shift_words (de62_acc_words rho high n))
    (rho (if high then 12%nat else 10%nat)) (rho (if high then 13%nat else 11%nat))
    (rho (S n)) (rho (5+S n)%nat) in
   if Nat.eqb (S n) 4 then fg_accum_words next (Int64.repr 256) (de62_correction_word rho high)
   else next
 end.
Definition de62_recurrence_word rho high i :=
 if Nat.eqb i 4 then fst (de62_shift_words (de62_acc_words rho high 4))
 else Int64.and (fst (de62_acc_words rho high (S i))) (Int64.repr (2^62-1)).

Lemma de62_accum_den rho beta (p : sx*sx) a b :
 den rho beta (fst (fg_iter_accum p a b))=
   Vlong (fst (fg_accum_words (il (den rho beta (fst p)),il (den rho beta (snd p)))
     (il (den rho beta a)) (il (den rho beta b)))) /\
 den rho beta (snd (fg_iter_accum p a b))=
   Vlong (snd (fg_accum_words (il (den rho beta (fst p)),il (den rho beta (snd p)))
     (il (den rho beta a)) (il (den rho beta b)))).
Proof. split;reflexivity. Qed.

Lemma de62_shift_den rho beta (p : sx*sx) :
 den rho beta (fst (de62_shift_sx p))=
 Vlong (fst (de62_shift_words (il (den rho beta (fst p)),il (den rho beta (snd p))))) /\
 den rho beta (snd (de62_shift_sx p))=
 Vlong (snd (de62_shift_words (il (den rho beta (fst p)),il (den rho beta (snd p))))).
Proof. split;reflexivity. Qed.

Lemma de62_acc_words_den rho beta high k :
 den rho beta (fst (de62_acc_sx high k))=Vlong (fst (de62_acc_words rho high k)) /\
 den rho beta (snd (de62_acc_sx high k))=Vlong (snd (de62_acc_words rho high k)).
Proof.
 induction k as [|k IH].
 - destruct high;split;reflexivity.
 - cbn [de62_acc_sx de62_acc_words];destruct (Nat.eqb (S k) 4).
   + repeat first [rewrite (proj1 (de62_accum_den _ _ _ _ _))|
        rewrite (proj2 (de62_accum_den _ _ _ _ _))].
     rewrite (proj1 (de62_shift_den _ _ _)),(proj2 (de62_shift_den _ _ _)).
     rewrite (proj1 IH),(proj2 IH),de62_correction_den;split;reflexivity.
   + repeat first [rewrite (proj1 (de62_accum_den _ _ _ _ _))|
        rewrite (proj2 (de62_accum_den _ _ _ _ _))].
     rewrite (proj1 (de62_shift_den _ _ _)),(proj2 (de62_shift_den _ _ _)).
     rewrite (proj1 IH),(proj2 IH);split;reflexivity.
Qed.

Lemma de62_recurrence_den rho beta high i :
 den rho beta (de62_recurrence_sx high i)=Vlong (de62_recurrence_word rho high i).
Proof.
 unfold de62_recurrence_sx,de62_recurrence_word;destruct (Nat.eqb i 4).
 - rewrite (proj1 (de62_shift_den _ _ _)),(proj1 (de62_acc_words_den _ _ _ _)),
    (proj2 (de62_acc_words_den _ _ _ _));reflexivity.
 - change (Vlong (Int64.and (il (den rho beta (fst (de62_acc_sx high (S i)))))
     (Int64.repr (2^62-1)))=
     Vlong (Int64.and (fst (de62_acc_words rho high (S i))) (Int64.repr (2^62-1)))).
   rewrite (proj1 (de62_acc_words_den _ _ _ _));reflexivity.
Qed.

Lemma de62_word_recurrence rho high i : (i<5)%nat ->
 de62_word rho high i=de62_recurrence_word rho high i.
Proof.
 intro I;pose proof (de62_word_den rho (fun _=>(1%positive,0)) high i I) as Word.
 rewrite de62_recurrence_matches in Word by exact I.
 rewrite de62_recurrence_den in Word;congruence.
Qed.

(** Complete execution of the unchanged helper, now against an explicit
    five-limb machine recurrence. Integer/modular-value invariants remain
    separate obligations, not assumptions added to this execution result. *)
Theorem eval_de_recurrence rho beta m : rep rho beta de62_regs m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_update_de_62)
  [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
   Vptr (blk beta 2) (Ptrofs.repr (bas beta 2));Vptr (blk beta 3) (Ptrofs.repr (bas beta 3))] E0 mf Vundef /\
 (forall (high : bool) i,(i<5)%nat -> Mem.load Mint64 mf (blk beta (if high then 1 else 0))
  (bas beta (if high then 1 else 0)+8*Z.of_nat i)=Some (Vlong (de62_recurrence_word rho high i))) /\
 rep rho beta (sregs de62_state) mf /\
 lframe (fun b ofs=>~foot beta (map rshape de62_regs) b ofs) m mf.
Proof.
 intro Rep;destruct (eval_de_words rho beta m Rep) as (mf & Call & Words & Out & Frame).
 exists mf;split;[exact Call|];split.
 - intros high i I;rewrite <-de62_word_recurrence by exact I;apply Words;exact I.
 - split;assumption.
Qed.
