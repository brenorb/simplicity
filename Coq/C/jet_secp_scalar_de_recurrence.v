(** Explicit scalar-order recurrence, checked against all ten output limbs
    of the real update_de_62 call. No numeric/output property is assumed. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jet_sx_expr C.jet_sx_eval C.jet_sx_state C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_scalar_de_exec C.jet_secp_scalar_normalize62.
Require Import C.jet_secp_modinv_de_correction C.jet_secp_modinv_de_recurrence
 C.jet_secp_modinv_de_recurrence_words C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_prefix_numeric
 C.jet_secp_modinv_fg_iteration_prefix C.jet_secp_modinv_fg_iteration_arith
 C.jet_secp_i128_accum_mul_numeric C.jet_secp_modinv_normalize62_exec.
Require Import C.jet_secp_u128_word_sx.
Require Import C.jet_secp_multiply_run_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_de62_correction_sx high := XLb Bsub (de62_multiple_sx high)
 (XLb Band (XLb Badd (XLb Bmul (XLc(Int64.repr 3815112494326173377))
   (fg_row_lo (XLv(if high then 12 else 10)) (XLv(if high then 13 else 11))))
   (de62_multiple_sx high)) norm62_mask).
Definition scalar_de62_correction_word (rho : nat -> int64) high :=
 Int64.sub (de62_multiple_word rho high)
 (Int64.and (Int64.add (Int64.mul (Int64.repr 3815112494326173377)
   (fg_row_low rho (if high then 12%nat else 10%nat) (if high then 13%nat else 11%nat)))
   (de62_multiple_word rho high)) (Int64.repr(2^62-1))).
Lemma scalar_de62_correction_den rho beta high :
 den rho beta (scalar_de62_correction_sx high)=Vlong(scalar_de62_correction_word rho high).
Proof. destruct high;reflexivity. Qed.

Fixpoint scalar_de62_acc_sx (high : bool) (k : nat) : sx*sx :=
 match k with
 | O=>fg_iter_accum
   (fg_row_lo (XLv(if high then 12 else 10)) (XLv(if high then 13 else 11)),
    fg_row_hi (XLv(if high then 12 else 10)) (XLv(if high then 13 else 11)))
   (XLc(modinfo_scalar_limb 0)) (scalar_de62_correction_sx high)
 | S n=>let next:=fg_iter_accum
   (fg_iter_accum (de62_shift_sx(scalar_de62_acc_sx high n))
     (XLv(if high then 12 else 10)) (XLv(S n)))
     (XLv(if high then 13 else 11)) (XLv(5+S n)) in
   if Nat.eqb (S n) 3 then next else
     fg_iter_accum next (XLc(modinfo_scalar_limb(S n))) (scalar_de62_correction_sx high)
 end.
Definition scalar_de62_recurrence_sx high i :=
 if Nat.eqb i 4 then fst(de62_shift_sx(scalar_de62_acc_sx high 4))
 else XLb Band (fst(scalar_de62_acc_sx high (S i))) norm62_mask.
Lemma scalar_de62_recurrence_matches high i : (i<5)%nat ->
 nth i (scalar_de62_limbs high) (XLc Int64.zero)=scalar_de62_recurrence_sx high i.
Proof.
 destruct high;destruct i as [|[|[|[|[|i]]]]];intro I;try lia.
 - apply sx_beq_true. Timeout 30 vm_compute. reflexivity.
 - apply sx_beq_true. Timeout 30 vm_compute. reflexivity.
 - apply sx_beq_true. Timeout 30 vm_compute. reflexivity.
 - apply sx_beq_true. Timeout 30 vm_compute. reflexivity.
 - apply sx_beq_true. Timeout 30 vm_compute. reflexivity.
 - apply sx_beq_true. Timeout 30 vm_compute. reflexivity.
 - apply sx_beq_true. Timeout 30 vm_compute. reflexivity.
 - apply sx_beq_true. Timeout 30 vm_compute. reflexivity.
 - apply sx_beq_true. Timeout 30 vm_compute. reflexivity.
 - apply sx_beq_true. Timeout 30 vm_compute. reflexivity.
Qed.

Fixpoint scalar_de62_acc_words (rho : nat -> int64) (high : bool) (k : nat) : int64*int64 :=
 match k with
 | O=>fg_accum_words
   (fg_row_low rho (if high then 12%nat else 10%nat) (if high then 13%nat else 11%nat),
    fg_row_high rho (if high then 12%nat else 10%nat) (if high then 13%nat else 11%nat))
   (modinfo_scalar_limb 0) (scalar_de62_correction_word rho high)
 | S n=>let next:=fg_row_words (de62_shift_words(scalar_de62_acc_words rho high n))
   (rho(if high then 12%nat else 10%nat)) (rho(if high then 13%nat else 11%nat))
   (rho(S n)) (rho(5+S n)%nat) in
   if Nat.eqb (S n) 3 then next else
     fg_accum_words next (modinfo_scalar_limb(S n)) (scalar_de62_correction_word rho high)
 end.
Definition scalar_de62_recurrence_word rho high i :=
 if Nat.eqb i 4 then fst(de62_shift_words(scalar_de62_acc_words rho high 4))
 else Int64.and (fst(scalar_de62_acc_words rho high (S i))) (Int64.repr(2^62-1)).
Lemma scalar_de62_acc_words_den rho beta high k :
 den rho beta (fst(scalar_de62_acc_sx high k))=Vlong(fst(scalar_de62_acc_words rho high k)) /\
 den rho beta (snd(scalar_de62_acc_sx high k))=Vlong(snd(scalar_de62_acc_words rho high k)).
Proof.
 induction k as [|k IH].
 - destruct high;split;reflexivity.
 - cbn [scalar_de62_acc_sx scalar_de62_acc_words];destruct(Nat.eqb (S k) 3).
   + repeat first[rewrite(proj1(de62_accum_den _ _ _ _ _))|rewrite(proj2(de62_accum_den _ _ _ _ _))].
     rewrite (proj1(de62_shift_den _ _ _)),(proj2(de62_shift_den _ _ _)),(proj1 IH),(proj2 IH).
     split;reflexivity.
   + repeat first[rewrite(proj1(de62_accum_den _ _ _ _ _))|rewrite(proj2(de62_accum_den _ _ _ _ _))].
     rewrite (proj1(de62_shift_den _ _ _)),(proj2(de62_shift_den _ _ _)),
       (proj1 IH),(proj2 IH),scalar_de62_correction_den;split;reflexivity.
Qed.
Lemma scalar_de62_recurrence_den rho beta high i :
 den rho beta (scalar_de62_recurrence_sx high i)=Vlong(scalar_de62_recurrence_word rho high i).
Proof.
 unfold scalar_de62_recurrence_sx,scalar_de62_recurrence_word;destruct(Nat.eqb i 4).
 - rewrite (proj1(de62_shift_den _ _ _)),(proj1(scalar_de62_acc_words_den _ _ _ _)),
     (proj2(scalar_de62_acc_words_den _ _ _ _));reflexivity.
 - change (Vlong(Int64.and (il(den rho beta(fst(scalar_de62_acc_sx high (S i))))) (Int64.repr(2^62-1)))=
     Vlong(Int64.and (fst(scalar_de62_acc_words rho high (S i))) (Int64.repr(2^62-1)))).
   rewrite (proj1(scalar_de62_acc_words_den _ _ _ _));reflexivity.
Qed.
Lemma scalar_de62_word_recurrence rho high i : (i<5)%nat ->
 scalar_de62_word rho high i=scalar_de62_recurrence_word rho high i.
Proof.
 intro I;pose proof(scalar_de62_word_den rho (fun _=>(1%positive,0)) high i I) as Word.
 rewrite scalar_de62_recurrence_matches in Word by exact I.
 rewrite scalar_de62_recurrence_den in Word;congruence.
Qed.

Theorem eval_scalar_de_recurrence rho beta m : rep rho beta scalar_de62_regs m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_update_de_62)
  [Vptr(blk beta 0)(Ptrofs.repr(bas beta 0));Vptr(blk beta 1)(Ptrofs.repr(bas beta 1));
   Vptr(blk beta 2)(Ptrofs.repr(bas beta 2));Vptr(blk beta 3)(Ptrofs.repr(bas beta 3))] E0 mf Vundef /\
 (forall (high : bool) i,(i<5)%nat -> Mem.load Mint64 mf (blk beta (if high then 1 else 0))
   (bas beta (if high then 1 else 0)+8*Z.of_nat i)=Some(Vlong(scalar_de62_recurrence_word rho high i))) /\
 rep rho beta (sregs scalar_de62_state) mf /\
 lframe (fun b ofs=>~foot beta (map rshape scalar_de62_regs) b ofs) m mf.
Proof.
 intro Rep;destruct(scalar_eval_de_words rho beta m Rep) as (mf & Call & Words & Out & Frame).
 exists mf;split;[exact Call|];split.
 - intros high i I;rewrite <-scalar_de62_word_recurrence by exact I;apply Words;exact I.
 - split;assumption.
Qed.
