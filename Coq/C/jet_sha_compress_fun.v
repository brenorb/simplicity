(** The interpretation of the generated compression body computes
    [SHA256.hash_block]: round-by-round invariant between the interpreter
    state (rotating physical registers, circular message schedule) and the
    functional model. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps.
Require sha.SHA256.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_round C.jet_sha_interp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

Fixpoint split_spine (fuel : nat) (s : statement) : list statement :=
  match fuel with
  | O => [s]
  | S fuel => match s with Ssequence a b => a :: split_spine fuel b | _ => [s] end
  end.

Fixpoint run (l : list statement) (st : cst) : option cst :=
  match l with
  | [] => Some st
  | a :: l' => match interp a (reset st) with Some st1 => run l' st1 | None => None end
  end.

Lemma interp_spine_run fuel : forall s st, interp_spine fuel s st = run (split_spine fuel s) st.
Proof.
  induction fuel as [|fuel IH]; intros s st; cbn [interp_spine split_spine run].
  - destruct (interp s (reset st)); reflexivity.
  - destruct s; cbn [run]; try (destruct (interp _ (reset st)); reflexivity).
    destruct (interp s1 (reset st)) as [st1|]; [apply IH|reflexivity].
Qed.

Lemma run_app l1 l2 st :
  run (l1 ++ l2) st = match run l1 st with Some st1 => run l2 st1 | None => None end.
Proof.
  revert st. induction l1 as [|a l1 IH]; intros st; cbn [run app]; [reflexivity|].
  destruct (interp a (reset st)); [apply IH|reflexivity].
Qed.

Definition body_elems : list statement :=
  Eval vm_compute in split_spine 79 (fn_body f_sha256_compression_portable).

Lemma body_elems_eq : split_spine 79 (fn_body f_sha256_compression_portable) = body_elems.
Proof. vm_compute. reflexivity. Qed.

Lemma int_eq_true_eq a b : Int.eq a b = true -> a = b.
Proof. intros H. pose proof (Int.eq_spec a b) as S. rewrite H in S. exact S. Qed.

Lemma int_mul_one' o x : Int.eq o Int.one = true -> Int.mul o x = x.
Proof. intros H. apply int_eq_true_eq in H. subst o. rewrite Int.mul_commut. apply Int.mul_one. Qed.

Lemma rnd_function_c x0 x1 x2 x3 x4 x5 x6 x7 Kc K W wt :
  Int.eq Kc K = true -> wt = W ->
  SHA256.rnd_function [x0; x1; x2; x3; x4; x5; x6; x7] K W =
    [Int.add (c_T1 x7 x4 x5 x6 (Int.add Kc wt)) (c_T2 x0 x1 x2); x0; x1; x2;
     Int.add x3 (c_T1 x7 x4 x5 x6 (Int.add Kc wt)); x4; x5; x6].
Proof.
  intros HK ->. apply int_eq_true_eq in HK. subst Kc.
  unfold SHA256.rnd_function, c_T1, c_T2.
  rewrite c_Sigma1_correct, c_Ch_correct, c_Sigma0_correct, c_Maj_correct.
  rewrite !Int.add_assoc. reflexivity.
Qed.

Section Fun.
Variables r0 r1 r2 r3 r4 r5 r6 r7 : int.
Variables c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : int.
Definition regs : list int := [r0; r1; r2; r3; r4; r5; r6; r7].
Definition block : list int := [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15].
Definition M : Z -> int := SHA256.nthi block.

Lemma W_first t : 0 <= t < 16 -> SHA256.W M t = M t.
Proof. intros Ht. rewrite SHA256.W_equation. rewrite zlt_true by lia. reflexivity. Qed.

Lemma W_step t wa wb wc wd one :
  16 <= t -> wa = SHA256.W M (t - 2) -> wb = SHA256.W M (t - 7) ->
  wc = SHA256.W M (t - 15) -> wd = SHA256.W M (t - 16) -> Int.eq one Int.one = true ->
  Int.add (Int.add (Int.add (Int.mul one wd) (c_sigma1 wa)) wb) (c_sigma0 wc) = SHA256.W M t.
Proof.
  intros Ht -> -> -> -> Ho. rewrite (int_mul_one' _ _ Ho).
  rewrite (SHA256.W_equation M t). rewrite zlt_false by lia.
  rewrite c_sigma1_correct, c_sigma0_correct.
  set (A := SHA256.sigma_1 (SHA256.W M (t - 2))). set (B := SHA256.W M (t - 7)).
  set (Cc := SHA256.sigma_0 (SHA256.W M (t - 15))). set (D := SHA256.W M (t - 16)).
  rewrite (Int.add_commut D A). rewrite !Int.add_assoc. f_equal.
  rewrite (Int.add_commut D (Int.add B Cc)). apply Int.add_assoc.
Qed.

Definition wlast (t j : nat) : nat := j + 16 * ((Nat.min t 62 - 1 - j) / 16).

Definition st_ok (st : cst) : Prop :=
  sarr st = regs /\ chunk st = block /\ ldef st = 8%nat /\ length (wv st) = 16%nat /\ length (lv st) = 8%nat.

Definition regs_inv (t : nat) (l : list int) : Prop :=
  map (fun j => nth ((j + 64 - t) mod 8) l Int.zero) (seq 0 8) = SHA256.Round regs M (Z.of_nat t - 1).

Definition w_inv (t : nat) (w : list int) : Prop :=
  forall j, (j < 16)%nat -> (j < t)%nat -> nth j w Int.zero = SHA256.W M (Z.of_nat (wlast t j)).

Definition Inv (t : nat) (st : cst) : Prop :=
  st_ok st /\ wdef st = Nat.min t 16 /\ regs_inv t (lv st) /\ w_inv t (wv st).

Definition round_stmt (t : nat) : statement := nth (8 + t) body_elems Sskip.
End Fun.
