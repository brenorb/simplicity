(** Explicit model of the compiler builtin [__builtin_ctzl] called by the
    frozen [secp256k1_ctz64_var]. The generated program declares it as
    [EF_builtin "__builtin_ctzl"] with signature [[Tlong] -> Tint]. The
    pinned CompCert 3.14 has no known builtin of that name, so its semantics
    is the abstract parameter [external_functions_sem]
    (see [jet_secp_ctz_semantics_gap]).

    The statement below is the GCC/Clang contract of [__builtin_ctzl] on
    64-bit [unsigned long], restricted to nonzero arguments (the result for
    zero is undefined in C, and the divstep callers add a sentinel bit
    before counting): the number of trailing zero bits, no memory change and
    no observable event. It is a premise of every theorem that reaches that
    call, reported as a conditional result like [memcpy_model]. Nothing here
    proves that the compiler or linked library implements this contract. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs.
Require Import C.extraMath.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition ctz_sig : signature := mksignature [AST.Tlong] AST.Tint cc_default.

Definition ctz_model_for (sem : extcall_sem) : Prop :=
  forall (ge : Senv.t) m x, Int64.unsigned x <> 0 ->
    sem ge [Vlong x] m E0 (Vint (Int.repr (Z_ctz (Int64.unsigned x)))) m.

Definition ctz_model : Prop :=
  ctz_model_for (external_functions_sem "__builtin_ctzl" ctz_sig).

(** [Z_ctz] is the trailing-zero count: the result divides out exactly. *)
Lemma Z_ctz_pos_spec p :
  exists q, Z.pos p = 2 ^ Z_ctz (Z.pos p) * (2 * q + 1) /\ 0 <= q.
Proof.
  induction p as [p IH|p IH|]; cbn [Z_ctz Pos_ctz] in *.
  - exists (Z.pos p);rewrite Z.pow_0_r;lia.
  - destruct IH as [q [E Q]];exists q;split;[|exact Q].
    rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia.
    change (Z.pos p~0) with (2 * Z.pos p);rewrite E;ring.
  - exists 0;rewrite Z.pow_0_r;lia.
Qed.

Lemma Z_ctz_bound x : 0 < x < 2 ^ 64 -> 0 <= Z_ctz x < 64.
Proof.
  intros [Pos Lt];destruct x as [|p|p];try lia.
  destruct (Z_ctz_pos_spec p) as [q [E Q]].
  split;[apply Z_ctz_non_neg|].
  destruct (Z_lt_le_dec (Z_ctz (Z.pos p)) 64) as [L|L];[exact L|exfalso].
  assert (2 ^ 64 <= 2 ^ Z_ctz (Z.pos p)) by (apply Z.pow_le_mono_r;lia).
  nia.
Qed.
