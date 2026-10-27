(** Explicit model of the plain libc [memset] called by the frozen secp unit
    ([secp256k1_ecmult_wnaf] clears its digit buffer; the x-only key helpers
    clear their output objects). The generated program declares it as
    [EF_external "memset"] with signature [[Tlong; Tint; Tlong] -> Tlong],
    whose CompCert semantics is the abstract parameter
    [external_functions_sem].

    The statement below is the C standard contract of [memset] for a valid,
    writable range of 1 to 1024 bytes: every byte becomes [(unsigned char) c],
    the destination pointer is returned, and there is no observable event. The
    size bound covers the largest call site (a 256-entry [int] buffer) and
    limits the assumed guarantee; callers prove it from their own
    preconditions. It is a premise of every theorem that reaches the call,
    reported as a conditional result like [memcpy_model]. Nothing here proves
    that the linked libc implements this contract. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Definition memset_sig : signature :=
  mksignature [AST.Tlong; AST.Tint; AST.Tlong] AST.Tlong cc_default.

(** [n] copies of the low byte of [c]. *)
Definition memset_bytes (c : int) (n : Z) : list memval :=
  repeat (Byte (Byte.repr (Int.unsigned c))) (Z.to_nat n).

Lemma memset_bytes_length c n : 0 <= n -> Z.of_nat (length (memset_bytes c n)) = n.
Proof. intro; unfold memset_bytes; rewrite repeat_length; apply Z2Nat.id; lia. Qed.

Definition memset_model_for (sem : extcall_sem) : Prop :=
  forall (ge : Senv.t) m bd od c n,
    Mem.valid_block m bd ->
    Mem.range_perm m bd (Ptrofs.unsigned od) (Ptrofs.unsigned od + n) Cur Writable ->
    0 < n <= 1024 ->
    exists m', Mem.storebytes m bd (Ptrofs.unsigned od) (memset_bytes c n) = Some m' /\
      sem ge [Vptr bd od; Vint c; Vlong (Int64.repr n)] m E0 (Vptr bd od) m'.

Definition memset_model : Prop :=
  memset_model_for (external_functions_sem "memset" memset_sig).
