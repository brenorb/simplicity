(** Explicit model of the plain libc [memcpy] called by the aligned paths of
    [copyBitsHelper].  The generated program declares it as
    [EF_external "memcpy"], whose CompCert semantics is the abstract parameter
    [external_functions_sem]; CompCert's runtime provides no definition.  The
    statement below is the C standard contract of [memcpy] for valid,
    non-overlapping ranges, stated as a premise of every theorem that reaches
    that call. The copy effect has the checked builtin witness below, but
    the abstract external function also has a different argument/result ABI.
    Nothing here proves that the linked libc implements this contract. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Definition memcpy_sig : signature :=
  mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil) AST.Tlong cc_default.

Definition memcpy_model : Prop :=
  forall (ge : Senv.t) m bd od bs os n bytes,
    Mem.loadbytes m bs (Ptrofs.unsigned os) n = Some bytes ->
    Mem.range_perm m bd (Ptrofs.unsigned od) (Ptrofs.unsigned od + n) Cur Writable ->
    (bs <> bd \/ Ptrofs.unsigned os + n <= Ptrofs.unsigned od \/
      Ptrofs.unsigned od + n <= Ptrofs.unsigned os) ->
    0 <= n <= Int64.max_unsigned ->
    exists m', Mem.storebytes m bd (Ptrofs.unsigned od) bytes = Some m' /\
      external_call (EF_external "memcpy" memcpy_sig) ge
        [Vptr bd od; Vptr bs os; Vlong (Int64.repr n)] m E0 (Vptr bd od) m'.

(** The specified memory effect is executable in CompCert's defined builtin
    semantics, with byte alignment. This does not discharge [memcpy_model]:
    the builtin takes two arguments and returns [Vundef], whereas libc takes
    three arguments and returns the destination pointer. *)
Lemma memcpy_builtin_witness (ge : Senv.t) m bd od bs os n bytes :
  Mem.loadbytes m bs (Ptrofs.unsigned os) n = Some bytes ->
  Mem.range_perm m bd (Ptrofs.unsigned od) (Ptrofs.unsigned od + n) Cur Writable ->
  (bs <> bd \/ Ptrofs.unsigned os + n <= Ptrofs.unsigned od \/
    Ptrofs.unsigned od + n <= Ptrofs.unsigned os) ->
  0 <= n ->
  exists m', Mem.storebytes m bd (Ptrofs.unsigned od) bytes = Some m' /\
    extcall_memcpy_sem n 1 ge [Vptr bd od; Vptr bs os] m E0 Vundef m'.
Proof.
  intros Hload Hperm Hsep Hn.
  assert (Hlength : Z.of_nat (length bytes) = n).
  { rewrite (Mem.loadbytes_length _ _ _ _ _ Hload). apply Z2Nat.id; exact Hn. }
  assert (Hdest : Mem.range_perm m bd (Ptrofs.unsigned od)
    (Ptrofs.unsigned od + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlength. exact Hperm. }
  destruct (Mem.range_perm_storebytes m bd (Ptrofs.unsigned od) bytes Hdest)
    as [m' Hstore].
  exists m'. split; [exact Hstore|].
  apply extcall_memcpy_sem_intro with (bytes := bytes).
  - left; reflexivity.
  - lia.
  - apply Z.divide_1_l.
  - intros _. apply Z.divide_1_l.
  - intros _. apply Z.divide_1_l.
  - destruct Hsep as [Hsep | [Hsep | Hsep]]; auto.
  - exact Hload.
  - exact Hstore.
Qed.

Definition block_memcpy : block := jet_symbol_block _memcpy.

Lemma symbol_memcpy :
  Genv.find_symbol (Clight.genv_genv ge0) _memcpy = Some block_memcpy.
Proof. vm_compute; reflexivity. Qed.

Lemma funct_memcpy :
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_memcpy Ptrofs.zero) =
    Some (External (EF_external "memcpy" memcpy_sig)
      (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid) cc_default).
Proof. vm_compute; reflexivity. Qed.
