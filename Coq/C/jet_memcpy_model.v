(** Explicit model of the plain libc [memcpy] called by the aligned paths of
    [copyBitsHelper].  The generated program declares it as
    [EF_external "memcpy"], whose CompCert semantics is the abstract parameter
    [external_functions_sem]; CompCert's runtime provides no definition.  The
    statement below is the C standard contract of [memcpy] for valid,
    non-overlapping ranges, stated as a premise of every theorem that reaches
    that call.  It is satisfiable (it is exactly the semantics of CompCert's
    builtin [EF_memcpy] restricted to word copies) and is never assumed
    implicitly. *)
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

Definition block_memcpy : block := jet_symbol_block _memcpy.

Lemma symbol_memcpy :
  Genv.find_symbol (Clight.genv_genv ge0) _memcpy = Some block_memcpy.
Proof. vm_compute; reflexivity. Qed.

Lemma funct_memcpy :
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_memcpy Ptrofs.zero) =
    Some (External (EF_external "memcpy" memcpy_sig)
      (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid) cc_default).
Proof. vm_compute; reflexivity. Qed.
