(** Linked-program replacement of [jet_memcpy_model].

    In the linked core program the symbol [memcpy] is bound to the internal
    function generated from [jet_memcpy_exact.c] instead of an external
    declaration.  [memcpy_model] keeps the premises and the memory conclusion
    of the libc contract, but its call is the Clight big-step execution of
    that function, and it is a theorem ([memcpy_model_holds]) rather than a
    premise about the abstract external-function semantics. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec.
Require C.memcpy_exact C.jet_memcpy_exact.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

Definition memcpy_sig : signature :=
  mksignature (AST.Tlong :: AST.Tlong :: AST.Tlong :: nil) AST.Tlong cc_default.

(** The call of the linked definition, with the argument order of
    [external_call] so that the call-site modules are textually derived from
    the accepted ones. *)
Definition memcpy_call (ge : genv) (args : list val) (m : mem) (t : trace)
    (v : val) (m' : mem) : Prop :=
  Clight2.eval_funcall ge m (Internal f_memcpy) args t m' v.

Definition memcpy_model : Prop :=
  forall (ge : genv) m bd od bs os n bytes,
    Mem.valid_block m bs -> Mem.valid_block m bd ->
    Mem.loadbytes m bs (Ptrofs.unsigned os) n = Some bytes ->
    Mem.range_perm m bd (Ptrofs.unsigned od) (Ptrofs.unsigned od + n) Cur Writable ->
    (bs <> bd \/ Ptrofs.unsigned os + n <= Ptrofs.unsigned od \/
      Ptrofs.unsigned od + n <= Ptrofs.unsigned os) ->
    0 < n <= Int64.max_unsigned ->
    Ptrofs.unsigned os + n <= Ptrofs.max_unsigned + 1 ->
    Ptrofs.unsigned od + n <= Ptrofs.max_unsigned + 1 ->
    exists m', Mem.storebytes m bd (Ptrofs.unsigned od) bytes = Some m' /\
      memcpy_call ge
        [Vptr bd od; Vptr bs os; Vlong (Int64.repr n)] m E0 (Vptr bd od) m'.

(** The linked definition is the function proved in [jet_memcpy_exact]. *)
Lemma linked_memcpy_definition : f_memcpy = memcpy_exact.f_memcpy.
Proof. reflexivity. Qed.

Theorem memcpy_model_holds : memcpy_model.
Proof.
  intros ge m bd od bs os n bytes _ _ HL HP Hsep Hn Hse Hde.
  unfold memcpy_call. rewrite linked_memcpy_definition.
  exact (jet_memcpy_exact.eval_memcpy_exact ge m bd od bs os n bytes
    HL HP Hsep Hn Hse Hde).
Qed.

Definition block_memcpy : block := jet_symbol_block _memcpy.

Lemma symbol_memcpy :
  Genv.find_symbol (Clight.genv_genv ge0) _memcpy = Some block_memcpy.
Proof. vm_compute; reflexivity. Qed.

Lemma funct_memcpy :
  Genv.find_funct (Clight.genv_genv ge0) (Vptr block_memcpy Ptrofs.zero) =
    Some (Internal f_memcpy).
Proof. vm_compute; reflexivity. Qed.
