(** [malloc] in the environment unit is CompCert's [EF_malloc], whose
    semantics is defined (not assumed): a fresh block with bounds
    [-8, size) whose header word stores the size.  CompCert's model has no
    failing allocation, so the builders' NULL-return paths after [malloc]
    are not exercised by these statements. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jets_sha C.jet_sha_linkage.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Definition malloc_fundef : Clight.fundef := External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default.

Lemma sha_malloc_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _malloc = Some (sha_symbol_block _malloc).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_malloc_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _malloc) Ptrofs.zero) =
    Some malloc_fundef.
Proof. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

Theorem eval_malloc m (n : Z) :
  0 <= n <= Ptrofs.max_unsigned ->
  exists m1 m2 b,
    Mem.alloc m (-8) n = (m1, b) /\
    Mem.store Mptr m1 b (-8) (Vlong (Int64.repr n)) = Some m2 /\
    Clight2.eval_funcall sha_ge m malloc_fundef [Vlong (Int64.repr n)] E0 m2 (Vptr b Ptrofs.zero).
Proof.
  intros Hn.
  destruct (Mem.alloc m (-8) n) as [m1 b] eqn:HA.
  destruct (Mem.valid_access_store m1 Mptr b (-8) (Vlong (Int64.repr n))) as [m2 HS].
  { split.
    - intros ofs Hr. change (size_chunk Mptr) with 8 in Hr.
      eapply Mem.perm_implies; [eapply Mem.perm_alloc_2; [exact HA|lia]|constructor].
    - exists (-1). reflexivity. }
  exists m1, m2, b. split; [reflexivity|]. split; [exact HS|].
  apply eval_funcall_external. cbn.
  assert (HV : Vlong (Int64.repr n) = Vptrofs (Ptrofs.repr n)).
  { unfold Vptrofs. cbn. unfold Ptrofs.to_int64. rewrite Ptrofs.unsigned_repr by lia. reflexivity. }
  rewrite HV in HS |- *.
  eapply extcall_malloc_sem_intro with (m' := m1).
  - rewrite Ptrofs.unsigned_repr by lia. exact HA.
  - exact HS.
Qed.
