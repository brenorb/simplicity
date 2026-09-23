(** Actual LP64 generated functions for the unsigned-long jet widths. *)
From Coq Require Import ZArith Lia.
From compcert Require Import AST Integers Ctypes Clight Globalenvs.
Require Import C.jets C.jet_exec.
Import Values Ctypes.
Local Open Scope Z_scope.

Inductive wide_size := W16 | W32 | W64.
Definition wide_bits s : Z := match s with W16 => 16 | W32 => 32 | W64 => 64 end.
Definition wide_log s : nat := match s with W16 => 4%nat | W32 => 5%nat | W64 => 6%nat end.
Definition wide_writer s := match s with
  W16 => f_simplicity_write16 | W32 => f_simplicity_write32 | W64 => f_simplicity_write64 end.
Definition wide_writer_id s := match s with
  W16 => _simplicity_write16 | W32 => _simplicity_write32 | W64 => _simplicity_write64 end.
Definition wide_reader s := match s with
  W16 => f_simplicity_read16 | W32 => f_simplicity_read32 | W64 => f_simplicity_read64 end.
Definition wide_reader_id s := match s with
  W16 => _simplicity_read16 | W32 => _simplicity_read32 | W64 => _simplicity_read64 end.
Definition wide_one s := match s with
  W16 => f_simplicity_one_16 | W32 => f_simplicity_one_32 | W64 => f_simplicity_one_64 end.

Lemma wide_bits_bounds s : 1 <= wide_bits s <= 64.
Proof. destruct s; cbn; lia. Qed.

Lemma wide_writer_symbol s : Genv.find_symbol (Clight.genv_genv ge0) (wide_writer_id s) =
  Some (jet_symbol_block (wide_writer_id s)).
Proof. destruct s; vm_compute; reflexivity. Qed.

Lemma wide_writer_funct s : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block (wide_writer_id s)) Ptrofs.zero) = Some (Internal (wide_writer s)).
Proof. destruct s; vm_compute; reflexivity. Qed.

Lemma wide_reader_symbol s : Genv.find_symbol (Clight.genv_genv ge0) (wide_reader_id s) =
  Some (jet_symbol_block (wide_reader_id s)).
Proof. destruct s; vm_compute; reflexivity. Qed.

Lemma wide_reader_funct s : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block (wide_reader_id s)) Ptrofs.zero) = Some (Internal (wide_reader s)).
Proof. destruct s; vm_compute; reflexivity. Qed.
