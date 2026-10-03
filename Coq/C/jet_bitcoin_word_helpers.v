(** Resolve and execute the actual Bitcoin unit's pure word helpers. *)
From Coq Require Import ZArith.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Globalenvs Values Events.
Require Import C.jet_word_bits C.jet_LSBclear_width C.jet_LSBkeep_width.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage.
Import Ctypes Values List.ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma bitcoin_clear_symbol :
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) _LSBclear = Some (bitcoin_symbol_block _LSBclear).
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_clear_funct :
  Genv.find_funct (Clight.genv_genv bitcoin_ge) (Vptr (bitcoin_symbol_block _LSBclear) Ptrofs.zero) =
    Some (Internal f_LSBclear).
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_keep_symbol :
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) _LSBkeep = Some (bitcoin_symbol_block _LSBkeep).
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_keep_funct :
  Genv.find_funct (Clight.genv_genv bitcoin_ge) (Vptr (bitcoin_symbol_block _LSBkeep) Ptrofs.zero) =
    Some (Internal f_LSBkeep).
Proof. vm_compute; reflexivity. Qed.

Lemma eval_bitcoin_clear_width m w n : 1 <= n <= 64 ->
  Clight2.eval_funcall bitcoin_ge m (Internal f_LSBclear)
    [Vlong w; Vlong (Int64.repr n)] E0 m (Vlong (clear_low n w)).
Proof. apply eval_clear_width_ge. Qed.

Lemma eval_bitcoin_keep_width m w n : 1 <= n <= 64 ->
  Clight2.eval_funcall bitcoin_ge m (Internal f_LSBkeep)
    [Vlong w; Vlong (Int64.repr n)] E0 m (Vlong (Int64.zero_ext n w)).
Proof. apply eval_keep_width_ge. Qed.
