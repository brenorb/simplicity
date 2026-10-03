(** Concrete linkage/layout observations for the real Bitcoin translation unit.
    Identical helper syntax is not yet an execution transport theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Maps Globalenvs Errors Values.
Require Import C.jets C.jets_bitcoin.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition bitcoin_ge : Clight.genv := Clight.globalenv jets_bitcoin.prog.
Definition bitcoin_symbol_block (id : ident) : block :=
  match Genv.find_symbol (Clight.genv_genv bitcoin_ge) id with
  | Some b => b | None => 1%positive end.

Lemma bitcoin_write32_symbol :
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) jets_bitcoin._simplicity_write32 =
    Some (bitcoin_symbol_block jets_bitcoin._simplicity_write32).
Proof. vm_compute; reflexivity. Qed.

Lemma bitcoin_write32_funct :
  Genv.find_funct (Clight.genv_genv bitcoin_ge)
    (Values.Vptr (bitcoin_symbol_block jets_bitcoin._simplicity_write32) Ptrofs.zero) =
    Some (Internal jets_bitcoin.f_simplicity_write32).
Proof. vm_compute; reflexivity. Qed.

Lemma bitcoin_write32_body_shared :
  jets_bitcoin.f_simplicity_write32 = jets.f_simplicity_write32.
Proof. reflexivity. Qed.

Lemma bitcoin_frame_composite_shared :
  (Clight.genv_cenv bitcoin_ge)!jets_bitcoin._frameItem =
    (prog_comp_env jets.prog)!jets._frameItem.
Proof. vm_compute; reflexivity. Qed.

Lemma bitcoin_env_tx_field :
  match (Clight.genv_cenv bitcoin_ge)!jets_bitcoin._txEnv with
  | Some co => field_offset (Clight.genv_cenv bitcoin_ge) jets_bitcoin._tx (co_members co) = OK (0, Full)
  | None => False
  end.
Proof. vm_compute; reflexivity. Qed.

Lemma bitcoin_tx_version_field :
  match (Clight.genv_cenv bitcoin_ge)!jets_bitcoin._bitcoinTransaction with
  | Some co => field_offset (Clight.genv_cenv bitcoin_ge) jets_bitcoin._version (co_members co) = OK (464, Full)
  | None => False
  end.
Proof. vm_compute; reflexivity. Qed.
