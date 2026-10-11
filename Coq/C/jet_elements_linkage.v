(** Concrete linkage/layout observations for the real Elements translation
    unit ([jet_elements_translation_unit.c]: frame helpers, core jets,
    SHA-256, Elements operations and Elements jets).  Port of
    [jet_bitcoin_linkage]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Maps Globalenvs Errors Values.
Require Import C.jets C.jets_elements.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_ge : Clight.genv := Clight.globalenv jets_elements.prog.
Definition elements_symbol_block (id : ident) : block :=
  match Genv.find_symbol (Clight.genv_genv elements_ge) id with
  | Some b => b | None => 1%positive end.

Lemma elements_write32_symbol :
  Genv.find_symbol (Clight.genv_genv elements_ge) jets_elements._simplicity_write32 =
    Some (elements_symbol_block jets_elements._simplicity_write32).
Proof. vm_compute; reflexivity. Qed.

Lemma elements_write32_funct :
  Genv.find_funct (Clight.genv_genv elements_ge)
    (Values.Vptr (elements_symbol_block jets_elements._simplicity_write32) Ptrofs.zero) =
    Some (Internal jets_elements.f_simplicity_write32).
Proof. vm_compute; reflexivity. Qed.

Lemma elements_write32_body_shared :
  jets_elements.f_simplicity_write32 = jets.f_simplicity_write32.
Proof. reflexivity. Qed.

Lemma elements_env_tx_field :
  match (Clight.genv_cenv elements_ge)!jets_elements._txEnv with
  | Some co => field_offset (Clight.genv_cenv elements_ge) jets_elements._tx (co_members co) = OK (0, Full)
  | None => False
  end.
Proof. vm_compute; reflexivity. Qed.

Lemma elements_tx_version_field :
  match (Clight.genv_cenv elements_ge)!jets_elements._elementsTransaction with
  | Some co => field_offset (Clight.genv_cenv elements_ge) jets_elements._version (co_members co) = OK (720, Full)
  | None => False
  end.
Proof. vm_compute; reflexivity. Qed.

Lemma elements_tx_lockTime_field :
  match (Clight.genv_cenv elements_ge)!jets_elements._elementsTransaction with
  | Some co => field_offset (Clight.genv_cenv elements_ge) jets_elements._lockTime (co_members co) = OK (728, Full)
  | None => False
  end.
Proof. vm_compute; reflexivity. Qed.
