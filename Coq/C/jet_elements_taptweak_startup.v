(** Constructibility for the derived program returned by actual linking. *)
From compcert Require Import AST Ctypes Clight Globalenvs Memory.
Require Import C.jet_elements_taptweak_program C.jet_program_initialization.
Set Default Timeout 10.
Definition elements_taptweak_initialization_okb:=
 program_initialization_okb (Ctypes.program_of_program elements_taptweak_linked_program).
Lemma elements_taptweak_initialization_checked:elements_taptweak_initialization_okb=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_linked_program program_initialization_okb Genv.init_mem.
Theorem elements_taptweak_initial_memory_exists:
 exists m,Genv.init_mem elements_taptweak_linked_program=Some m.
Proof.
 exact (program_initialization_checked (Ctypes.program_of_program elements_taptweak_linked_program)
 elements_taptweak_initialization_checked).
Qed.
