(** Actual linked initialization of SHA's dispatch cell and readonly counter. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight Globalenvs Memory Values.
Require Import C.jet_elements_taptweak_program C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_startup C.jet_sha_initial_globals C.jet_sha_uchars_exec.
Require Import C.jet_sha_global_state.
Require C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition elements_taptweak_symbol_block id:=
 match Genv.find_symbol elements_taptweak_ge id with Some b=>b|None=>1%positive end.
Definition elements_taptweak_sha_dispatch_block:=elements_taptweak_symbol_block jets_secp._simplicity_sha256_compression.
Definition elements_taptweak_sha_counter_block:=elements_taptweak_symbol_block jets_secp._sha256_max_counter.
Definition elements_taptweak_sha_compression_block:=elements_taptweak_symbol_block jets_secp._sha256_compression_portable.
Definition elements_taptweak_sha_startup:=sha_global_state_at
 elements_taptweak_sha_dispatch_block elements_taptweak_sha_compression_block elements_taptweak_sha_counter_block.
Lemma elements_taptweak_sha_dispatch_info:
 Genv.find_var_info (Genv.globalenv elements_taptweak_linked_program)
 elements_taptweak_sha_dispatch_block=Some jets_secp.v_simplicity_sha256_compression.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_sha_counter_info:
 Genv.find_var_info (Genv.globalenv elements_taptweak_linked_program)
 elements_taptweak_sha_counter_block=Some jets_secp.v_sha256_max_counter.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_sha_compression_symbol:
 Genv.find_symbol (Genv.globalenv elements_taptweak_linked_program) jets_secp._sha256_compression_portable=
 Some elements_taptweak_sha_compression_block.
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge elements_taptweak_linked_program
 elements_taptweak_sha_dispatch_block elements_taptweak_sha_counter_block elements_taptweak_sha_compression_block.
Theorem elements_taptweak_sha_startup_initial m:
 Genv.init_mem elements_taptweak_linked_program=Some m ->elements_taptweak_sha_startup m.
Proof.
 intro Init.
 destruct (Genv.init_mem_characterization elements_taptweak_linked_program _ elements_taptweak_sha_counter_info Init)
 as (_ & CounterBounds & CounterLoad & _).
 destruct (Genv.init_mem_characterization elements_taptweak_linked_program _ elements_taptweak_sha_dispatch_info Init)
 as (_ & DispatchBounds & _).
 split.
 - split.
   + exact (@scalar_pointer_global_initialized Clight.fundef type elements_taptweak_linked_program
     elements_taptweak_sha_dispatch_block (gvar_info jets_secp.v_simplicity_sha256_compression)
     jets_secp._sha256_compression_portable elements_taptweak_sha_compression_block Ptrofs.zero m false
     elements_taptweak_sha_dispatch_info elements_taptweak_sha_compression_symbol Init).
   + exact (proj1 (CounterLoad eq_refl)).
 - split.
   + intros ofs Perm;pose proof (proj2 (CounterBounds ofs Max Writable Perm)) as Order.
     change (perm_order Readable Writable) in Order;inversion Order.
   + intros ofs Perm;pose proof (proj2 (DispatchBounds ofs Max Freeable Perm)) as Order.
     change (perm_order Writable Freeable) in Order;inversion Order.
Qed.
Theorem elements_taptweak_sha_startup_exists:
 exists m,Genv.init_mem elements_taptweak_linked_program=Some m /\elements_taptweak_sha_startup m.
Proof.
 destruct elements_taptweak_initial_memory_exists as [m Init].
 exists m;split;[exact Init|exact (elements_taptweak_sha_startup_initial m Init)].
Qed.

Definition elements_taptweak_sha_startup_separate:=sha_global_state_separate
 elements_taptweak_sha_dispatch_block elements_taptweak_sha_compression_block elements_taptweak_sha_counter_block.
Definition elements_taptweak_sha_startup_preserved:=sha_global_state_preserved
 elements_taptweak_sha_dispatch_block elements_taptweak_sha_compression_block elements_taptweak_sha_counter_block.
