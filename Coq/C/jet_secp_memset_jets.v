(** Public secp jets whose only remaining dependency was the original wNAF
    [memset] call. Each theorem is the existing full initialized local
    contract, conditional on the explicit [memset_model] premise for the
    abstract libc call (see [jet_memset_model]); a conditional result,
    reported as such in coverage, like [memcpy_model]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout
  C.jet_frame_inv C.jet_encoding C.jet_secp_frame C.jet_secp_linkage
  C.jet_memset_model C.jets_secp C.jet_secp_initialized_contract
  C.jet_secp_generate_program C.jet_secp_generator_startup C.jet_secp_generate_local
  C.jet_secp_wnaf_memset.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem generate_initialized_local_spec :
  memset_model ->
  secp_jet_initialized_local_spec generator_startup f_simplicity_generate Word256
    (Ty.Prod (Ty.Prod Word256 Word256) Word256) (@literal_generate Alg.CoreFunSem).
Proof.
  intro Model;apply generate_initialized_local_spec_from_memset_steps;exact (generate_memset_steps Model).
Qed.

(** Every input runs from the original program's actual initial memory. *)
Theorem generate_runs_from_actual_init_memset (Model:memset_model) (value:Ty.tySem Word256) envv :
  exists mi m bd bs bi bw edge mf,
    Genv.init_mem jets_secp.prog=Some mi /\ generator_startup mi /\ generator_startup m /\
    frame_fields_at m bs 0 bi edge 0 /\ frame_input_cells_at m bi edge 0 (encode value) /\
    write_frame_at m bd 0 bw 0 768 768 /\
    Clight2.eval_funcall secp_ge m (Internal f_simplicity_generate)
      [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero;envv] E0 mf (Vint Int.one) /\
    finv m bd 0 bw 0 768 768 bi mf true (encode (@literal_generate Alg.CoreFunSem value)) /\
    generator_startup mf /\
    (forall b chunk ofs,Mem.valid_block mi b -> Mem.load chunk mf b ofs=Mem.load chunk mi b ofs).
Proof. exact (generate_runs_from_actual_init value envv (generate_memset_steps Model)). Qed.
