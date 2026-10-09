(** Derive the complete original helper call directly from initial owned fields. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Integers Values Memory Clight ClightBigstep Events.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv.
Require Import C.jet_secp_field_add C.jet_secp_field_add_initial C.jet_secp_field_add_storage.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_field_add_owned m a b rho :
  a <> b ->
  fe_at m a 0 (field_values rho 1) -> fe_at m b 0 (field_values rho 6) ->
  Mem.range_perm m a 0 40 Cur Freeable -> Mem.range_perm m b 0 40 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add)
      [Vptr a Ptrofs.zero; Vptr b Ptrofs.zero] E0 mf Vundef /\
    fe_at mf a 0 (add_values rho) /\
    Mem.range_perm mf a 0 40 Cur Freeable /\
    Mem.range_perm mf b 0 40 Cur Freeable /\
    lframe (fun b' pos => ~ foot [(a,0);(b,0)]
      (map rshape field_add_initial_regs) b' pos) m mf.
Proof.
  intros HSeparate HA HB HFreeA HFreeB.
  apply eval_field_add_to_field.
  apply field_add_initial_from_owned_fields; assumption.
Qed.
Print Assumptions eval_field_add_owned.
