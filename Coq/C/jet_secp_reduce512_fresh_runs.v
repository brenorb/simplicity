(** Execute the original reduction stages with an uninitialized destination.
    The first two stages do not read it; the third overwrites all four limbs.
    Their arithmetic expressions and checkpoint temporaries are unchanged. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Maps Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem
 C.jet_sx_compact C.jet_sx_forget_cells C.jet_secp_linkage C.jets_secp
 C.jet_secp_shift64_executor C.jet_secp_scalar_reduce512_run
 C.jet_secp_reduce512_first_run C.jet_secp_reduce512_typed_stage
 C.jet_secp_reduce512_two_stages C.jet_secp_reduce512_third_stage
 C.jet_secp_reduce512_first_symbolic C.jet_secp_scalar_mul512_symbolic.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition reduce512_forget_destination (regs:list region) := match regs with
 | []=>[] | h::t=>forget_region h::t end.
Definition reduce512_freshen (st:sstate) := mkst (stemps st)
 (reduce512_forget_destination (sregs st)) (slog st) (snv st).
Definition reduce512_fresh_initial_regs := reduce512_forget_destination scalar_reduce512_initial_regs.
Definition reduce512_fresh_first := reduce512_freshen reduce512_first_initial.
Definition reduce512_fresh_first_computation := compact_stmt (genv_cenv secp_ge) []
 secp_shift64_table 300 (snd reduce512_allocated) reduce512_fresh_first reduce512_first_prefix.
Lemma reduce512_fresh_first_completes :
 match reduce512_fresh_first_computation with Some (RDone _ ONormal)=>true|_=>false end=true.
Proof. timeout 10 (vm_compute;reflexivity). Qed.
Definition reduce512_fresh_first_state := match reduce512_fresh_first_computation with
 | Some (RDone st _)=>st|_=>reduce512_fresh_first end.
Definition reduce512_fresh_second digits m6 := reduce512_freshen (reduce512_typed_stage_initial digits m6).
Definition reduce512_fresh_second_state digits m6 := reduce512_freshen (reduce512_typed_stage_state digits m6).
Definition reduce512_fresh_third digits p4 := reduce512_freshen (reduce512_third_initial digits p4).

Lemma reduce512_forget_destination_shape regs :
 map rshape (reduce512_forget_destination regs)=map rshape regs.
Proof. destruct regs;[reflexivity|cbn [reduce512_forget_destination map];rewrite forget_region_shape;reflexivity]. Qed.
Lemma reduce512_fresh_shape st : map rshape (sregs (reduce512_freshen st))=map rshape (sregs st).
Proof. apply reduce512_forget_destination_shape. Qed.
Lemma reduce512_fresh_entry_regs : sregs reduce512_fresh_first=
 reduce512_fresh_initial_regs++fst reduce512_allocated.
Proof. reflexivity. Qed.
Lemma reduce512_fresh_first_run :
 compact_stmt (genv_cenv secp_ge) [] secp_shift64_table 300 (snd reduce512_allocated)
 reduce512_fresh_first reduce512_first_prefix=Some (RDone reduce512_fresh_first_state ONormal).
Proof.
 pose proof reduce512_fresh_first_completes as Complete.
 change (reduce512_fresh_first_computation=Some (RDone reduce512_fresh_first_state ONormal)).
 unfold reduce512_fresh_first_state;destruct reduce512_fresh_first_computation as [result|];[|discriminate].
 destruct result;[destruct o;try discriminate;reflexivity|discriminate].
Qed.
Lemma reduce512_fresh_first_stack : forget_after 2 (sregs reduce512_fresh_first_state)=
 reduce512_fresh_initial_regs++fst reduce512_allocated.
Proof. timeout 10 (vm_compute;reflexivity). Qed.
Lemma reduce512_fresh_first_sources :
 (stemps reduce512_fresh_first_state)!_r=Some (XP 0 0) /\
 (stemps reduce512_fresh_first_state)!_l=Some (XP 1 0) /\
 (stemps reduce512_fresh_first_state)!_m0=Some (sc_lo first_sy0) /\
 (stemps reduce512_fresh_first_state)!_m1=Some (sc_lo first_sy1) /\
 (stemps reduce512_fresh_first_state)!_m2=Some (sc_lo first_sy2) /\
 (stemps reduce512_fresh_first_state)!_m3=Some (sc_lo first_sy3) /\
 (stemps reduce512_fresh_first_state)!_m4=Some (sc_lo first_sy4) /\
 (stemps reduce512_fresh_first_state)!_m5=Some (sc_lo first_sy5) /\
 (stemps reduce512_fresh_first_state)!_m6=Some (XL2I (sc_hi first_sy5)).
Proof. repeat split;timeout 10 reflexivity. Qed.
Lemma reduce512_fresh_second_run digits m6 :
 compact_stmt (genv_cenv secp_ge) [] secp_shift64_table 300 (snd reduce512_allocated)
 (reduce512_fresh_second digits m6) reduce512_typed_stage=
 Some (RDone (reduce512_fresh_second_state digits m6) ONormal).
Proof. timeout 10 (vm_compute;reflexivity). Qed.
Lemma reduce512_fresh_second_stack digits m6 :
 forget_after 2 (sregs (reduce512_fresh_second_state digits m6))=
 reduce512_fresh_initial_regs++fst reduce512_allocated.
Proof. timeout 10 (vm_compute;reflexivity). Qed.
Lemma reduce512_fresh_third_run digits p4 :
 compact_stmt (genv_cenv secp_ge) [] secp_shift64_table 300 (snd reduce512_allocated)
 (reduce512_fresh_third digits p4) reduce512_third_stage=
 Some (RDone (reduce512_third_state digits p4) ONormal).
Proof. timeout 10 (vm_compute;reflexivity). Qed.
