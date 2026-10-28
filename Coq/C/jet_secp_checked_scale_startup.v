(** Initialized readonly state for the literal scale caller, established
    from the original program and preserved by actual readers/calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Integers Ctypes Clight ClightBigstep Memory Values Globalenvs.
Require Import C.jets_secp C.jet_sx_mem C.jet_secp_linkage C.jet_clight_forward
 C.jet_clight_internal_preserve C.jet_clight_readonly_frame
 C.jet_secp_strauss_zero_generator C.jet_secp_strauss_scale_main C.jet_secp_strauss_scale_function
 C.jet_secp_scalar_constant C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_reader_support
 C.jet_secp_split_constants C.jet_secp_split_multipliers C.jet_secp_scalar_lambda_global
 C.jet_secp_beta_global C.jet_secp_beta_state.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge beta_block strauss_zero_block.


Require Import C.jet_secp_scale_startup.
Definition checked_zero_block : block := secp_symbol_block _ng__1.
Lemma checked_zero_info : Genv.find_var_info (genv_genv secp_ge) checked_zero_block=Some v_ng.
Proof. vm_compute;reflexivity. Qed.
Local Opaque checked_zero_block.
Theorem checked_zero_initializes m : Genv.init_mem jets_secp.prog=Some m ->
 (zero_scalar_state checked_zero_block) m.
Proof.
 intro Init;pose proof checked_zero_info as Info;rewrite beta_genv_projection in Info.
 destruct (Genv.init_mem_characterization jets_secp.prog _ Info Init) as (Range & Bounds & Loads & Bytes).
 change (Mem.range_perm m checked_zero_block 0 32 Cur Readable) in Range.
 specialize (Loads eq_refl).
 change (Mem.load Mint64 m checked_zero_block 0=Some (Vlong Int64.zero) /\
  Mem.load Mint64 m checked_zero_block 8=Some (Vlong Int64.zero) /\
  Mem.load Mint64 m checked_zero_block 16=Some (Vlong Int64.zero) /\
  Mem.load Mint64 m checked_zero_block 24=Some (Vlong Int64.zero) /\ True) in Loads.
 split.
 - unfold scalar_at;split;[reflexivity|];split;[lia|];split;[exists 0;reflexivity|];split.
   + change (0+32<=18446744073709551615);lia.
   + split;[exact Range|].
     intros i w Nth;destruct i as [|[|[|[|i]]]];cbn [nth_error] in Nth;
      try (destruct i;discriminate Nth);injection Nth as <-;cbn [Z.of_nat Z.mul Z.add];tauto.
 - intros ofs k p;split.
   + intro Perm;exact (Bounds ofs k p Perm).
   + intros (Pos & Order);eapply Mem.perm_implies;[|exact Order].
     destruct k;[apply Mem.perm_cur_max|];apply Range;exact Pos.
Qed.

Lemma checked_zero_exists : exists m,Genv.init_mem jets_secp.prog=Some m /\ zero_scalar_state checked_zero_block m.

Proof. destruct beta_initialized_memory_exists as (m & Init & _);exists m;split;[exact Init|apply checked_zero_initializes;exact Init]. Qed.

Definition checked_scale_startup m := scale_startup_at checked_zero_block m.
Lemma checked_scale_startup_initializes m :
 Genv.init_mem jets_secp.prog=Some m -> checked_scale_startup m.
Proof.
 intro Init;split;[apply checked_zero_initializes;exact Init|];split;
 [apply split_constants_initializes|apply beta_initialized_from_init];exact Init.
Qed.
Lemma checked_scale_startup_exists : exists m,
 Genv.init_mem jets_secp.prog=Some m /\ checked_scale_startup m.
Proof.
 destruct checked_zero_exists as (m & Init & Zero).
 exists m;split;[exact Init|apply checked_scale_startup_initializes;exact Init].
Qed.
