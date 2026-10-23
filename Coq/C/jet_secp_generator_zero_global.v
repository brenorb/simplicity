(** The original readonly auxiliary scalar used by simplicity_generate.
    This constant is not the jet's arbitrary logical scalar input. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Memory Values Globalenvs Events Maps.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_beta_global.
Require Import C.jet_clight_readonly_frame C.jet_secp_generator_zero_scalar.
Require Import C.jet_secp_scalar_get_b32_storage.
Import ListNotations Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generator_zero_block : block := secp_symbol_block _na.
Definition generator_zero_global_state m :=
 scalar_at m generator_zero_block 0 [Int64.zero;Int64.zero;Int64.zero;Int64.zero] /\
 readonly_region_bounds m generator_zero_block 0 32.

Lemma generator_zero_symbol : Genv.find_symbol (genv_genv secp_ge) _na=Some generator_zero_block.
Proof. vm_compute;reflexivity. Qed.
Lemma generator_zero_info : Genv.find_var_info (genv_genv secp_ge) generator_zero_block=Some v_na.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge generator_zero_block.

Theorem generator_zero_global_initializes m : Genv.init_mem jets_secp.prog=Some m ->
 generator_zero_global_state m.
Proof.
 intro Init;pose proof generator_zero_info as Info;rewrite beta_genv_projection in Info.
 destruct (Genv.init_mem_characterization jets_secp.prog _ Info Init) as (Range & Bounds & Loads & Bytes).
 change (Mem.range_perm m generator_zero_block 0 32 Cur Readable) in Range.
 specialize (Loads eq_refl).
 change (Mem.load Mint64 m generator_zero_block 0=Some (Vlong Int64.zero) /\
  Mem.load Mint64 m generator_zero_block 8=Some (Vlong Int64.zero) /\
  Mem.load Mint64 m generator_zero_block 16=Some (Vlong Int64.zero) /\
  Mem.load Mint64 m generator_zero_block 24=Some (Vlong Int64.zero) /\ True) in Loads.
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

Lemma generator_zero_global_valid m : generator_zero_global_state m ->
 Mem.valid_block m generator_zero_block.
Proof.
 intros ((Length & Base & Align & Hi & Readable & Loads) & Bounds).
 eapply Mem.perm_valid_block;apply (Readable 0);lia.
Qed.

Lemma generator_zero_global_separate m b : generator_zero_global_state m ->
 Mem.perm m b 0 Cur Freeable -> b<>generator_zero_block.
Proof.
 intros (_ & Bounds) Free ->.
 destruct (proj1 (Bounds 0 Cur Freeable) Free) as (_ & Order);inversion Order.
Qed.

Lemma generator_zero_global_unchanged m mf : generator_zero_global_state m ->
 Mem.unchanged_on (fun b _=>b=generator_zero_block) m mf -> generator_zero_global_state mf.
Proof.
 intros State Unchanged;pose proof (generator_zero_global_valid m State) as Valid.
 destruct State as ((Length & Base & Align & Hi & Readable & Loads) & Bounds).
 split.
 - unfold scalar_at;split;[exact Length|];split;[exact Base|];split;[exact Align|];split;[exact Hi|];split.
   + intros pos Range;eapply Mem.perm_unchanged_on;[exact Unchanged|reflexivity|apply Readable;exact Range].
   + intros i w Nth;eapply Mem.load_unchanged_on;
      [exact Unchanged|intros;reflexivity|exact (Loads i w Nth)].
 - intros ofs k p;split.
   + intro Perm;apply (proj1 (Bounds ofs k p)).
     eapply Mem.perm_unchanged_on_2;[exact Unchanged|reflexivity|exact Valid|exact Perm].
   + intro Pos; eapply Mem.perm_unchanged_on;
      [exact Unchanged|reflexivity|apply (proj2 (Bounds ofs k p));exact Pos].
Qed.

Lemma generator_zero_global_alloc m mf lo hi b : generator_zero_global_state m ->
 Mem.alloc m lo hi=(mf,b) -> generator_zero_global_state mf /\ b<>generator_zero_block.
Proof.
 intros State Alloc;pose proof (generator_zero_global_valid m State) as Valid.
 split.
 - eapply generator_zero_global_unchanged;[exact State|].
   eapply Mem.unchanged_on_implies;[eapply Mem.alloc_unchanged_on;exact Alloc|].
   intros block ofs At Old;exact Old.
 - intro E;subst b;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid).
Qed.

Lemma eval_generator_zero_address e le m : e!_na=None ->
 eval_expr secp_ge e le m (Eaddrof (Evar _na (Tstruct __5826 noattr))
  (tptr (Tstruct __5826 noattr))) (Vptr generator_zero_block Ptrofs.zero).
Proof.
 intro Local;apply eval_Eaddrof;apply eval_Evar_global;[exact Local|exact generator_zero_symbol].
Qed.

Theorem eval_generator_scalar_zero_global m : generator_zero_global_state m ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_is_zero)
  [Vptr generator_zero_block Ptrofs.zero] E0 m (Vint Int.one).
Proof. intros (Storage & Bounds);exact (eval_generator_scalar_zero m generator_zero_block 0 Storage). Qed.

Theorem generator_zero_initialized_memory_exists :
 exists m,Genv.init_mem jets_secp.prog=Some m /\ generator_zero_global_state m.
Proof.
 destruct beta_initialized_memory_exists as (m & Init & Beta).
 exists m;split;[exact Init|apply generator_zero_global_initializes;exact Init].
Qed.
