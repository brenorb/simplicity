(** Complete distinct-destination scalar addition from actual caller storage.
    The destination contents are unrestricted. Both sources, ownership and
    readonly globals are retained; the existing modular arithmetic is reused. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions
 C.jet_secp_scalar_add_run C.jet_secp_scalar_add_exec C.jet_secp_scalar_add_initial
 C.jet_secp_scalar_add_values C.jet_secp_scalar_add_numeric C.jet_secp_scalar_add_flag
 C.jet_secp_scalar_add_reduced C.jet_secp_scalar_add_storage C.jet_secp_canonical_scalar
 C.jet_secp_scalar_add_reader_environment
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_add_separate_run C.jet_secp_slice_permissions C.jet_secp_closed_helpers
 C.jet_clight_internal_frame C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma scalar_add_separate_cells_ok : cells_sorted 0 scalar_add_separate_cells=true /\
 Forall (fun c=>cofs c+size_chunk (cchunk c)<=32 /\ (align_chunk (cchunk c)|cofs c) /\ cval c=None)
 scalar_add_separate_cells.
Proof.
 split;[reflexivity|];repeat constructor;cbn;try lia;
 first [exists 0;reflexivity|exists 1;reflexivity|exists 2;reflexivity|exists 3;reflexivity].
Qed.

Lemma scalar_add_separate_initial_storage rho m br ba bb : br<>ba -> br<>bb -> ba<>bb ->
 scalar_at m ba 0 (scalar_add_values rho 0) -> scalar_at m bb 0 (scalar_add_values rho 4) ->
 Mem.range_perm m br 0 32 Cur Freeable -> Mem.range_perm m ba 0 32 Cur Freeable ->
 Mem.range_perm m bb 0 32 Cur Freeable ->
 rep rho [(br,0);(ba,0);(bb,0)] scalar_add_separate_initial m.
Proof.
 intros RA RB AB A B FR FA FB.
 assert (R:rep rho [(br,0)] [mkreg scalar_add_separate_cells true (Some 32)] m).
 { apply (rep_snoc rho [] [] m br scalar_add_separate_cells 32);
   [apply rep_nil|cbn;tauto| |exact FR|exact (proj1 scalar_add_separate_cells_ok)|
    exact (proj2 scalar_add_separate_cells_ok)|change (32<=18446744073709551615);lia].
   eapply Mem.perm_valid_block;apply (FR 0);lia. }
 assert (A1:rep rho [(br,0);(ba,0)]
  [mkreg scalar_add_separate_cells true (Some 32);mkreg (u64_cells 0 (scalar_add_vars 0)) true (Some 32)] m).
 { apply (rep_add rho [(br,0)] [mkreg scalar_add_separate_cells true (Some 32)] m ba 0);
   [exact R|cbn;intros [Eq|[]];congruence|apply scalar_add_region_from_values;[reflexivity|exact A|exact FA]]. }
 apply (rep_add rho [(br,0);(ba,0)]
  [mkreg scalar_add_separate_cells true (Some 32);mkreg (u64_cells 0 (scalar_add_vars 0)) true (Some 32)] m bb 0);
 [exact A1|cbn;intros [Eq|[Eq|[]]];congruence|].
 apply scalar_add_region_from_values;[reflexivity|exact B|exact FB].
Qed.

Lemma scalar_add_region_storage rho beta m r start : bas beta r=0 ->
 region_ok rho beta m r (mkreg (u64_cells 0 (scalar_add_vars start)) true (Some 32)) ->
 scalar_at m (blk beta r) 0 (scalar_add_values rho start).
Proof.
 intros Base Region;pose proof Region as (_ & Valid & _ & _ & (_ & _ & Free & _)).
 unfold scalar_at;split;[reflexivity|];split;[lia|];split;[exists 0;lia|];split;
 [change (32<=18446744073709551615);lia|];split.
 - intros pos Range;eapply Mem.perm_implies;[apply Free;exact Range|constructor].
 - intros i word Nth.
   assert (N: nth_error (scalar_add_vars start) i=Some (XLv (start+i)%nat)).
   { destruct i as [|[|[|[|i]]]];try (destruct i;discriminate Nth);
     cbn [scalar_add_vars nth_error];f_equal;f_equal;lia. }
   pose proof (region_load rho beta m r _ _ _ _ Region (u64_cells_nth _ 0 i _ N)) as Load.
   rewrite Base,Z.add_0_l,Z.add_0_l in Load.
   destruct i as [|[|[|[|i]]]];try (destruct i;discriminate Nth);
   injection Nth as <-;cbn [den] in Load;rewrite ?Nat.add_0_r in Load;
   rewrite Z.add_0_l;exact Load.
Qed.

Lemma scalar_add_separate_output_storage rho beta m :
 rep rho beta (sregs scalar_add_separate_state) m ->
 scalar_at m (blk beta 0) 0 (map Int64.repr (scalar_limbs_of (scalar_add_output_value rho (lay beta)))).
Proof.
 intro Rep;rewrite scalar_add_separate_output in Rep.
 destruct (rep_free_region _ _ _ _ 0 32 Rep ltac:(cbn;lia) eq_refl) as [Base Free].
 rewrite <-scalar_add_output_limbs_numeric.
 unfold scalar_at;split;[rewrite map_length;apply scalar_add_limbs_length|];split;[lia|];split;
 [exists 0;lia|];split;[change (32<=18446744073709551615);lia|];split.
 - intros pos Range;eapply Mem.perm_implies;[apply Free;exact Range|constructor].
 - intros i word Nth;rewrite nth_error_map in Nth.
   destruct (nth_error scalar_add_limbs i) as [x|] eqn:X;[|discriminate];injection Nth as <-.
   pose proof (region_load rho beta m 0 _ _ _ _ (rep_region _ _ _ _ 0 _ Rep eq_refl)
    (u64_cells_nth _ 0 i x X)) as Load.
   rewrite Base,Z.add_0_l,Z.add_0_l in Load.
   rewrite Z.add_0_l,Load,den_KL;
   [reflexivity|exact (proj1 (Forall_forall _ _) scalar_add_limbs_long x (nth_error_In _ _ X))].
Qed.

Lemma scalar_add_closed : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_scalar_add)=true.
Proof. timeout 10 (vm_compute;reflexivity). Qed.
Local Opaque secp_ge scalar_add_separate_state.

Theorem eval_scalar_add_separate_owned rho m br ba bb : br<>ba -> br<>bb -> ba<>bb ->
 scalar_at m ba 0 (scalar_add_values rho 0) -> scalar_at m bb 0 (scalar_add_values rho 4) ->
 Mem.range_perm m br 0 32 Cur Freeable -> Mem.range_perm m ba 0 32 Cur Freeable ->
 Mem.range_perm m bb 0 32 Cur Freeable -> 0<=scalar_add_input_value rho<2*canonical_group_order ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_add)
 [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf
 (Vint (b2i (Z.leb canonical_group_order (scalar_add_input_value rho)))) /\
 scalar_at mf br 0 (map Int64.repr (scalar_limbs_of (scalar_add_input_value rho mod canonical_group_order))) /\
 scalar_at mf ba 0 (scalar_add_values rho 0) /\ scalar_at mf bb 0 (scalar_add_values rho 4) /\
 Mem.range_perm mf br 0 32 Cur Freeable /\ Mem.range_perm mf ba 0 32 Cur Freeable /\
 Mem.range_perm mf bb 0 32 Cur Freeable /\ keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun b _=>b<>br /\ b<>ba /\ b<>bb) m mf.
Proof.
 intros RA RB AB A B FR FA FB Range.
 pose proof (scalar_add_separate_initial_storage rho m br ba bb RA RB AB A B FR FA FB) as Initial.
 destruct (eval_scalar_add_separate_regions rho [(br,0);(ba,0);(bb,0)] m Initial)
  as (mf & Call & Final & Frame).
 rewrite scalar_add_flag_exact,scalar_add_flag_reduced in Call by exact Range.
 cbn [ii blk bas lay nth fst snd] in Call.
 pose proof (scalar_add_separate_output_storage _ _ _ Final) as Output.
 rewrite scalar_add_output_mod_group in Output by exact Range.
 rewrite scalar_add_separate_output in Final.
 assert (Keep:keeps_permissions m mf) by
  (eapply secp_internal_keeps_permissions;[exact scalar_add_closed|reflexivity|exact Call]).
 exists mf;split;[exact Call|];split;[exact Output|];split.
 - exact (scalar_add_region_storage rho [(br,0);(ba,0);(bb,0)] mf 1 0 eq_refl
    (rep_region _ _ _ _ 1 _ Final eq_refl)).
 - split.
   + exact (scalar_add_region_storage rho [(br,0);(ba,0);(bb,0)] mf 2 4 eq_refl
      (rep_region _ _ _ _ 2 _ Final eq_refl)).
   + split;[eapply keeps_range_permissions;[exact Keep|exact FR]|];split;
     [eapply keeps_range_permissions;[exact Keep|exact FA]|];split;
     [eapply keeps_range_permissions;[exact Keep|exact FB]|];split;[exact Keep|];split.
     * eapply (secp_closed_function_preserved f_secp256k1_scalar_add);[exact scalar_add_closed|reflexivity|exact Call].
     * eapply lframe_implies;[exact Frame|];intros b ofs (NotR & NotA & NotB) Valid.
       intros (r & sh & d & ch & Nth & Cell & Eq & Bytes);destruct r as [|[|[|r]]].
       -- apply NotR;exact Eq.
       -- apply NotA;exact Eq.
       -- apply NotB;exact Eq.
       -- cbn [scalar_add_separate_initial scalar_add_initial_regs map nth_error] in Nth;destruct r;discriminate.
Qed.

(** Direct numeric interface for the two normalized intermediate products of
    split_lambda. Each source is below n; no destination value is required. *)
Theorem eval_scalar_add_separate_values a b m br ba bb :
 0<=a<canonical_group_order -> 0<=b<canonical_group_order -> br<>ba -> br<>bb -> ba<>bb ->
 scalar_at m ba 0 (map Int64.repr (scalar_limbs_of a)) ->
 scalar_at m bb 0 (map Int64.repr (scalar_limbs_of b)) ->
 Mem.range_perm m br 0 32 Cur Freeable -> Mem.range_perm m ba 0 32 Cur Freeable ->
 Mem.range_perm m bb 0 32 Cur Freeable ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_add)
 [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf
 (Vint (b2i (Z.leb canonical_group_order (a+b)))) /\
 scalar_at mf br 0 (map Int64.repr (scalar_limbs_of ((a+b) mod canonical_group_order))) /\
 scalar_at mf ba 0 (map Int64.repr (scalar_limbs_of a)) /\
 scalar_at mf bb 0 (map Int64.repr (scalar_limbs_of b)) /\
 Mem.range_perm mf br 0 32 Cur Freeable /\ Mem.range_perm mf ba 0 32 Cur Freeable /\
 Mem.range_perm mf bb 0 32 Cur Freeable /\ keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun block _=>block<>br /\ block<>ba /\ block<>bb) m mf.
Proof.
 intros A B RA RB AB StoredA StoredB FR FA FB.
 destruct canonical_group_order_range as [[Positive Limit] _].
 change (canonical_group_order<2^256) in Limit.
 destruct (scalar_add_reader_weighted_values a b ltac:(lia) ltac:(lia)) as [VA VB].
 assert (Value:scalar_add_input_value (scalar_add_reader_rho a b)=a+b)
  by (unfold scalar_add_input_value;rewrite VA,VB;reflexivity).
 pose proof (eval_scalar_add_separate_owned (scalar_add_reader_rho a b) m br ba bb RA RB AB
  ltac:(rewrite scalar_add_reader_values_first;exact StoredA)
  ltac:(rewrite scalar_add_reader_values_second;exact StoredB) FR FA FB ltac:(rewrite Value;lia)) as Run.
 rewrite Value,scalar_add_reader_values_first,scalar_add_reader_values_second in Run;exact Run.
Qed.
