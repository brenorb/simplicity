(** Numeric storage interfaces for the original in-place scalar calls used by
    split_lambda. Execution, arithmetic and serialization proofs are reused. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_writer_run C.jet_secp_scalar_writer_storage
 C.jet_secp_scalar_negate_canonical C.jet_secp_scalar_negate_storage C.jet_secp_scalar_overflow_numeric
 C.jet_secp_scalar_mul512_low C.jet_secp_scalar_mul512_accumulate
 C.jet_secp_scalar_borrowed_inputs C.jet_secp_scalar_mul_reader_bridge
 C.jet_secp_scalar_mul_borrowed_alloc C.jet_secp_scalar_mul_borrowed_observed
 C.jet_secp_scalar_mul_caller_observed C.jet_secp_scalar_mul_writer_bridge
 C.jet_secp_scalar_mul_separate_support C.jet_secp_scalar_add_run C.jet_secp_scalar_add_exec
 C.jet_secp_scalar_add_initial C.jet_secp_scalar_add_reader_environment
 C.jet_secp_scalar_add_numeric C.jet_secp_scalar_add_numeric_exec C.jet_secp_scalar_add_storage
 C.jet_secp_scalar_add_reduced C.jet_secp_scalar_add_separate C.jet_secp_slice_permissions
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem eval_scalar_mul_inplace_values a b m ba bb : 0<=a<2^256 -> 0<=b<2^256 -> ba<>bb ->
 scalar_at m ba 0 (map Int64.repr (scalar_limbs_of a)) ->
 scalar_at m bb 0 (map Int64.repr (scalar_limbs_of b)) -> Mem.range_perm m ba 0 32 Cur Freeable ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul)
 [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf ba 0 (map Int64.repr (scalar_limbs_of ((a*b) mod canonical_group_order))) /\
 Mem.range_perm mf ba 0 32 Cur Freeable /\ keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun block _=>block<>ba /\ block<>bb) m mf.
Proof.
 intros A B Separate StoredA StoredB Free.
 pose proof (scalar_borrowed_inputs_from_storage a b m ba bb StoredA StoredB Free Separate) as Inputs.
 destruct (eval_scalar_mul_borrowed_inplace_observed (scalar_mul_reader_rho a b) [(ba,0);(bb,0)] m Inputs)
  as (mf & Call & Loads & Value & Output & RHS & Frame).
 destruct (scalar_mul_reader_input_values a b A B) as [VA VB];rewrite VA,VB in Value.
 destruct (scalar_mul_output_owned _ _ _ Output) as [_ FreeF].
 assert (Stored:scalar_at mf ba 0 (map Int64.repr (scalar_limbs_of ((a*b) mod canonical_group_order)))).
 { rewrite <-Value;apply four_words_scalar_at;[apply scalar_mul_caller_word_count|exact FreeF|exact Loads]. }
 exists mf;split;[exact Call|];split;[exact Stored|];split;[exact FreeF|];split.
 - eapply secp_internal_keeps_permissions;[exact scalar_mul_separate_closed|reflexivity|exact Call].
 - split;[eapply (secp_closed_function_preserved f_secp256k1_scalar_mul);
   [exact scalar_mul_separate_closed|reflexivity|exact Call]|].
   eapply lframe_implies;[exact Frame|];intros block ofs [NotA NotB] Valid.
   intros (r & sh & d & ch & Nth & Cell & Eq & Bytes);destruct r as [|[|r]].
   + apply NotA;exact Eq.
   + apply NotB;exact Eq.
   + cbn [scalar_mul_borrowed_inputs map nth_error] in Nth;destruct r;discriminate.
Qed.

Lemma scalar_negate_closed : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_scalar_negate)=true.
Proof. timeout 10 (vm_compute;reflexivity). Qed.

Theorem eval_scalar_negate_value a m ba : 0<=a<canonical_group_order ->
 scalar_at m ba 0 (map Int64.repr (scalar_limbs_of a)) -> Mem.range_perm m ba 0 32 Cur Freeable ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_negate)
 [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf ba 0 (map Int64.repr (scalar_limbs_of ((-a) mod canonical_group_order))) /\
 Mem.range_perm mf ba 0 32 Cur Freeable /\ keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun block _=>block<>ba) m mf.
Proof.
 intros A Stored Free;pose proof (scalar_writer_initial_rep_from_storage a m ba Stored Free) as Input.
 destruct canonical_group_order_range as [[Positive Limit] _];change (canonical_group_order<2^256) in Limit.
 assert (Value:scalar_limb_value (scalar_limb_rho a)=a) by (apply scalar_limb_rho_value;lia).
 destruct (eval_scalar_negate_numeric_owned (scalar_limb_rho a) [(ba,0)] m Input ltac:(rewrite Value;exact A))
  as (mf & Call & Output & FreeF & Frame).
 rewrite Value in Output.
 exists mf;split;[exact Call|];split;[exact Output|];split;[exact FreeF|];split.
 - eapply secp_internal_keeps_permissions;[exact scalar_negate_closed|reflexivity|exact Call].
 - split;[eapply (secp_closed_function_preserved f_secp256k1_scalar_negate);
   [exact scalar_negate_closed|reflexivity|exact Call]|].
   eapply lframe_implies;[exact Frame|];intros block ofs NotA Valid.
   intros (r & sh & d & ch & Nth & Cell & Eq & Bytes);destruct r as [|r].
   + apply NotA;exact Eq.
   + cbn [scalar_writer_initial_regs map nth_error] in Nth;destruct r;discriminate.
Qed.

Theorem eval_scalar_add_inplace_values a b m ba bb :
 0<=a<canonical_group_order -> 0<=b<canonical_group_order -> ba<>bb ->
 scalar_at m ba 0 (map Int64.repr (scalar_limbs_of a)) ->
 scalar_at m bb 0 (map Int64.repr (scalar_limbs_of b)) ->
 Mem.range_perm m ba 0 32 Cur Freeable -> Mem.range_perm m bb 0 32 Cur Freeable ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_add)
 [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf
 (Vint (b2i (Z.leb canonical_group_order (a+b)))) /\
 scalar_at mf ba 0 (map Int64.repr (scalar_limbs_of ((a+b) mod canonical_group_order))) /\
 scalar_at mf bb 0 (map Int64.repr (scalar_limbs_of b)) /\
 Mem.range_perm mf ba 0 32 Cur Freeable /\ Mem.range_perm mf bb 0 32 Cur Freeable /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (fun block _=>block<>ba /\ block<>bb) m mf.
Proof.
 intros A B Separate StoredA StoredB FA FB.
 destruct canonical_group_order_range as [[Positive Limit] _];change (canonical_group_order<2^256) in Limit.
 destruct (scalar_add_reader_weighted_values a b ltac:(lia) ltac:(lia)) as [VA VB].
 assert (Value:scalar_add_input_value (scalar_add_reader_rho a b)=a+b)
  by (unfold scalar_add_input_value;rewrite VA,VB;reflexivity).
 pose proof (scalar_add_initial_from_owned_scalars m ba bb (scalar_add_reader_rho a b) Separate
  ltac:(rewrite scalar_add_reader_values_first;exact StoredA)
  ltac:(rewrite scalar_add_reader_values_second;exact StoredB) FA FB) as Input.
 destruct (eval_scalar_add_mod_group_owned (scalar_add_reader_rho a b) [(ba,0);(bb,0)] m Input
  ltac:(rewrite Value;lia)) as (mf & Call & Output & OwnA & OwnB & Loads & Numeric & Frame).
 rewrite Value in Call.
 destruct (scalar_add_output_scalar_at _ _ _ Output) as [Stored [FreeA FreeB]].
 rewrite Numeric,Value in Stored.
 assert (StoredBF:scalar_at mf bb 0 (map Int64.repr (scalar_limbs_of b))).
 { rewrite <- (scalar_add_reader_values_second a b).
   apply (scalar_add_region_storage (scalar_add_reader_rho a b) [(ba,0);(bb,0)] mf 1 4 eq_refl).
   exact (rep_region _ _ _ _ 1 _ Output eq_refl). }
 exists mf;split;[exact Call|];split;[exact Stored|];split;[exact StoredBF|];split;[exact FreeA|];
 split;[exact FreeB|];split.
 - eapply secp_internal_keeps_permissions;[exact scalar_add_closed|reflexivity|exact Call].
 - split;[eapply (secp_closed_function_preserved f_secp256k1_scalar_add);
   [exact scalar_add_closed|reflexivity|exact Call]|].
   eapply lframe_implies;[exact Frame|];intros block ofs [NotA NotB] Valid.
   intros (r & sh & d & ch & Nth & Cell & Eq & Bytes);destruct r as [|[|r]].
   + apply NotA;exact Eq.
   + apply NotB;exact Eq.
   + cbn [scalar_add_initial_regs map nth_error] in Nth;destruct r;discriminate.
Qed.
