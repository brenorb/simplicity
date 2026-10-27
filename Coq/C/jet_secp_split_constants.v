(** Actual static basis constants and lambda used by scalar_split_lambda.
    Their exact initialized words, numeric values and readonly preservation
    are established from the original program, not assumed load oracles. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Globalenvs Memory Values.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_scalar_constant
 C.jet_secp_split_multipliers C.jet_secp_scalar_lambda_global C.jet_secp_canonical_scalar
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_mul512_accumulate C.jet_secp_scalar_mul_writer_bridge
 C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition split_basis_id (first:bool) := if first then _minus_b1 else _minus_b2.
Definition split_basis_var (first:bool) := if first then v_minus_b1 else v_minus_b2.
Definition split_basis_block first := secp_symbol_block (split_basis_id first).
Definition split_basis_words (first:bool) := if first then
 [Int64.repr 8022177200260244675;Int64.repr (-1998614352016537560);Int64.zero;Int64.zero] else
 [Int64.repr (-2925706260434037204);Int64.repr (-8491525256057179027);Int64.repr (-2);Int64.repr (-1)].
Definition split_basis_value (first:bool) := if first then 0xe4437ed6010e88286f547fa90abfe4c3 else
 canonical_group_order-0x3086d221a7d46bcde86c90e49284eb15.
Definition split_basis_state first := scalar_constant_state (split_basis_block first) (split_basis_words first).
Definition split_constants_ready m := split_multipliers_ready m /\
 (forall first,split_basis_state first m) /\ scalar_constant_state scalar_lambda_block scalar_lambda_words m.

Lemma split_basis_symbol first : Genv.find_symbol (Clight.genv_genv secp_ge) (split_basis_id first)=
 Some (split_basis_block first).
Proof. destruct first;reflexivity. Qed.
Lemma split_basis_info first : Genv.find_var_info (Clight.genv_genv secp_ge) (split_basis_block first)=
 Some (split_basis_var first).
Proof. destruct first;reflexivity. Qed.
Lemma split_basis_count first : length (split_basis_words first)=4%nat.
Proof. destruct first;reflexivity. Qed.
Lemma split_basis_value_checked first : column_words_value (split_basis_words first)=split_basis_value first.
Proof. destruct first;vm_compute;reflexivity. Qed.
Lemma split_basis_bounds first : 0<=split_basis_value first<canonical_group_order.
Proof. destruct first;vm_compute;intuition discriminate. Qed.
Lemma split_lambda_bounds : 0<=canonical_lambda_value<canonical_group_order.
Proof. vm_compute;intuition discriminate. Qed.

Local Opaque secp_ge split_basis_block scalar_lambda_block.
Theorem split_constants_initializes m : Genv.init_mem jets_secp.prog=Some m -> split_constants_ready m.
Proof.
 intro Init;split;[apply split_multipliers_initializes;exact Init|];split.
 - intro first;unfold split_basis_state;apply (scalar_constant_initializes (split_basis_var first));
   [apply split_basis_info|apply split_basis_count|destruct first;reflexivity|
    destruct first;reflexivity|destruct first;reflexivity|exact Init].
 - apply (scalar_constant_initializes v_secp256k1_const_lambda);
   [apply scalar_lambda_global_info|apply scalar_lambda_words_count|reflexivity|reflexivity|reflexivity|exact Init].
Qed.
Theorem split_constants_initial_memory : exists m,Genv.init_mem jets_secp.prog=Some m /\ split_constants_ready m.
Proof.
 destruct split_multipliers_initial_memory as (m & Init & Ready);exists m;split;
 [exact Init|apply split_constants_initializes;exact Init].
Qed.
Lemma split_constants_readonly m mf : split_constants_ready m -> readonly_preserved m mf -> split_constants_ready mf.
Proof.
 intros [Multipliers [Basis Lambda]] Preserve;split.
 - eapply split_multipliers_readonly;[exact Multipliers|exact Preserve].
 - split;[intro first;eapply scalar_constant_readonly;[apply Basis|exact Preserve]|
   eapply scalar_constant_readonly;[exact Lambda|exact Preserve]].
Qed.
Lemma split_basis_storage first m : split_constants_ready m ->
 scalar_at m (split_basis_block first) 0 (map Int64.repr (scalar_limbs_of (split_basis_value first))).
Proof.
 intros [_ [Basis _]];rewrite <-(split_basis_value_checked first),four_words_scalar_limbs by apply split_basis_count.
 exact (proj1 (Basis first)).
Qed.
Lemma split_lambda_storage m : split_constants_ready m ->
 scalar_at m scalar_lambda_block 0 (map Int64.repr (scalar_limbs_of canonical_lambda_value)).
Proof.
 intros [_ [_ Lambda]];rewrite <-scalar_lambda_words_value,four_words_scalar_limbs by apply scalar_lambda_words_count.
 exact (proj1 Lambda).
Qed.
Lemma split_basis_separate first m b : split_constants_ready m -> Mem.range_perm m b 0 32 Cur Freeable ->
 b<>split_basis_block first.
Proof. intros [_ [Basis _]] Free;eapply scalar_constant_separate;[apply Basis|exact Free]. Qed.
Lemma split_lambda_separate m b : split_constants_ready m -> Mem.range_perm m b 0 32 Cur Freeable ->
 b<>scalar_lambda_block.
Proof. intros [_ [_ Lambda]] Free;eapply scalar_constant_separate;[exact Lambda|exact Free]. Qed.

(** Values computed by the actual remaining C calls. These definitions do not
    assert a correspondence to the literal signed-half specification. *)
Definition split_product first k := (split_coefficient first k*split_basis_value first) mod canonical_group_order.
Definition split_second_value k := (split_product true k+split_product false k) mod canonical_group_order.
Definition split_lambda_product k := (split_second_value k*canonical_lambda_value) mod canonical_group_order.
Definition split_negated_value k := (-split_lambda_product k) mod canonical_group_order.
Definition split_first_value k := (split_negated_value k+k) mod canonical_group_order.
Lemma split_mod_bound value : 0<=value mod canonical_group_order<canonical_group_order.
Proof. apply Z.mod_pos_bound;pose proof canonical_group_order_range;lia. Qed.
Lemma split_product_bounds first k : 0<=split_product first k<canonical_group_order.
Proof. apply split_mod_bound. Qed.
Lemma split_second_bounds k : 0<=split_second_value k<canonical_group_order.
Proof. apply split_mod_bound. Qed.
Lemma split_lambda_product_bounds k : 0<=split_lambda_product k<canonical_group_order.
Proof. apply split_mod_bound. Qed.
Lemma split_negated_bounds k : 0<=split_negated_value k<canonical_group_order.
Proof. apply split_mod_bound. Qed.
Lemma split_first_bounds k : 0<=split_first_value k<canonical_group_order.
Proof. apply split_mod_bound. Qed.
