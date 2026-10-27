(** The two original readonly rounding multipliers of scalar_split_lambda.
    Their C initializers and canonical Haskell constants are checked separately. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory Globalenvs Ctypes Clight.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_scalar_constant
 C.jet_secp_scalar_mul512_accumulate C.jet_secp_scalar_lambda_init_exists
 C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition split_multiplier_id (first:bool) := if first then _g1 else _g2.
Definition split_multiplier_var (first:bool) := if first then v_g1 else v_g2.
Definition split_multiplier_block first := secp_symbol_block (split_multiplier_id first).
Definition split_multiplier_words (first:bool) : list int64 := if first then
 [Int64.repr (-1687969588364726223);Int64.repr 4443515802769476223;
  Int64.repr (-1698823648040391915);Int64.repr 3496713202691238861] else
 [Int64.repr 1545214808910233457;Int64.repr 2455034284347819718;
  Int64.repr 8022177200260244676;Int64.repr (-1998614352016537560)].
Definition split_multiplier_value (first:bool) : Z := if first then
 0x3086d221a7d46bcde86c90e49284eb153daa8a1471e8ca7fe893209a45dbb031 else
 0xe4437ed6010e88286f547fa90abfe4c4221208ac9df506c61571b4ae8ac47f71.
Definition split_multiplier_state first := scalar_constant_state (split_multiplier_block first) (split_multiplier_words first).
Definition split_multipliers_ready m := forall first,split_multiplier_state first m.

Lemma split_multiplier_symbol first : Genv.find_symbol (Clight.genv_genv secp_ge) (split_multiplier_id first)=
 Some (split_multiplier_block first).
Proof. destruct first;reflexivity. Qed.
Lemma split_multiplier_info first : Genv.find_var_info (Clight.genv_genv secp_ge) (split_multiplier_block first)=
 Some (split_multiplier_var first).
Proof. destruct first;reflexivity. Qed.
Lemma split_multiplier_count first : length (split_multiplier_words first)=4%nat.
Proof. destruct first;reflexivity. Qed.
Lemma split_multiplier_value_checked first : column_words_value (split_multiplier_words first)=split_multiplier_value first.
Proof. destruct first;vm_compute;reflexivity. Qed.
Lemma split_multiplier_bounds first : 0<=split_multiplier_value first<=2^256-2^128.
Proof. destruct first;vm_compute;intuition discriminate. Qed.

Local Opaque secp_ge split_multiplier_block.
Theorem split_multipliers_initializes m : Genv.init_mem jets_secp.prog=Some m -> split_multipliers_ready m.
Proof.
 intros Init first;unfold split_multiplier_state.
 apply (scalar_constant_initializes (split_multiplier_var first));
 [apply split_multiplier_info|apply split_multiplier_count|destruct first;reflexivity|
  destruct first;reflexivity|destruct first;reflexivity|exact Init].
Qed.
Theorem split_multipliers_initial_memory : exists m,Genv.init_mem jets_secp.prog=Some m /\ split_multipliers_ready m.
Proof. destruct secp_initial_memory_exists as (m & Init);exists m;split;[exact Init|apply split_multipliers_initializes;exact Init]. Qed.
Lemma split_multipliers_readonly m mf : split_multipliers_ready m -> readonly_preserved m mf -> split_multipliers_ready mf.
Proof. intros Ready Preserve first;eapply scalar_constant_readonly;[apply Ready|exact Preserve]. Qed.

Definition split_coefficient first k := (k*split_multiplier_value first+2^383)/2^384.
Lemma rounded_multiplier_small k g : 0<=k<2^256 -> 0<=g<=2^256-2^128 ->
 0<=(k*g+2^383)/2^384<2^128.
Proof. intros K G;split;[apply Z.div_pos;nia|apply Z.div_lt_upper_bound;[lia|nia]]. Qed.
Theorem split_coefficient_bounds first k : 0<=k<2^256 -> 0<=split_coefficient first k<2^128.
Proof. intro Range;apply rounded_multiplier_small;[exact Range|apply split_multiplier_bounds]. Qed.
