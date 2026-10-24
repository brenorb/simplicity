(** Interpret the original inverse finishing path against the literal
    inverse program. The outer loop must still establish the terminal
    trajectory, bounds/link and the zero-input coefficient invariant. *)
From Coq Require Import ZArith Znumtheory List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg.
Require Import C.jet_secp_modinv_var_tail C.jet_secp_modinv_var_invariant C.jet_secp_modinv_var_seed.
Require Import C.jet_secp_modinv_var_finish C.jet_secp_modinv_var_free C.jet_secp_modinv_normalize62_words.
Require Import C.jet_secp_modinv_normalize62_exec C.jet_secp_modinv_de_numeric C.jet_secp_modinfo_fe_global.
Require Import C.jet_secp_modinv_de_correction_numeric.
Require Import C.jet_secp_signed62_numeric C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_invert_literal C.jet_secp_invert_modinv C.modinv C.divstep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma inv_active_negative_top n w :
  (forall i,(i<n)%nat -> 0<=w i<2^62) ->
  (norm62_value_z n w<0 <-> w n<0).
Proof.
  induction n as [|n IH] in w|-*;intro Low;[reflexivity|].
  pose proof (Low 0%nat ltac:(lia)) as Head.
  specialize (IH (fun i=>w (S i)) ltac:(intros i I;apply Low;lia)).
  cbn [norm62_value_z];rewrite <-IH;lia.
Qed.

Lemma inv_finish_abs_value len rho : (0<len<=5)%nat -> inv_tail_low_bounds len rho ->
  (if Int64.lt (inv_finish_sign len rho) Int64.zero then -1 else 1)*
    inv_fg_active_value len rho false=Z.abs (inv_fg_active_value len rho false).
Proof.
  intros Len Low.
  pose proof (inv_active_negative_top (len-1)
    (fun i=>Int64.signed (rho (15+i)%nat)) ltac:(intros i I;apply (Low false i);lia)) as Sign.
  change (inv_fg_active_value len rho false<0 <-> Int64.signed (inv_finish_sign len rho)<0) in Sign.
  unfold Int64.lt;rewrite Int64.signed_zero.
  destruct (zlt (Int64.signed (inv_finish_sign len rho)) 0) as [Negative|Nonnegative].
  - rewrite Z.abs_neq by (pose proof (proj2 Sign Negative);lia);ring.
  - rewrite Z.abs_eq by (destruct (Z_lt_ge_dec (inv_fg_active_value len rho false) 0)
      as [NegValue|NonnegValue];[apply Sign in NegValue;lia|lia]);ring.
Qed.

Lemma inv_terminal_unit st n : Z.gcd (f st) (g st)=1 ->
  g (fst (stepN n st))=0 -> Z.abs (f (fst (stepN n st)))=1.
Proof.
  intros Coprime Zero.
  pose proof (Zgcd_is_gcd (f st) (g st)) as Initial;rewrite Coprime in Initial.
  pose proof (C.divstep.gcd st 1 n Initial) as Final.
  pose proof (Zis_gcd_gcd _ _ 1 ltac:(lia) Final) as Gcd.
  rewrite Zero,Z.gcd_0_r in Gcd;exact Gcd.
Qed.

Lemma inv_field_terminal_unit value n : 0<value<feP ->
  g (fst (stepN n (init feP value inv_seed_modulus_odd)))=0 ->
  Z.abs (f (fst (stepN n (init feP value inv_seed_modulus_odd))))=1.
Proof.
  intros Range Zero;apply inv_terminal_unit;[|exact Zero].
  change (Z.gcd feP value=1);apply field_gcd_nonmultiple;lia.
Qed.

Lemma inv_finish_unit_inverse value len rho : (0<len<=5)%nat -> inv_tail_low_bounds len rho ->
  inv_coefficient_link value len rho -> Z.abs (inv_fg_active_value len rho false)=1 ->
  ((if Int64.lt (inv_finish_sign len rho) Int64.zero then -1 else 1)*
    de62_input_value (inv_de_rho rho) false) mod feP=modInv value feP.
Proof.
  intros Len Low Link Unit;apply modInv_mul_unique_l.
  replace (((if Int64.lt (inv_finish_sign len rho) Int64.zero then -1 else 1)*
    de62_input_value (inv_de_rho rho) false)*value) with
    ((if Int64.lt (inv_finish_sign len rho) Int64.zero then -1 else 1)*
      (value*de62_input_value (inv_de_rho rho) false)) by ring.
  rewrite <-Zmult_mod_idemp_r,(Link false),Zmult_mod_idemp_r.
  rewrite inv_finish_abs_value by assumption;rewrite Unit;apply Z.mod_small;unfold feP,feR;lia.
Qed.

Lemma inv_finish_zero_inverse len rho : de62_input_value (inv_de_rho rho) false mod feP=0 ->
  ((if Int64.lt (inv_finish_sign len rho) Int64.zero then -1 else 1)*
    de62_input_value (inv_de_rho rho) false) mod feP=modInv 0 feP.
Proof.
  intro Zero;rewrite <-Zmult_mod_idemp_r,Zero,Z.mul_0_r,Zmod_0_l,modInv_zero;reflexivity.
Qed.

Lemma inv_terminal_literal_coefficient value n len rho : 0<=value<feP ->
  (0<len<=5)%nat -> inv_tail_low_bounds len rho -> inv_coefficient_link value len rho ->
  inv_state_matches len rho (fst (stepN n (init feP value inv_seed_modulus_odd))) ->
  g (fst (stepN n (init feP value inv_seed_modulus_odd)))=0 ->
  (value=0 -> de62_input_value (inv_de_rho rho) false mod feP=0) ->
  ((if Int64.lt (inv_finish_sign len rho) Int64.zero then -1 else 1)*
    de62_input_value (inv_de_rho rho) false) mod feP=literal_invert_numeric value.
Proof.
  intros Range Len Low Link (F & G) Stop Zero.
  rewrite literal_invert_numeric_modInv by (unfold feP,feR in *;lia).
  destruct (Z.eq_dec value 0) as [Eq|Ne].
  - subst value;apply inv_finish_zero_inverse;apply Zero;reflexivity.
  - apply inv_finish_unit_inverse;[exact Len|exact Low|exact Link|].
    rewrite <-F;apply inv_field_terminal_unit;[lia|exact Stop].
Qed.

(** The C caller canonically normalizes its input before packing signed62.
    Retain the literal result for the original word, including word feP. *)
Lemma inv_literal_after_canonical_input raw : 0<=raw<2^256 ->
  literal_invert_numeric (raw mod feP)=literal_invert_numeric raw.
Proof.
  intro Range.
  assert (Normalized : 0<=raw mod feP<2^256).
  { pose proof (Z.mod_pos_bound raw feP ltac:(unfold feP,feR;lia));unfold feP,feR in *;lia. }
  rewrite (literal_invert_numeric_modInv raw Range),
    (literal_invert_numeric_modInv (raw mod feP) Normalized).
  apply modInv_eqm;unfold eqm;rewrite Z.mod_mod by exact inv_field_modulus_nonzero;reflexivity.
Qed.

Theorem exec_inv_finish_literal value n len rho beta e le m :
  (0<len<=5)%nat -> rep rho beta inv_loop_regs m -> ematch beta (snd inv_start_alloc) e ->
  blk beta 1=modinfo_fe_block -> bas beta 1=0 ->
  le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
  le!_modinfo=Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
  le!_x=Some (Vptr (blk beta 0) Ptrofs.zero) -> de62_state_bounds (inv_de_rho rho) ->
  0<=value<feP -> inv_tail_low_bounds len rho -> inv_coefficient_link value len rho ->
  inv_state_matches len rho (fst (stepN n (init feP value inv_seed_modulus_odd))) ->
  g (fst (stepN n (init feP value inv_seed_modulus_odd)))=0 ->
  (value=0 -> de62_input_value (inv_de_rho rho) false mod feP=0) -> exists mf mr,
  Clight2.exec_stmt secp_ge e le m inv_finish E0 (inv_finish_temps len rho le) mf Out_normal /\
  Mem.free_list mf (blocks_of_env secp_ge e)=Some mr /\
  fe_at mr (blk beta 0) 0 (words5 (inv_finish_words len rho)) /\
  signed62_normalized (inv_finish_words len rho) /\
  signed62_unsigned_value (inv_finish_words len rho)=literal_invert_numeric value /\
  (forall raw,0<=raw<2^256 -> value=raw mod feP ->
    signed62_unsigned_value (inv_finish_words len rho)=literal_invert_numeric raw) /\
  Mem.range_perm mr (blk beta 0) 0 40 Cur Freeable /\ modinfo_fe_global_rep mr /\
  lframe (fun b ofs=>norm62_outside (blk beta 2) modinfo_fe_block b ofs /\ b<>blk beta 0 /\
    inv_free_outside beta b) m mr.
Proof.
  intros Len Rep Env Block Base Length Modinfo X Bounds Range Low Link State Stop Zero.
  destruct (exec_inv_finish_and_free len rho beta e le m Len Rep Env Block Base Length Modinfo X Bounds)
    as (mf & mr & Run & Free & Out & Normalized & Numeric & Owned & Global & Frame).
  rewrite (inv_terminal_literal_coefficient value n len rho Range Len Low Link State Stop Zero) in Numeric.
  assert (Original : forall raw,0<=raw<2^256 -> value=raw mod feP ->
    signed62_unsigned_value (inv_finish_words len rho)=literal_invert_numeric raw).
  { intros raw Raw Eq;rewrite Numeric,Eq;apply inv_literal_after_canonical_input;exact Raw. }
  exists mf,mr;repeat first [assumption|split].
Qed.

(** The zero case cannot be obtained from the coefficient link alone.
    Establish its additional invariant at the actual initializer, and retain
    it across the exact coefficient equation supplied by the C update proof. *)
Lemma inv_seed_coefficient_zero w :
  de62_input_value (inv_de_rho (inv_seed_rho w)) false mod feP=0.
Proof. rewrite inv_seed_de_value,Zmod_0_l;reflexivity. Qed.

Lemma inv_trajectory_zero_coefficient value n len rho :
  inv_matrix_matches rho (fst (stepN n (init feP value inv_seed_modulus_odd))) ->
  2^62*de62_input_value (inv_de_rho (inv_iteration_rho len rho)) false=
    de62_matrix_value (inv_de_rho rho) false+feP*de62_correction_value (inv_de_rho rho) false ->
  (value=0 -> de62_input_value (inv_de_rho rho) false mod feP=0) ->
  (value=0 -> de62_input_value (inv_de_rho (inv_iteration_rho len rho)) false mod feP=0).
Proof.
  intros Matrix Update Zero Eq;subst value.
  rewrite (inv_zero_iteration_coefficient len rho (fst (stepN n (init feP 0 inv_seed_modulus_odd)))
    (fixed_g (init feP 0 inv_seed_modulus_odd) n eq_refl) Matrix Update).
  apply Zero;reflexivity.
Qed.
