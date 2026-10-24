(** The original scalar inverse loop body after divsteps, including the
    actual stop/shortening control. The matrix correspondence remains an
    incoming obligation of the earlier divstep call, not an execution axiom. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_modinv_loop_modulus C.jet_secp_modinv_tail_modulus C.jet_secp_scalar_inverse_updates
 C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg C.jet_secp_modinv_var_tail
 C.jet_secp_modinv_var_post C.jet_secp_modinv_var_invariant C.jet_secp_modinv_de_numeric
 C.jet_secp_scalar_de_ranges C.jet_secp_scalar_de_invariant C.jet_secp_scalar_de_numeric
 C.jet_secp_scalar_de_exec C.jet_secp_scalar_normalize62 C.jet_secp_modinv_fg_loop_numeric
 C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_body C.jet_secp_canonical_scalar
 C.jet_secp_modinv_fg_start C.jet_secp_modinv_var_ranges C.divstep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_inv_iteration_rho len rho := inv_tail_next_rho len (scalar_inv_updates_rho len rho).
Definition scalar_inv_iteration_length len rho := inv_tail_length len (scalar_inv_updates_rho len rho).
Lemma scalar_inv_tail_de_value len rho high : de62_input_value(inv_de_rho(inv_tail_next_rho len rho)) high=
 de62_input_value(inv_de_rho rho) high.
Proof.
 unfold de62_input_value;apply C.jet_secp_modinv_normalize62_words.norm62_value_ext;
 intros i I;rewrite inv_tail_de_unchanged;reflexivity.
Qed.
Lemma scalar_inv_tail_de_bounds len rho : scalar_de62_state_bounds(inv_de_rho rho) ->
 scalar_de62_state_bounds(inv_de_rho(inv_tail_next_rho len rho)).
Proof.
 intros(Limbs & Values);split.
 - intros high i I;unfold de62_array;rewrite inv_tail_de_unchanged;apply Limbs;exact I.
 - intro high;rewrite scalar_inv_tail_de_value;apply Values.
Qed.

(** Pure range transport, applied below only after the real C execution
    has established NextState. It uses the existing shared f/g and tail
    range lemmas, including the inactive stored limbs. *)
Lemma scalar_inv_iteration_ranges len rho st : (0<len<=5)%nat -> inv_state_matches len rho st ->
 fg_input_bounds(inv_fg_rho len rho) ->
 inv_state_matches (scalar_inv_iteration_length len rho) (scalar_inv_iteration_rho len rho) (fst(stepN 62 st)) ->
 inv_fg_value_capacity len rho -> inv_fg_limb_bounds(scalar_inv_iteration_rho len rho) /\
 inv_fg_value_capacity (scalar_inv_iteration_length len rho) (scalar_inv_iteration_rho len rho).
Proof.
 intros Length State FG NextState Capacity.
 assert(UpdatedLow:inv_tail_low_bounds len (scalar_inv_updates_rho len rho)) by(apply inv_fg_next_low;exact Length).
 assert(AfterValue:forall high,Z.abs(inv_fg_active_value (scalar_inv_iteration_length len rho)
  (scalar_inv_iteration_rho len rho) high)<=2^(62*Z.of_nat len)).
 { assert(Max:Z.max (Z.abs(f st)) (Z.abs(g st))<=2^(62*Z.of_nat len)).
   { apply Z.max_lub;[rewrite(proj1 State)|rewrite(proj2 State)];apply Capacity. }
   destruct(fgBounds st 62) as(FB & GB);intro high;destruct high;
    [rewrite <-(proj2 NextState)|rewrite <-(proj1 NextState)];lia. }
 assert(UpdatedCapacity:inv_fg_value_capacity len (scalar_inv_updates_rho len rho)).
 { intro high;rewrite <-(inv_tail_value_preserved len (scalar_inv_updates_rho len rho) high Length UpdatedLow).
   apply AfterValue. }
 pose proof(inv_fg_next_ranges len (scalar_inv_de_next_rho rho) Length
  (scalar_inv_fg_bounds_after_de len rho FG) UpdatedCapacity) as UpdatedBounds.
 exact(inv_tail_ranges len (scalar_inv_updates_rho len rho) Length UpdatedLow UpdatedBounds UpdatedCapacity).
Qed.

Theorem exec_scalar_inv_after_divsteps value len rho st beta e le m : (0<len<=5)%nat ->
 rep rho beta (inv_mod_loop_regs modinfo_scalar_limb) m -> ematch beta (snd inv_start_alloc) e ->
 le!_modinfo=Some(Vptr(blk beta 1)(Ptrofs.repr(bas beta 1))) -> le!_len=Some(Vint(Int.repr(Z.of_nat len))) ->
 scalar_de62_state_bounds(inv_de_rho rho) -> inv_state_matches len rho st -> inv_matrix_matches rho st ->
 scalar_de62_coefficient_link value (inv_de_rho rho) st ->
 (forall high j,(j<5)%nat -> Z.abs(Int64.signed(fg_array_word(inv_fg_rho len rho) high j))<=2^62) ->
 exists lef mf out,
 Clight2.exec_stmt secp_ge e le m inv_after_divsteps E0 lef mf out /\
 rep (scalar_inv_iteration_rho len rho) beta (inv_mod_loop_regs modinfo_scalar_limb) mf /\
 lef!_len=Some(Vint(Int.repr(Z.of_nat(scalar_inv_iteration_length len rho)))) /\
 scalar_de62_state_bounds(inv_de_rho(scalar_inv_iteration_rho len rho)) /\
 scalar_de62_coefficient_link value (inv_de_rho(scalar_inv_iteration_rho len rho)) (fst(stepN 62 st)) /\
 inv_state_matches (scalar_inv_iteration_length len rho) (scalar_inv_iteration_rho len rho) (fst(stepN 62 st)) /\
 inv_tail_low_bounds (scalar_inv_iteration_length len rho) (scalar_inv_iteration_rho len rho) /\
 (g st=0 -> out=Out_break /\
  de62_input_value(inv_de_rho(scalar_inv_iteration_rho len rho)) false mod canonical_group_order=
   de62_input_value(inv_de_rho rho) false mod canonical_group_order) /\
 (inv_fg_value_capacity len rho -> inv_fg_limb_bounds(scalar_inv_iteration_rho len rho) /\
  inv_fg_value_capacity (scalar_inv_iteration_length len rho) (scalar_inv_iteration_rho len rho)) /\
 (forall high,2^62*de62_input_value(inv_de_rho(scalar_inv_iteration_rho len rho)) high=
   de62_matrix_value(inv_de_rho rho) high+canonical_group_order*scalar_de62_correction_value(inv_de_rho rho) high /\
   (2^62*de62_input_value(inv_de_rho(scalar_inv_iteration_rho len rho)) high-de62_matrix_value(inv_de_rho rho) high) mod canonical_group_order=0) /\
 (forall high,inv_fg_active_value (scalar_inv_iteration_length len rho) (scalar_inv_iteration_rho len rho) high=
   fg_matrix_value(inv_fg_rho len (scalar_inv_de_next_rho rho)) high len/2^62) /\
 (out=Out_break <-> inv_fg_active_value (scalar_inv_iteration_length len rho) (scalar_inv_iteration_rho len rho) true=0) /\
 (out=Out_normal -> inv_fg_active_value (scalar_inv_iteration_length len rho) (scalar_inv_iteration_rho len rho) true<>0) /\
 (out=Out_break \/ out=Out_normal) /\ (0<scalar_inv_iteration_length len rho<=5)%nat /\ inv_post_temp_frame le lef /\
 lframe(fun b ofs=>~foot (inv_de_layout beta) (map rshape scalar_de62_regs) b ofs /\
   ~foot (inv_fg_layout beta) (map rshape fg_regs) b ofs /\ b<>blk beta 4 /\ b<>blk beta 5) m mf.
Proof.
 intros Length Rep Env Modinfo Len Bounds State Matrix Link Limbs.
 destruct(exec_scalar_inv_updates_invariant value len rho st beta e le m Length Rep Env Modinfo Len Bounds State Matrix Link Limbs)
  as(mu & Updates & URep & UBounds & ULink & UState & ULow & UZero & DENumeric & FGNumeric & UFrame).
 destruct(exec_inv_mod_tail modinfo_scalar_limb len (scalar_inv_updates_rho len rho) beta e le mu
  Length URep Env Len ULow) as(lef & mf & out & Tail & Out & NewLength & Values & Low & Stop & Nonzero & Outcomes & Range & TFrame & Frame).
 assert(NextState:inv_state_matches (scalar_inv_iteration_length len rho) (scalar_inv_iteration_rho len rho) (fst(stepN 62 st))).
 { split;unfold scalar_inv_iteration_length,scalar_inv_iteration_rho;rewrite Values;[exact(proj1 UState)|exact(proj2 UState)]. }
 assert(NextLink:scalar_de62_coefficient_link value (inv_de_rho(scalar_inv_iteration_rho len rho)) (fst(stepN 62 st))).
 { intro high;unfold scalar_inv_iteration_rho;rewrite scalar_inv_tail_de_value;apply ULink. }
 assert(Zero:g st=0 -> out=Out_break /\
  de62_input_value(inv_de_rho(scalar_inv_iteration_rho len rho)) false mod canonical_group_order=
   de62_input_value(inv_de_rho rho) false mod canonical_group_order).
 { intro Z;split.
   - apply(proj2 Stop);change(inv_fg_active_value (scalar_inv_iteration_length len rho) (scalar_inv_iteration_rho len rho) true=0).
     rewrite <-(proj2 NextState);apply fixed_g;exact Z.
   - unfold scalar_inv_iteration_rho;rewrite scalar_inv_tail_de_value;apply UZero;exact Z. }
 assert(NextBounds:inv_fg_value_capacity len rho -> inv_fg_limb_bounds(scalar_inv_iteration_rho len rho) /\
  inv_fg_value_capacity (scalar_inv_iteration_length len rho) (scalar_inv_iteration_rho len rho)).
 { exact(scalar_inv_iteration_ranges len rho st Length State (inv_fg_bounds_from_matrix len rho st Matrix Limbs) NextState). }
 exists lef,mf,out;split.
 - eapply exec_inv_updates_then_tail;[exact Updates|exact Tail].
 - split;[exact Out|];split;[exact NewLength|];split;[apply scalar_inv_tail_de_bounds;exact UBounds|];split;[exact NextLink|];
   split;[exact NextState|];split;[exact Low|];split;[exact Zero|];split;[exact NextBounds|];split.
   + intro high;unfold scalar_inv_iteration_rho;rewrite scalar_inv_tail_de_value;exact(DENumeric high).
   + split.
     * intro high;unfold scalar_inv_iteration_length,scalar_inv_iteration_rho;rewrite Values;apply FGNumeric.
     * split;[exact Stop|];split;[exact Nonzero|];split;[exact Outcomes|];split;[exact Range|];split;[exact TFrame|].
       eapply lframe_trans;[eapply lframe_implies;[exact UFrame|]|eapply lframe_implies;[exact Frame|]];
       intros b ofs [DEOutside [FGOutside [FOutside GOutside]]] Valid;tauto.
Qed.
