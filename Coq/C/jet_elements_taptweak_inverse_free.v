(** Release the five actual linked inverse locals after normalization/copy. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_de.
Require Import C.jet_secp_modinv_var_finish C.jet_secp_modinv_normalize62_exec C.jet_secp_modinfo_fe_global.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_signed62_numeric C.jet_secp_modinv_de_numeric C.jet_secp_fe_math.
Require Import C.jet_secp_field_read_preservation.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Require Import C.jet_secp_modinv_var_result C.divstep C.jet_secp_modinv_var_invariant C.jet_secp_modinv_var_seed C.jet_secp_modinv_var_tail C.jet_secp_invert_literal C.jet_secp_modinv_var_free C.jet_elements_taptweak_pure C.jet_elements_taptweak_modinfo
 C.jet_elements_taptweak_inverse_phases C.jet_elements_taptweak_inverse_entry C.jet_transport.
Require Import C.jet_elements_taptweak_inverse_finish.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_modinfo_fe_block.
Lemma elements_taptweak_inverse_blocks beta e:
 ematch beta(snd inv_start_alloc)e ->blocks_of_env elements_taptweak_ge e=blocks_of_env secp_ge e.
Proof.
 intro Env;symmetry;eapply blocks_of_env_agree;
 [exact(elements_taptweak_inverse_env_domain beta e Env)|exact elements_taptweak_inverse_vars_checked].
Qed.
Lemma elements_taptweak_inv_finish_locals_freeable rho beta m mf : rep rho beta inv_loop_regs m ->
 blk beta 1=elements_taptweak_modinfo_fe_block -> Mem.range_perm mf (blk beta 2) 0 40 Cur Freeable ->
 lframe (fun b ofs=>norm62_outside (blk beta 2) elements_taptweak_modinfo_fe_block b ofs /\ b<>blk beta 0) m mf ->
 forall r,(2<=r<7)%nat -> Mem.range_perm mf (blk beta r) 0 (inv_local_size r) Cur Freeable.
Proof.
 intros Rep Block DFree Frame r R;destruct (Nat.eq_dec r 2) as [->|Other];[exact DFree|].
 pose proof (inv_loop_rep_distinct rho beta m Rep) as Distinct.
 destruct (rep_free_region rho beta inv_loop_regs m r (inv_local_size r) Rep
  ltac:(change (r<7)%nat;lia) (inv_local_owned r R)) as (Base & OldFree).
 pose proof (nth_error_nth' inv_loop_regs (mkreg [] true None) (n:=r) ltac:(change (r<7)%nat;lia)) as At.
 pose proof (proj1 (proj2 (rep_region _ _ _ _ r _ Rep At))) as Valid.
 intros pos P;eapply (proj1 (proj2 Frame));[exact Valid| |apply OldFree;exact P].
 split.
 - split;left;[apply Distinct;lia|rewrite <-Block;apply Distinct;lia].
 - apply Distinct;lia.
Qed.

Theorem elements_taptweak_inv_free_actual_locals rho beta e m mf : rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e -> blk beta 1=elements_taptweak_modinfo_fe_block ->
 Mem.range_perm mf (blk beta 2) 0 40 Cur Freeable ->
 lframe (fun b ofs=>norm62_outside (blk beta 2) elements_taptweak_modinfo_fe_block b ofs /\ b<>blk beta 0) m mf ->
 exists mr,Mem.free_list mf (blocks_of_env elements_taptweak_ge e)=Some mr /\
 lframe (fun b _=>inv_free_outside beta b) mf mr.
Proof.
 intros Rep Env Block DFree Frame.
 destruct (inv_free_env_blocks rho beta e m Rep Env) as (Blocks & NoRepeat).
 rewrite <-(elements_taptweak_inverse_blocks beta e Env)in Blocks,NoRepeat.
 destruct (free_list_exists (blocks_of_env elements_taptweak_ge e) mf NoRepeat) as (mr & Free & Unchanged).
 - intros b lo hi Member;destruct (Blocks b lo hi Member) as (r & R & -> & -> & ->).
   apply (elements_taptweak_inv_finish_locals_freeable rho beta m mf Rep Block DFree Frame r R).
 - exists mr;split;[exact Free|].
   eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
   intros b ofs Outside _;rewrite(elements_taptweak_inverse_blocks beta e Env);apply(inv_free_not_listed rho beta e m b Rep Env Outside).
Qed.

Theorem exec_elements_taptweak_inv_finish_and_free len rho beta e le m : (0<len<=5)%nat -> rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e -> blk beta 1=elements_taptweak_modinfo_fe_block -> bas beta 1=0 ->
 le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 le!_modinfo=Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
 le!_x=Some (Vptr (blk beta 0) Ptrofs.zero) -> de62_state_bounds (inv_de_rho rho) -> exists mf mr,
 Clight2.exec_stmt elements_taptweak_ge e le m inv_finish E0 (inv_finish_temps len rho le) mf Out_normal /\
 Mem.free_list mf (blocks_of_env elements_taptweak_ge e)=Some mr /\
 fe_at mr (blk beta 0) 0 (words5 (inv_finish_words len rho)) /\
 signed62_normalized (inv_finish_words len rho) /\
 signed62_unsigned_value (inv_finish_words len rho)=
  ((if Int64.lt (inv_finish_sign len rho) Int64.zero then -1 else 1)*
   de62_input_value (inv_de_rho rho) false) mod feP /\
 Mem.range_perm mr (blk beta 0) 0 40 Cur Freeable /\ elements_taptweak_modinfo_fe_global_rep mr /\
 lframe (fun b ofs=>norm62_outside (blk beta 2) elements_taptweak_modinfo_fe_block b ofs /\ b<>blk beta 0 /\
  inv_free_outside beta b) m mr.
Proof.
 intros Len Rep Env Block Base Length Modinfo X Bounds.
 destruct (exec_elements_taptweak_inv_finish len rho beta e le m Len Rep Env Block Base Length Modinfo X Bounds)
  as (mf & Exec & XField & DField & Normalized & Numeric & XFree & DFree & Global & Frame).
 destruct (elements_taptweak_inv_free_actual_locals rho beta e m mf Rep Env Block DFree Frame) as (mr & Free & FFrame).
 pose proof (inv_loop_rep_distinct rho beta m Rep) as Distinct.
 assert (XOutside : inv_free_outside beta (blk beta 0)) by (intros r R;apply Distinct;lia).
 assert (GOutside : inv_free_outside beta elements_taptweak_modinfo_fe_block).
 { rewrite <-Block;intros r R;apply Distinct;lia. }
 assert (XFieldR : fe_at mr (blk beta 0) 0 (words5 (inv_finish_words len rho))).
 { eapply field_at_lframe;[exact XField|exact FFrame|intros;exact XOutside]. }
 assert (XFreeR : Mem.range_perm mr (blk beta 0) 0 40 Cur Freeable).
 { eapply field_freeable_lframe;[exact XField|exact XFree|exact FFrame|intros;exact XOutside]. }
 assert (GlobalR : elements_taptweak_modinfo_fe_global_rep mr).
 { eapply elements_taptweak_modinfo_fe_global_lframe;[exact Global|exact FFrame|intros;exact GOutside]. }
 exists mf,mr;split;[exact Exec|];split;[exact Free|];split;[exact XFieldR|];split;[exact Normalized|].
 split;[exact Numeric|];split;[exact XFreeR|];split;[exact GlobalR|].
 eapply lframe_trans.
 - eapply lframe_implies;[exact Frame|intros b ofs (N & XN & O) _;split;assumption].
 - eapply lframe_implies;[exact FFrame|intros b ofs (N & XN & O) _;exact O].
Qed.

Theorem exec_elements_taptweak_inv_finish_literal value n len rho beta e le m :
  (0<len<=5)%nat -> rep rho beta inv_loop_regs m -> ematch beta (snd inv_start_alloc) e ->
  blk beta 1=elements_taptweak_modinfo_fe_block -> bas beta 1=0 ->
  le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
  le!_modinfo=Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
  le!_x=Some (Vptr (blk beta 0) Ptrofs.zero) -> de62_state_bounds (inv_de_rho rho) ->
  0<=value<feP -> inv_tail_low_bounds len rho -> inv_coefficient_link value len rho ->
  inv_state_matches len rho (fst (stepN n (init feP value inv_seed_modulus_odd))) ->
  g (fst (stepN n (init feP value inv_seed_modulus_odd)))=0 ->
  (value=0 -> de62_input_value (inv_de_rho rho) false mod feP=0) -> exists mf mr,
  Clight2.exec_stmt elements_taptweak_ge e le m inv_finish E0 (inv_finish_temps len rho le) mf Out_normal /\
  Mem.free_list mf (blocks_of_env elements_taptweak_ge e)=Some mr /\
  fe_at mr (blk beta 0) 0 (words5 (inv_finish_words len rho)) /\
  signed62_normalized (inv_finish_words len rho) /\
  signed62_unsigned_value (inv_finish_words len rho)=literal_invert_numeric value /\
  (forall raw,0<=raw<2^256 -> value=raw mod feP ->
    signed62_unsigned_value (inv_finish_words len rho)=literal_invert_numeric raw) /\
  Mem.range_perm mr (blk beta 0) 0 40 Cur Freeable /\ elements_taptweak_modinfo_fe_global_rep mr /\
  lframe (fun b ofs=>norm62_outside (blk beta 2) elements_taptweak_modinfo_fe_block b ofs /\ b<>blk beta 0 /\
    inv_free_outside beta b) m mr.
Proof.
  intros Len Rep Env Block Base Length Modinfo X Bounds Range Low Link State Stop Zero.
  destruct (exec_elements_taptweak_inv_finish_and_free len rho beta e le m Len Rep Env Block Base Length Modinfo X Bounds)
    as (mf & mr & Run & Free & Out & Normalized & Numeric & Owned & Global & Frame).
  rewrite (inv_terminal_literal_coefficient value n len rho Range Len Low Link State Stop Zero) in Numeric.
  assert (Original : forall raw,0<=raw<2^256 -> value=raw mod feP ->
    signed62_unsigned_value (inv_finish_words len rho)=literal_invert_numeric raw).
  { intros raw Raw Eq;rewrite Numeric,Eq;apply inv_literal_after_canonical_input;exact Raw. }
  exists mf,mr;repeat first [assumption|split].
Qed.

