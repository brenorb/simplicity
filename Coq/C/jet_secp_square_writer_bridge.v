(** Discharge the square helper's storage premises at its real caller boundary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Word.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_rep C.jet_sx_revalue_cells.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_b32_exec.
Require Import C.jet_secp_local_regions C.jet_secp_wrapper_run.
Require Import C.jet_secp_multiply_input_input C.jet_secp_multiply_normalize_bridge
  C.jet_secp_multiply_writer_bridge C.jet_secp_multiply_finish_execute.
Require Import C.jet_secp_square_execution C.jet_secp_square_columns C.jet_secp_square_schedule C.jet_secp_square_denote C.jet_secp_square_source_list
  C.jet_secp_square_numeric C.jet_secp_square_numeric_call C.jet_secp_square_spec_bridge.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque square_limbs sq_r0 sq_r1 sq_r2 sq_r3 sq_r4 secp_ge.

Lemma square_initial_rep x m ba :
  fe_at m ba 0 (map Int64.repr (fe_limbs_of (normalized_value x))) ->
  Mem.range_perm m ba 0 40 Cur Freeable ->
  rep (square_reader_rho x) [(ba,0)] square_regs m.
Proof.
  intros HA HF.
  apply (rep_add _ [] [] m ba 0); [apply rep_nil|cbn; tauto|].
  apply (owned_field_region _ _ _ _ 0 (normalized_value x));
    [reflexivity|exact HA|exact HF|].
  intros i HI; reflexivity.
Qed.

Lemma square_output_owned rho layout m : square_input_bounds rho ->
  rep rho layout [mkreg (u64_cells 0 square_limbs) true (Some 40)] m ->
  bas layout 0 = 0 /\ Mem.range_perm m (blk layout 0) 0 40 Cur Freeable /\
  fe_at m (blk layout 0) (bas layout 0) (words5 (square_words rho)).
Proof.
  intros HB HR; pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof H0 as (_ & _ & _ & _ & HBase & HW & HF & _).
  assert (HK : forallb (isk KL) square_limbs = true).
  { rewrite original_square_symbolic_output; reflexivity. }
  pose proof (region_ok_revalue_u64 rho layout m 0 square_limbs true (Some 40) H0 HK) as HV.
  assert (HD : map (den rho (lay layout)) square_limbs = map Vlong (words5 (square_words rho))).
  { rewrite original_square_symbolic_output; cbn [map].
    rewrite (sq_r0_den rho (lay layout) HB), (sq_r1_den rho (lay layout) HB),
      (sq_r2_den rho (lay layout) HB), (sq_r3_den rho (lay layout) HB), (sq_r4_den rho (lay layout) HB).
    reflexivity. }
  rewrite (revalue_u64_machine_map rho layout _ _ HD) in HV.
  split; [exact HBase|]; split; [exact HF|].
  apply (u64_region_fe_at rho layout m 0 _ (Some 40)); exact HV.
Qed.

Lemma square_output_writer_rep x layout m rc :
  rep (square_reader_rho x) layout [mkreg (u64_cells 0 square_limbs) true (Some 40)] m ->
  rep (product_writer_rho (diagonal (square_reader_rho x)) rc)
    [(blk layout 0,0)] local_write_initial_regs m.
Proof.
  intro HR.
  destruct (square_output_owned (square_reader_rho x) layout m (square_reader_bounds x) HR)
    as (HB & HF & HA).
  rewrite HB in HA.
  exact (wide_initial_from_owned_words _ _ _ _ _ rc m (blk layout 0) HA HF).
Qed.

Lemma square_foot_owner ba b ofs :
  foot [(ba,0)] (map rshape square_regs) b ofs -> b = ba.
Proof.
  intros (r & sh & d & ch & HN & HI & HE & HO).
  destruct r as [|r]; [exact HE|destruct r; discriminate HN].
Qed.

Theorem eval_square_for_writer x m ba rc :
  fe_at m ba 0 (map Int64.repr (fe_limbs_of (normalized_value x))) ->
  Mem.range_perm m ba 0 40 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
      [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef /\
    rep (product_writer_rho (diagonal (square_reader_rho x)) rc) [(ba,0)] local_write_initial_regs mf /\
    Mem.range_perm mf ba 0 40 Cur Freeable /\
    lframe (fun b _ => b <> ba) m mf.
Proof.
  intros HA HF.
  destruct (eval_original_square_literal_from_reader x [(ba,0)] m (square_initial_rep x m ba HA HF))
    as (mf & HC & HR & HL & HV & HB & HFrame).
  assert (HC' : Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf Vundef) by exact HC.
  destruct (square_output_owned (square_reader_rho x) [(ba,0)] mf (square_reader_bounds x) HR)
    as (_ & HFree & HField).
  exists mf; split; [exact HC'|]; split;
    [exact (square_output_writer_rep x [(ba,0)] mf rc HR)|]; split; [exact HFree|].
  eapply lframe_implies; [exact HFrame|].
  intros b ofs HNot HVB HFoot; apply HNot; exact (square_foot_owner ba b ofs HFoot).
Qed.
