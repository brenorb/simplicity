(** From caller storage through actual function entry and the first two
    original statements.  The four multiply calls and final free remain. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_multiply_checkpoint_columns C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_square_separate_layout.
Require Import C.jet_secp_rescale_prefix C.jet_secp_rescale_entry.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words rescale_prefix rescale_prefix_state.

Theorem rescale_start_from_storage rho m bp bs :
  square_input_bounds rho -> Mem.range_perm m bp 0 128 Cur Freeable ->
  fe_at m bs 0 (words5 rho) -> Mem.range_perm m bs 0 40 Cur Freeable -> bp <> bs ->
  exists bz e le0 le1 mi mf,
    function_entry2 secp_ge f_secp256k1_gej_rescale
      [Vptr bp Ptrofs.zero;Vptr bs Ptrofs.zero] m e le0 mi /\
    Clight2.exec_stmt secp_ge e le0 mi rescale_prefix E0 le1 mf Out_normal /\
    ematch [(bp,0);(bs,0);(bz,0)] (snd rescale_allocated) e /\
    tmatch rho [(bp,0);(bs,0);(bz,0)] (stemps rescale_prefix_state) le1 /\
    fe_at mf bz 0 (words5 (square_words rho)) /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
    fe_at mf bs 0 (words5 rho) /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\
    radix_value (square_words rho) mod field_prime = (radix_value rho * radix_value rho) mod field_prime /\
    square_input_bounds (square_words rho) /\ ~ Mem.valid_block m bz /\
    lframe (fun b _ => b = bp) m mf /\
    lframe (fun b _ => b <> bp /\ b <> bs) m mf.
Proof.
  intros HB HP HS HFS HNe.
  pose proof (rescale_inputs_from_storage rho m bp bs HP HS HFS HNe) as HR.
  destruct (rescale_actual_entry rho [(bp,0);(bs,0)] m HR)
    as (betaN & e & le0 & mi & HEntry & HRi & HT & HE & HL & HFresh & HU).
  change (length betaN = 1%nat) in HL.
  destruct betaN as [|[bz bzofs] rest]; [discriminate HL|].
  destruct rest; [|discriminate HL].
  change (rep rho [(bp,0);(bs,0);(bz,bzofs)] rescale_prefix_regs mi) in HRi.
  pose proof (rep_region _ _ _ mi 2 _ HRi eq_refl) as HZ.
  destruct HZ as (_ & _ & _ & _ & HBase & _).
  change (bzofs = 0) in HBase; subst bzofs.
  assert (HNew : ~ Mem.valid_block m bz).
  { inversion HFresh; assumption. }
  destruct (exec_rescale_square_numeric rho [(bp,0);(bs,0);(bz,0)] e le0 mi HB HRi HT HE)
    as (le1 & mf & HX & HField & HFreeZ & HScalar & HFreeS & HFreeP & HV & HBounds & HT1 & HF).
  pose proof (rescale_prefix_point_frame rho [(bp,0);(bs,0);(bz,0)] mi mf HRi HF) as HPoint.
  assert (HPointAll : lframe (fun b _ => b = bp) m mf).
  { eapply lframe_trans; [|exact HPoint].
    apply lframe_unchanged; eapply Mem.unchanged_on_implies; [exact HU|]; intros; exact I. }
  assert (HOutside : lframe (fun b _ => Mem.valid_block m b /\ b <> bp /\ b <> bs) m mf).
  { eapply lframe_trans.
    - apply lframe_unchanged; eapply Mem.unchanged_on_implies; [exact HU|]; intros; exact I.
    - eapply lframe_implies; [exact HF|].
      intros b ofs (HValid & HBP & HBS) HValidI (r & sh & d & ch & HN & HC & HEq & HO).
      destruct r as [|[|[|r]]]; cbn [blk bas lay nth fst snd] in HEq.
      + exact (HBP HEq).
      + exact (HBS HEq).
      + apply HNew; rewrite <- HEq; exact HValid.
      + destruct r; discriminate HN. }
  exists bz, e, le0, le1, mi, mf.
  split; [exact HEntry|]; split; [exact HX|]; split; [exact HE|]; split; [exact HT1|].
  split; [exact HField|]; split; [exact HFreeZ|]; split; [exact HScalar|]; split; [exact HFreeS|].
  split; [exact HFreeP|]; split; [exact HV|]; split; [exact HBounds|]; split; [exact HNew|].
  split; [exact HPointAll|].
  eapply lframe_implies; [exact HOutside|]; intros b ofs HBOut HValid; split; assumption.
Qed.
