(** Complete original gej_rescale helper: actual entry, the retained check,
    square, four multiplies and free of zz.  The public jet bridge is separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_mul_storage.
Require Import C.jet_secp_statement_prefix C.jet_secp_rescale_prefix C.jet_secp_rescale_start
  C.jet_secp_rescale_calls C.jet_secp_rescale_statements.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition rescale_local_env bz := PTree.set _zz (bz,Tstruct __5467 noattr) empty_env.
Lemma rescale_variable_table : snd rescale_allocated = [(_zz,(2%nat,Tstruct __5467 noattr))].
Proof. reflexivity. Qed.
Lemma rescale_local_blocks bz : blocks_of_env secp_ge (rescale_local_env bz) = [(bz,0,40)].
Proof. reflexivity. Qed.
Lemma rescale_prefix_r : (stemps rescale_prefix_state)!_r = Some (XP 0 0).
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma rescale_prefix_s : (stemps rescale_prefix_state)!_s = Some (XP 1 0).
Proof. Timeout 10 vm_compute; reflexivity. Qed.

Local Opaque secp_ge square_words point_mul_words rescale_prefix_state rescale_rest.
Lemma rescale_environment_exact e bp bs bz :
  ematch [(bp,0);(bs,0);(bz,0)] (snd rescale_allocated) e -> e = rescale_local_env bz.
Proof.
  intro HE; apply PTree.extensionality; intro id.
  rewrite (proj1 (HE id)), rescale_variable_table.
  unfold rescale_local_env; rewrite PTree.gsspec.
  destruct (peq id _zz) as [->|HNe]; [reflexivity|].
  rewrite PTree.gempty; cbn [vlookup].
  destruct (Pos.eqb _zz id) eqn:HB; [apply Pos.eqb_eq in HB; congruence|reflexivity].
Qed.

Lemma rescale_field_block_frame m mf b ofs w : fe_at m b ofs (words5 w) ->
  lframe (fun bx _ => bx = b) m mf -> fe_at mf b ofs (words5 w).
Proof.
  intros (HB & HA & HM & HP & HL) HF.
  assert (HV : Mem.valid_block m b) by (eapply Mem.perm_valid_block; apply (HP ofs); lia).
  split; [exact HB|]; split; [exact HA|]; split; [exact HM|]; split.
  - intros pos HPos; apply (proj1 (proj2 HF)); [exact HV|reflexivity|apply HP; exact HPos].
  - intros i x HN; rewrite (proj1 HF Mint64 b (ofs + 8 * Z.of_nat i) HV).
    + apply HL; exact HN.
    + intros; reflexivity.
Qed.

Theorem eval_gej_rescale_owned x y z s m bp bs flag :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds s ->
  bp <> bs -> fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
  fe_at m bs 0 (words5 s) -> Mem.range_perm m bp 0 128 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.load Mint32 m bp 120 = Some (Vint flag) ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_rescale)
      [Vptr bp Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef /\
    fe_at mf bp 0 (words5 (point_mul_words x (square_words s))) /\
    fe_at mf bp 40 (words5 (point_mul_words (point_mul_words y (square_words s)) s)) /\
    fe_at mf bp 80 (words5 (point_mul_words z s)) /\ fe_at mf bs 0 (words5 s) /\
    Mem.load Mint32 mf bp 120 = Some (Vint flag) /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
    square_input_bounds (point_mul_words x (square_words s)) /\
    square_input_bounds (point_mul_words (point_mul_words y (square_words s)) s) /\
    square_input_bounds (point_mul_words z s) /\
    lframe (fun b _ => b <> bp /\ b <> bs) m mf.
Proof.
  intros BX BY BZ BS HPS HX HY HZ HS HFP HFS HFlag.
  assert (HVP : Mem.valid_block m bp) by (eapply Mem.perm_valid_block; apply (HFP 0); lia).
  assert (HVS : Mem.valid_block m bs) by (eapply Mem.perm_valid_block; apply (HFS 0); lia).
  destruct (rescale_start_from_storage s m bp bs BS HFP HS HFS HPS)
    as (bz & e & le0 & le1 & mi & mp & HEntry & HPrefix & HE & HT & HZZ & HFZZ & HS1 & HFS1 & HFP1 &
      HSquare & BSS & HNew & HPoint & HStart).
  assert (HPZ : bp <> bz) by (intros ->; contradiction).
  assert (HSZ : bs <> bz) by (intros ->; contradiction).
  pose proof (rescale_field_block_frame m mp bp 0 x HX HPoint) as X1.
  pose proof (rescale_field_block_frame m mp bp 40 y HY HPoint) as Y1.
  pose proof (rescale_field_block_frame m mp bp 80 z HZ HPoint) as Z1.
  assert (Flag1 : Mem.load Mint32 mp bp 120 = Some (Vint flag)).
  { rewrite (proj1 HPoint Mint32 bp 120 HVP); [exact HFlag|intros; reflexivity]. }
  destruct (rescale_four_multiply_calls x y z s (square_words s) mp bp bs bz flag
    BX BY BZ BS BSS HPS HPZ HSZ X1 Y1 Z1 HS1 HZZ HFP1 HFS1 HFZZ Flag1)
    as (m1 & m2 & m3 & mb & C1 & C2 & C3 & C4 & X4 & Y4 & Z4 & S4 & Flag4 &
      FP4 & FS4 & FZZ4 & BX4 & BY4 & BZ4 & HCalls).
  pose proof (HT _r _ rescale_prefix_r) as HR.
  pose proof (HT _s _ rescale_prefix_s) as HST.
  change (le1!_r = Some (Vptr bp Ptrofs.zero)) in HR.
  change (le1!_s = Some (Vptr bs Ptrofs.zero)) in HST.
  pose proof (rescale_environment_exact e bp bs bz HE) as HEnv.
  assert (HLZ : e!_zz = Some (bz,Tstruct __5467 noattr)) by (rewrite HEnv; apply PTree.gss).
  assert (HG : e!_secp256k1_fe_mul = None) by (rewrite HEnv; reflexivity).
  pose proof (exec_rescale_rest_from_calls e le1 mp m1 m2 m3 mb bp bs bz HR HST HLZ HG C1 C2 C3 C4) as HRest.
  assert (HBody : Clight2.exec_stmt secp_ge e le0 mi (fn_body f_secp256k1_gej_rescale) E0 le1 mb Out_normal).
  { rewrite <- rescale_prefix_source.
    eapply exec_statement_prefix_then_last; [exact HPrefix|exact HRest]. }
  destruct (Mem.range_perm_free mb bz 0 40 FZZ4) as (mf & HFree).
  assert (HU : Mem.unchanged_on (fun b _ => b <> bz) mb mf).
  { eapply Mem.free_unchanged_on; [exact HFree|]; intros pos HPos HSame; apply HSame; reflexivity. }
  pose proof (lframe_unchanged _ _ _ HU) as HFreeFrame.
  assert (HFreePoint : lframe (fun b _ => b = bp) mb mf).
  { eapply lframe_implies; [exact HFreeFrame|]; intros b ofs -> _; exact HPZ. }
  assert (HFreeScalar : lframe (fun b _ => b = bs) mb mf).
  { eapply lframe_implies; [exact HFreeFrame|]; intros b ofs -> _; exact HSZ. }
  assert (HVP4 : Mem.valid_block mb bp) by (eapply Mem.perm_valid_block; apply (FP4 0); lia).
  assert (HVS4 : Mem.valid_block mb bs) by (eapply Mem.perm_valid_block; apply (FS4 0); lia).
  exists mf; split.
  - eapply eval_funcall_internal with (e := e) (le1 := le0) (le2 := le1) (m1 := mi) (m2 := mb) (out := Out_normal).
    + exact HEntry.
    + exact HBody.
    + reflexivity.
    + rewrite HEnv, rescale_local_blocks; cbn [Mem.free_list]; rewrite HFree; reflexivity.
  - split; [eapply rescale_field_block_frame; [exact X4|exact HFreePoint]|].
    split; [eapply rescale_field_block_frame; [exact Y4|exact HFreePoint]|].
    split; [eapply rescale_field_block_frame; [exact Z4|exact HFreePoint]|].
    split; [eapply rescale_field_block_frame; [exact S4|exact HFreeScalar]|].
    split.
    { rewrite (proj1 HFreePoint Mint32 bp 120 HVP4); [exact Flag4|intros; reflexivity]. }
    split.
    { intros pos HPos; apply (proj1 (proj2 HFreePoint)); [exact HVP4|reflexivity|apply FP4; exact HPos]. }
    split.
    { intros pos HPos; apply (proj1 (proj2 HFreeScalar)); [exact HVS4|reflexivity|apply FS4; exact HPos]. }
    split; [exact BX4|]; split; [exact BY4|]; split; [exact BZ4|].
    assert (HFAll : lframe (fun b _ => Mem.valid_block m b /\ b <> bp /\ b <> bs) m mf).
    { eapply lframe_trans.
      - eapply lframe_implies; [exact HStart|]; intros b ofs (HV & HBP & HBS) _; split; assumption.
      - eapply lframe_trans.
        + eapply lframe_implies; [exact HCalls|]; intros b ofs (HV & HBP & HBS) _.
          split; [exact HBP|]; split; [exact HBS|]; intro HB; apply HNew; rewrite <- HB; exact HV.
        + eapply lframe_implies; [exact HFreeFrame|]; intros b ofs (HV & HBP & HBS) _ HB.
          apply HNew; rewrite <- HB; exact HV. }
    eapply lframe_implies; [exact HFAll|]; intros b ofs HOutside HV; split; assumption.
Qed.
