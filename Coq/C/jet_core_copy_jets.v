(** Generic proofs of the core projection jets
      [src_local = src; (forwardBits(&src_local, n - m);) copyBits(dst, &src_local, m); return 1]
    (leftmost_n_m, rightmost_n_m), conditional on the explicit [memcpy_model]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_context_separated C.jet_projection_cells C.jet_forwardBits_layout.
Require Import C.jet_bitcoin_effects C.jet_core_wrapper C.jet_core_copy_exec.
Require Import C.jet_bitmachine_rep C.jet_copyBits_separation C.jet_memcpy_model C.jet_copyBits_short_cells C.jet_copyBits_small_full.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque ge0.
Set Default Timeout 60.

Lemma core_input_cells_load_preserved m m2 bi edge rc cells :
  (forall ofs w, Mem.load Mint64 m bi ofs = Some (Vlong w) -> Mem.load Mint64 m2 bi ofs = Some (Vlong w)) ->
  frame_input_cells_at m bi edge rc cells -> frame_input_cells_at m2 bi edge rc cells.
Proof.
  intros HP HI.
  assert (HB : forall q bit, frame_input_bit_at m bi edge q bit -> frame_input_bit_at m2 bi edge q bit).
  { intros q bit [HQ [HE [w [HL HX]]]]. split; [exact HQ|]. split; [exact HE|].
    exists w. split; [apply HP; exact HL|exact HX]. }
  intros i c Hi. specialize (HI i c Hi). destruct c as [bit|]; cbn [cell_matches] in *.
  - apply HB; exact HI.
  - destruct HI as [bit Hbit]. exists bit. apply HB; exact Hbit.
Qed.

(** The copy phase: the actual call on a local source frame at cursor [rc]. *)
Lemma core_copy_phase_call (Hmodel : memcpy_model) m1 bl bd dbase bw outedge cursor bi edge rc K cells :
  frame_fields_at m1 bl 0 bi edge rc -> write_frame_at m1 bd dbase bw outedge cursor K ->
  K = Z.of_nat (length cells) -> 0 < K <= 64 ->
  jet_copy_buffers_separated bd bi bw edge outedge cursor rc K ->
  frame_input_cells_at m1 bi edge rc cells ->
  exists mf,
    Clight2.eval_funcall ge0 m1 (Internal f_simplicity_copyBits)
      [Vptr bd (Ptrofs.repr dbase); Vptr bl Ptrofs.zero; Vlong (Int64.repr K)] E0 mf Vundef /\
    write_effect m1 mf bd dbase bw outedge cursor K cells.
Proof.
  intros HF HW Hlen HK Hsep Hin.
  assert (HB0 : frame_base_valid 0) by (split; [lia|change (16 <= 18446744073709551615); lia]).
  destruct (eval_copyBits_small_layout Hmodel m1 bd dbase bl 0 bi edge rc bw outedge cursor K cells
    HB0 HF HW Hlen HK Hsep Hin) as (mf & Hcall & Hcells & Hprefix & Hfields & Hloads & Hperm & Hvalid).
  exists mf. split.
  - change (Ptrofs.repr 0) with Ptrofs.zero in Hcall. exact Hcall.
  - split; [exact Hcells|]. split; [exact Hprefix|]. split; [exact Hfields|]. split; [exact Hloads|]. split; assumption.
Qed.

Lemma core_copy_phase (Hmodel : memcpy_model) m1 bl bd dbase bw outedge cursor bi edge rc K cells le :
  frame_fields_at m1 bl 0 bi edge rc -> write_frame_at m1 bd dbase bw outedge cursor K ->
  K = Z.of_nat (length cells) -> 0 < K <= 64 ->
  jet_copy_buffers_separated bd bi bw edge outedge cursor rc K ->
  frame_input_cells_at m1 bi edge rc cells ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  exists mf,
    Clight2.exec_stmt ge0 (core_src_locals bl) le m1 (core_copy_call K) E0 le mf Out_normal /\
    write_effect m1 mf bd dbase bw outedge cursor K cells.
Proof.
  intros HF HW Hlen HK Hsep Hin Hdst.
  destruct (core_copy_phase_call Hmodel m1 bl bd dbase bw outedge cursor bi edge rc K cells
    HF HW Hlen HK Hsep Hin) as (mf & Hcall & Heff).
  exists mf. split; [|exact Heff].
  eapply exec_core_copy_call; [lia|exact Hdst|exact Hcall].
Qed.

Lemma core_local_frame_fields m ma mc bl bs sbase bytes bi edge rc :
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes m bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Mem.load Mptr m bs sbase = Some (Vptr bi (Ptrofs.repr edge)) ->
  Mem.load Mint64 m bs (sbase + 8) = Some (Vlong (Int64.repr rc)) ->
  frame_fields_at mc bl 0 bi edge rc.
Proof.
  intros HA HB SC HE HO.
  assert (HV : Mem.valid_block m bs).
  { eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies with (p1 := Readable); [|constructor].
    eapply Mem.load_valid_access; exact HE. }
  assert (HBa : Mem.loadbytes ma bs sbase 16 = Some bytes)
    by (erewrite Mem.loadbytes_alloc_unchanged; eauto).
  assert (HEa : Mem.load Mptr ma bs sbase = Some (Vptr bi (Ptrofs.repr edge)))
    by (eapply Mem.load_alloc_other; eauto).
  assert (HOa : Mem.load Mint64 ma bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (eapply Mem.load_alloc_other; eauto).
  exact (frame_copy_fields_at ma mc bs sbase bl bytes _ _ HBa SC HEa HOa).
Qed.

Lemma core_local_frame_writable m ma mc bl bytes :
  Mem.alloc m 0 16 = (ma, bl) -> Mem.storebytes ma bl 0 bytes = Some mc ->
  Mem.valid_access mc Mint64 bl 8 Writable.
Proof.
  intros HA SC.
  eapply Mem.storebytes_valid_access_1; [exact SC|].
  eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
  eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|]. exists 1; reflexivity.
Qed.

Theorem core_leftmost_jet_e (Hmodel : memcpy_model) f (A B : Ty) (spec : tySem A -> tySem B) (arg : expr) :
  core_wrapper_shape f (core_simple_rest (core_copy_call_e arg)) ->
  typeof arg = tint -> (forall e le m, eval_expr ge0 e le m arg (Vint (Int.repr (Z.of_nat (bitSize B))))) ->
  0 < Z.of_nat (bitSize B) <= 64 -> (bitSize B <= bitSize A)%nat ->
  (forall a, encode (spec a) = firstn (bitSize B) (encode a)) ->
  jet_separated_local_spec f A B spec.
Proof.
  intros Hshape Hty Harg HK Hsize Hspec env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HBase HAlign [HSedge HSoff] H0 Hmax Hin Hout Hsep.
  set (K := Z.of_nat (bitSize B)) in *.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge)) (Vlong (Int64.repr rc))
    HSedge HSoff) as [bytes HBytes].
  assert (Hlen : K = Z.of_nat (length (encode (spec a)))) by (rewrite encode_length; reflexivity).
  destruct (core_wrapper_layout_simple f (core_copy_call_e arg) (encode (spec a)) env m bd dbase bs sbase bw
    outedge cursor K bytes Hshape HBase HAlign HBytes ltac:(lia) Hout) as (mf & Hcall & HC & HP & HFl & HL).
  - intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    pose proof (core_local_frame_fields m ma mc bl bs sbase bytes bi edge rc HAlloc HBytes HStore
      HSedge HSoff) as HLoc.
    assert (HInC : frame_input_cells_at mc bi edge rc (encode (spec a))).
    { rewrite Hspec. eapply core_input_cells_load_preserved; [|apply projection_input_firstn; exact Hin].
      intros ofs w HL. apply HLP. exact HL. }
    assert (HSepC : jet_copy_buffers_separated bd bi bw edge outedge cursor rc K).
    { replace rc with (rc + 0) by lia. eapply projection_buffers_slice with (total := Z.of_nat (bitSize A));
        [replace (rc + 0) with rc by lia; exact Hsep|lia|lia|lia]. }
    destruct (core_copy_phase_call Hmodel mc bl bd dbase bw outedge cursor bi edge rc K (encode (spec a))
      HLoc HFrameC Hlen ltac:(lia) HSepC HInC) as (mf & Hcallc & Heff).
    assert (Hexec : Clight2.exec_stmt ge0 (core_src_locals bl) (core_wrapper_temps f env bd dbase bs sbase) mc
      (core_copy_call_e arg) E0 (core_wrapper_temps f env bd dbase bs sbase) mf Out_normal).
    { eapply exec_core_copy_call_e with (k := K); [lia|exact Hty|apply Harg| |exact Hcallc].
      unfold core_wrapper_temps. rewrite !PTree.gso by discriminate. apply PTree.gss. }
    + destruct Heff as (HC & HP & HF & HL & HPm & HV).
      exists (core_wrapper_temps f env bd dbase bs sbase), mf.
      split; [exact Hexec|]. split; [exact HC|]. split; [exact HP|]. split; [exact HF|].
      split; [intros chunk b ofs _ H1 H2; apply HL; assumption|].
      split; [exact HPm|exact HV].
  - exists mf. split; [exact Hcall|]. split; [exact HC|]. split; [exact HP|]. split; [exact HFl|].
    exact HL.
Qed.


Theorem core_leftmost_jet (Hmodel : memcpy_model) f (A B : Ty) (spec : tySem A -> tySem B) :
  core_wrapper_shape f (core_simple_rest (core_copy_call (Z.of_nat (bitSize B)))) ->
  0 < Z.of_nat (bitSize B) <= 64 -> (bitSize B <= bitSize A)%nat ->
  (forall a, encode (spec a) = firstn (bitSize B) (encode a)) ->
  jet_separated_local_spec f A B spec.
Proof.
  intros Hshape HK Hsize Hspec.
  eapply core_leftmost_jet_e with (arg := Econst_int (Int.repr (Z.of_nat (bitSize B))) tint); try eassumption.
  - reflexivity.
  - intros e le m. apply eval_Econst_int.
Qed.

Theorem core_rightmost_jet (Hmodel : memcpy_model) f (A B : Ty) (spec : tySem A -> tySem B) (N M : Z) :
  core_wrapper_shape f (Ssequence (core_forward_call N M) (core_simple_rest (core_copy_call M))) ->
  N = Z.of_nat (bitSize A) -> M = Z.of_nat (bitSize B) -> 0 < M <= 64 -> M <= N <= 1000 ->
  (forall a, encode (spec a) = skipn (Z.to_nat (N - M)) (encode a)) ->
  jet_separated_local_spec f A B spec.
Proof.
  intros Hshape HN HM HK HNM Hspec env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HBase HAlign [HSedge HSoff] H0 Hmax Hin Hout Hsep.
  assert (HoutM : write_frame_at m bd dbase bw outedge cursor M) by (rewrite HM; exact Hout).
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge)) (Vlong (Int64.repr rc))
    HSedge HSoff) as [bytes HBytes].
  assert (Hlen : M = Z.of_nat (length (encode (spec a)))).
  { rewrite Hspec, skipn_length, encode_length. lia. }
  destruct (core_wrapper_layout f (Ssequence (core_forward_call N M) (core_simple_rest (core_copy_call M)))
    (encode (spec a)) env m bd dbase bs sbase bw outedge cursor M bytes Hshape HBase HAlign HBytes
    ltac:(lia) HoutM) as (mf & Hcall & HC & HP & HFl & HL).
  - unfold core_wrapper_mid. intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    pose proof (core_local_frame_fields m ma mc bl bs sbase bytes bi edge rc HAlloc HBytes HStore
      HSedge HSoff) as HLoc.
    pose proof (core_local_frame_writable m ma mc bl bytes HAlloc HStore) as HLocW.
    destruct (copy_input_cells_head m bi edge rc (encode a) ltac:(rewrite encode_length; lia) Hin)
      as [_ [_ [src0 Hsrc0]]].
    pose proof (fresh_frame_not_loaded m ma bl bi Mint64 _ _ HAlloc Hsrc0) as Hbi.
    pose proof (fresh_frame_not_loaded m ma bl bd Mptr dbase _ HAlloc (proj1 (proj1 (proj2 HoutM))))
      as Hbd.
    destruct (write_frame_at_head m bd dbase bw outedge cursor M ltac:(lia) HoutM)
      as [_ [_ [_ [w0 Hw0]]]].
    pose proof (fresh_frame_not_loaded m ma bl bw Mint64 _ _ HAlloc Hw0) as Hbw.
    assert (HB0 : frame_base_valid 0) by (split; [lia|change (16 <= 18446744073709551615); lia]).
    destruct (eval_forwardBits_layout mc bl 0 bi edge rc (N - M) HB0 H0 ltac:(lia) ltac:(lia) HLoc HLocW)
      as (mw & Hfwd & HFw & HLw & HPw & HVw).
    assert (HInW : frame_input_cells_at mw bi edge (rc + (N - M)) (encode (spec a))).
    { rewrite Hspec.
      replace (rc + (N - M)) with (rc + Z.of_nat (Z.to_nat (N - M))) by lia.
      eapply core_input_cells_load_preserved.
      - intros ofs w HL. rewrite HLw by (left; congruence). apply HLP. exact HL.
      - eapply projection_input_skipn; [rewrite encode_length; lia|exact Hin]. }
    assert (HFrameW : write_frame_at mw bd dbase bw outedge cursor M).
    { eapply write_frame_at_preserved with (m := mc); [|exact HPw|exact HFrameC].
      intros chunk b ofs v Hb HL. rewrite HLw; [exact HL|left; destruct Hb; congruence]. }
    assert (HSepW : jet_copy_buffers_separated bd bi bw edge outedge cursor (rc + (N - M)) M).
    { eapply projection_buffers_slice with (total := Z.of_nat (bitSize A));
        [exact Hsep|lia|lia|lia]. }
    destruct (core_copy_phase Hmodel mw bl bd dbase bw outedge cursor bi edge (rc + (N - M)) M
      (encode (spec a)) (core_wrapper_temps f env bd dbase bs sbase) HFw HFrameW Hlen ltac:(lia)
      HSepW HInW) as (mf & Hexec & Heff).
    + unfold core_wrapper_temps. rewrite !PTree.gso by discriminate. apply PTree.gss.
    + destruct Heff as (HC & HP & HF & HL & HPm & HV).
      exists (core_wrapper_temps f env bd dbase bs sbase), mf.
      split.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mw) (le1 := core_wrapper_temps f env bd dbase bs sbase).
        -- eapply exec_core_forward_call; [lia|lia|lia|].
           exact Hfwd.
        -- apply exec_core_simple_rest. exact Hexec.
      * split; [exact HC|]. split.
        -- eapply write_prefix_at_preserved with (mr := mw) (me := mf); [|intros ofs w' HL'; exact HL'|exact HP].
           intros ofs w' HL'. rewrite HLw by (left; congruence). exact HL'.
        -- split; [exact HF|]. split.
           ++ intros chunk b ofs Hbl H1 H2. rewrite (HL chunk b ofs H1 H2).
              apply HLw. left. exact Hbl.
           ++ split; [intros b ofs kind p H1; apply HPm; apply HPw; exact H1|
                      intros b H1; apply HV; apply HVw; exact H1].
  - exists mf. split; [exact Hcall|]. split; [exact HC|]. split; [exact HP|]. rewrite <- HM. split; [exact HFl|exact HL].
Qed.

Lemma core_input_cells_preserved_at m m2 bi edge rc cells :
  (forall j w, 0 <= j < Z.of_nat (length cells) ->
    Mem.load Mint64 m bi (edge - 8 * (1 + (rc + j) / 64)) = Some (Vlong w) ->
    Mem.load Mint64 m2 bi (edge - 8 * (1 + (rc + j) / 64)) = Some (Vlong w)) ->
  frame_input_cells_at m bi edge rc cells -> frame_input_cells_at m2 bi edge rc cells.
Proof.
  intros HP HI i c Hi.
  assert (Hlt : (i < length cells)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  assert (HB : forall bit, frame_input_bit_at m bi edge (rc + Z.of_nat i) bit ->
    frame_input_bit_at m2 bi edge (rc + Z.of_nat i) bit).
  { intros bit [HQ [HE [w [HL HX]]]]. split; [exact HQ|]. split; [exact HE|].
    exists w. split; [|exact HX]. apply (HP (Z.of_nat i) w ltac:(lia) HL). }
  specialize (HI i c Hi). destruct c as [bit|]; cbn [cell_matches] in *.
  - apply HB; exact HI.
  - destruct HI as [bit Hbit]. exists bit. apply HB; exact Hbit.
Qed.

(** Input cells survive a write effect whose footprint lies inside the output
    region, given the buffer separation. *)
Lemma core_input_after_effect m m2 bd dbase bi bw edge outedge cursor rc N cells low :
  jet_copy_buffers_separated bd bi bw edge outedge cursor rc N ->
  0 <= rc -> Z.of_nat (length cells) <= N -> 1 <= cursor ->
  outedge <= low -> write_word_address outedge cursor + 8 <= outedge + 8 * frame_words cursor ->
  loads_outside_ranges m m2 bd (dbase + 8) (dbase + 16) bw low (write_word_address outedge cursor + 8) ->
  frame_input_cells_at m bi edge rc cells -> frame_input_cells_at m2 bi edge rc cells.
Proof.
  intros [Hbd [Hbb|Hrange]] H0 Hlen Hc Hlow Hhigh Hloads Hin.
  - eapply core_input_cells_preserved_at; [|exact Hin].
    intros j w Hj HL. rewrite <- HL. apply Hloads; left; auto.
  - eapply core_input_cells_preserved_at; [|exact Hin].
    intros j w Hj HL. rewrite <- HL.
    apply Hloads.
    + left. auto.
    + right. change (size_chunk Mint64) with 8.
      destruct (copy_read_word_region edge rc N j H0 ltac:(lia)) as [Hrl Hrh].
      unfold disjoint_ranges in Hrange. lia.
Qed.
