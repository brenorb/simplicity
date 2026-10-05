(** The core full_left_shift_64_m / full_right_shift_64_m jets, whose copy
    count 64 + m exceeds one word.  Their canonical programs only rebalance the
    tuple, so the serialized output equals the input; the jets copy all input
    cells.  Conditional on the explicit [memcpy_model]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_context_separated C.jet_projection_cells C.jet_full_shift_cells.
Require Import C.jet_bitcoin_effects C.jet_core_wrapper C.jet_core_copy_exec C.jet_core_copy_jets.
Require Import C.jet_core_fullshift_jets.
Require Import C.jet_bitmachine_rep C.jet_copyBits_separation C.jet_memcpy_model C.jet_copyBits_wide_helper.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque ge0.
Set Default Timeout 120.

Lemma core_copy_phase_call_wide (Hmodel : memcpy_model) m1 bl bd dbase bw outedge cursor bi edge rc K cells :
  frame_fields_at m1 bl 0 bi edge rc -> write_frame_at m1 bd dbase bw outedge cursor K ->
  K = Z.of_nat (length cells) -> 64 < K <= 128 ->
  jet_copy_buffers_separated bd bi bw edge outedge cursor rc K ->
  frame_input_cells_at m1 bi edge rc cells ->
  exists mf,
    Clight2.eval_funcall ge0 m1 (Internal f_simplicity_copyBits)
      [Vptr bd (Ptrofs.repr dbase); Vptr bl Ptrofs.zero; Vlong (Int64.repr K)] E0 mf Vundef /\
    write_effect m1 mf bd dbase bw outedge cursor K cells.
Proof.
  intros HF HW Hlen HK Hsep Hin.
  assert (HB0 : frame_base_valid 0) by (split; [lia|change (16 <= 18446744073709551615); lia]).
  destruct (eval_copyBits_wide_layout Hmodel m1 bd dbase bl 0 bi edge rc bw outedge cursor K cells
    HB0 HF HW Hlen HK Hsep Hin) as (mf & Hcall & Hcells & Hprefix & Hfields & Hloads & Hperm & Hvalid).
  exists mf. split.
  - change (Ptrofs.repr 0) with Ptrofs.zero in Hcall. exact Hcall.
  - split; [exact Hcells|]. split; [exact Hprefix|]. split; [exact Hfields|]. split; [exact Hloads|]. split; assumption.
Qed.

Theorem core_leftmost_jet_e_wide (Hmodel : memcpy_model) f (A B : Ty) (spec : tySem A -> tySem B) (arg : expr) :
  core_wrapper_shape f (core_simple_rest (core_copy_call_e arg)) ->
  typeof arg = tint -> (forall e le m, eval_expr ge0 e le m arg (Vint (Int.repr (Z.of_nat (bitSize B))))) ->
  64 < Z.of_nat (bitSize B) <= 128 -> (bitSize B <= bitSize A)%nat ->
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
    destruct (core_copy_phase_call_wide Hmodel mc bl bd dbase bw outedge cursor bi edge rc K (encode (spec a))
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

Theorem full_left_shift_64_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_64_1 (Ty.Prod (Word 6) (Word 0)) (Ty.Prod (Word 0) (Word 6)) (@full_left_shift1 (Word 0) 6 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e_wide with (arg := fullshift_arg 64 1); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 64 1 ltac:(lia) ltac:(lia)).
  - vm_compute. split; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 0) 6 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_64_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_64_2 (Ty.Prod (Word 6) (Word 1)) (Ty.Prod (Word 1) (Word 6)) (@full_left_shift1 (Word 1) 5 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e_wide with (arg := fullshift_arg 64 2); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 64 2 ltac:(lia) ltac:(lia)).
  - vm_compute. split; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 1) 5 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_64_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_64_4 (Ty.Prod (Word 6) (Word 2)) (Ty.Prod (Word 2) (Word 6)) (@full_left_shift1 (Word 2) 4 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e_wide with (arg := fullshift_arg 64 4); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 64 4 ltac:(lia) ltac:(lia)).
  - vm_compute. split; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 2) 4 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_64_8_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_64_8 (Ty.Prod (Word 6) (Word 3)) (Ty.Prod (Word 3) (Word 6)) (@full_left_shift1 (Word 3) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e_wide with (arg := fullshift_arg 64 8); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 64 8 ltac:(lia) ltac:(lia)).
  - vm_compute. split; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 3) 3 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_64_16_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_64_16 (Ty.Prod (Word 6) (Word 4)) (Ty.Prod (Word 4) (Word 6)) (@full_left_shift1 (Word 4) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e_wide with (arg := fullshift_arg 64 16); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 64 16 ltac:(lia) ltac:(lia)).
  - vm_compute. split; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 4) 2 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_left_shift_64_32_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_left_shift_64_32 (Ty.Prod (Word 6) (Word 5)) (Ty.Prod (Word 5) (Word 6)) (@full_left_shift1 (Word 5) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e_wide with (arg := fullshift_arg 64 32); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 64 32 ltac:(lia) ltac:(lia)).
  - vm_compute. split; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_left_encode (Word 5) 1 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_64_1_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_64_1 (Ty.Prod (Word 0) (Word 6)) (Ty.Prod (Word 6) (Word 0)) (@full_right_shift1 (Word 0) 6 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e_wide with (arg := fullshift_arg 64 1); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 64 1 ltac:(lia) ltac:(lia)).
  - vm_compute. split; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 0) 6 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_64_2_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_64_2 (Ty.Prod (Word 1) (Word 6)) (Ty.Prod (Word 6) (Word 1)) (@full_right_shift1 (Word 1) 5 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e_wide with (arg := fullshift_arg 64 2); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 64 2 ltac:(lia) ltac:(lia)).
  - vm_compute. split; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 1) 5 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_64_4_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_64_4 (Ty.Prod (Word 2) (Word 6)) (Ty.Prod (Word 6) (Word 2)) (@full_right_shift1 (Word 2) 4 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e_wide with (arg := fullshift_arg 64 4); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 64 4 ltac:(lia) ltac:(lia)).
  - vm_compute. split; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 2) 4 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_64_8_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_64_8 (Ty.Prod (Word 3) (Word 6)) (Ty.Prod (Word 6) (Word 3)) (@full_right_shift1 (Word 3) 3 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e_wide with (arg := fullshift_arg 64 8); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 64 8 ltac:(lia) ltac:(lia)).
  - vm_compute. split; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 3) 3 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_64_16_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_64_16 (Ty.Prod (Word 4) (Word 6)) (Ty.Prod (Word 6) (Word 4)) (@full_right_shift1 (Word 4) 2 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e_wide with (arg := fullshift_arg 64 16); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 64 16 ltac:(lia) ltac:(lia)).
  - vm_compute. split; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 4) 2 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.

Theorem full_right_shift_64_32_local_spec : memcpy_model ->
  jet_separated_local_spec f_simplicity_full_right_shift_64_32 (Ty.Prod (Word 5) (Word 6)) (Ty.Prod (Word 6) (Word 5)) (@full_right_shift1 (Word 5) 1 Alg.CoreFunSem).
Proof.
  intros Hm. eapply core_leftmost_jet_e_wide with (arg := fullshift_arg 64 32); [exact Hm| | | | | | ].
  - repeat split; try reflexivity. intros x y Hx Hy; cbn in Hx, Hy; contradiction.
  - reflexivity.
  - intros e le m. exact (eval_fullshift_arg e le m 64 32 ltac:(lia) ltac:(lia)).
  - vm_compute. split; [reflexivity|discriminate].
  - vm_compute. lia.
  - intros a. refine (eq_trans (core_fullshift_right_encode (Word 5) 1 a) _). symmetry. apply firstn_all2.
    rewrite encode_length. vm_compute. lia.
Qed.
