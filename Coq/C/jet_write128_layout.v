(** Complete actual write128 call: high getter, high writer, low getter, low
    writer. The low reload is protected at the intermediate writer boundary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_spec C.jet_write_layout C.jet_output_layout.
Require Import C.jet_wide C.jet_wide_spec C.jet_write_wide_mixed_sequence C.jet_u128_fields.
Require Import C.jet_encoding.
Require Import C.jet_divmod128_branch_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition write128_get_call high result := Scall (Some result)
  (Evar (u128_get_id high) (Tfunction (Tcons (tptr (Tstruct _secp256k1_uint128 noattr)) Tnil) tulong cc_default))
  [Etempvar _x (tptr (Tstruct _secp256k1_uint128 noattr))].
Definition write128_write_call result := Scall None
  (Evar _simplicity_write64 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
  [Etempvar _frame (tptr (Tstruct _frameItem noattr)); Etempvar result tulong].
Definition write128_temps bd base br rbase := PTree.set _x (Vptr br (Ptrofs.repr rbase))
  (PTree.set _frame (Vptr bd (Ptrofs.repr base)) (create_undef_temps f_write128.(fn_temps))).

Lemma write128_body : f_write128.(fn_body) =
  Ssequence (Ssequence (write128_get_call Datatypes.true _t'1) (write128_write_call _t'1))
    (Ssequence (write128_get_call Datatypes.false _t'2) (write128_write_call _t'2)).
Proof. reflexivity. Qed.

Lemma call_write128_get high result e le m br base w :
  e!(u128_get_id high) = None -> le!_x = Some (Vptr br (Ptrofs.repr base)) ->
  frame_base_valid base -> Mem.load Mint64 m br (base + u128_field_offset high) = Some (Vlong w) ->
  Clight2.exec_stmt ge0 e le m (write128_get_call high result) E0 (PTree.set result (Vlong w) le) m Out_normal.
Proof.
  intros HE HX HB HL. eapply exec_Scall with
    (vf := Vptr (jet_symbol_block (u128_get_id high)) Ptrofs.zero)
    (vargs := [Vptr br (Ptrofs.repr base)]) (f := Internal (u128_get high)) (vres := Vlong w).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [exact HE|apply u128_get_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply eval_Etempvar; exact HX|reflexivity|apply eval_Enil].
  - apply u128_get_funct.
  - destruct high; reflexivity.
  - apply eval_u128_get_layout; assumption.
Qed.

Lemma call_write128_write result e le m mf bd base w :
  e!_simplicity_write64 = None -> le!_frame = Some (Vptr bd (Ptrofs.repr base)) -> le!result = Some (Vlong w) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_write64) [Vptr bd (Ptrofs.repr base); Vlong w] E0 mf Vundef ->
  Clight2.exec_stmt ge0 e le m (write128_write_call result) E0 le mf Out_normal.
Proof.
  intros HE HF HW HC. eapply exec_Scall with (vf := Vptr (jet_symbol_block _simplicity_write64) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr base); Vlong w]) (f := Internal f_simplicity_write64) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [exact HE|apply (wide_writer_symbol W64)].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply eval_Etempvar; exact HF|reflexivity|].
    eapply eval_Econs; [apply eval_Etempvar; exact HW|reflexivity|apply eval_Enil].
  - apply (wide_writer_funct W64).
  - reflexivity.
  - exact HC.
Qed.

Theorem eval_write128_layout m bd base bw edge cursor br rbase hi lo :
  frame_base_valid rbase -> br <> bd -> br <> bw ->
  Mem.load Mint64 m br (rbase + 8) = Some (Vlong hi) -> Mem.load Mint64 m br rbase = Some (Vlong lo) ->
  write_frame_at m bd base bw edge cursor 128 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_write128)
      [Vptr bd (Ptrofs.repr base); Vptr br (Ptrofs.repr rbase)] E0 mf Vundef /\
    frame_output_cells_at mf bw edge cursor
      (@encode (Word 7) (@fromZ (WordToZ 6) (Int64.unsigned hi), @fromZ (WordToZ 6) (Int64.unsigned lo))) /\
    write_prefix_at m mf bw edge cursor /\ frame_fields_at mf bd base bw edge (cursor - 128) /\
    loads_outside_ranges m mf bd (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - 128) / 64)) (write_word_address edge cursor + 8) /\
    (forall bb addr kind p, Mem.perm m bb addr kind p -> Mem.perm mf bb addr kind p) /\
    (forall bb, Mem.valid_block m bb -> Mem.valid_block mf bb).
Proof.
  intros HB ND NW HH HL Hout.
  destruct (write_wide_mixed_run_layout m bd base bw edge cursor [(W64,hi);(W64,lo)] Hout)
    as (mf & Hrun & Hcells & Hprefix & Hfields & Hmem & Hperm & Hvalid).
  cbn [write_wide_mixed_run] in Hrun.
  destruct Hrun as (mi & HW1 & HM1 & last & HW2 & HM2 & Hdone). subst last.
  assert (HLi : Mem.load Mint64 mi br rbase = Some (Vlong lo)).
  { rewrite HM1 by assumption. exact HL. }
  set (le0 := write128_temps bd base br rbase).
  set (le1 := PTree.set _t'1 (Vlong hi) le0). set (le2 := PTree.set _t'2 (Vlong lo) le1).
  exists mf. split.
  - eapply eval_funcall_internal with (e := PTree.empty _) (le1 := le0) (le2 := le2)
      (m1 := m) (m2 := mf) (out := Out_normal).
    + constructor.
      * constructor.
      * change (list_norepet [_frame; _x]). vm_compute.
        repeat (apply list_norepet_cons; [simpl; intuition discriminate|]). constructor.
      * change (list_disjoint [_frame; _x] [_t'2; _t'1]). vm_compute; intuition congruence.
      * constructor.
      * reflexivity.
    + rewrite write128_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mi).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
        -- eapply call_write128_get; [reflexivity|unfold le0, write128_temps; apply PTree.gss|exact HB|exact HH].
        -- eapply call_write128_write; [reflexivity|unfold le1, le0, write128_temps; rewrite PTree.gso by discriminate;
             rewrite PTree.gso by discriminate; apply PTree.gss|unfold le1; apply PTree.gss|exact HW1].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mi).
        -- eapply call_write128_get; [reflexivity|unfold le1, le0, write128_temps; rewrite PTree.gso by discriminate;
             apply PTree.gss|exact HB|change (Mem.load Mint64 mi br (rbase + 0) = Some (Vlong lo)); rewrite Z.add_0_r; exact HLi].
        -- eapply call_write128_write; [reflexivity|unfold le2, le1, le0, write128_temps;
             repeat rewrite PTree.gso by discriminate; apply PTree.gss|unfold le2; apply PTree.gss|exact HW2].
    + reflexivity.
    + reflexivity.
  - split.
    + change (frame_output_cells_at mf bw edge cursor
        (encode (decode_wide W64 (Int64.zero_ext 64 hi)) ++ (encode (decode_wide W64 (Int64.zero_ext 64 lo)) ++ []))) in Hcells.
      rewrite app_nil_r, !divmod128_wide_decode in Hcells by apply Int64.unsigned_range. exact Hcells.
    + split; [exact Hprefix|]. split; [exact Hfields|]. split; [exact Hmem|]. tauto.
Qed.
