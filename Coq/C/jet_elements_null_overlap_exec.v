(** Original C null-data overlap execution, including both reads, output,
    source-copy allocation/free and a constructible aliased frame state.
    This diagnostic does not refute the separated BitMachine contract. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_writeBit_layout.
Require Import Simplicity.Word C.jet_word_repr C.jet_input_layout.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem tag_overwrites_unread_index m bd bw :
  bd <> bw ->
  frame_fields_at m bd 0 bw 0 261 ->
  Mem.valid_access m Mint64 bd 8 Writable ->
  Mem.valid_access m Mint64 bw 32 Writable ->
  Mem.load Mint64 m bw 32 = Some (Vlong Int64.zero) ->
  exists mo mf,
    Mem.store Mint64 m bd 8 (Vlong (Int64.repr 260)) = Some mo /\
    Mem.store Mint64 mo bw 32 (Vlong (Int64.repr 16)) = Some mf /\
    Clight2.eval_funcall ge0 m (Internal f_writeBit)
      [Vptr bd Ptrofs.zero; Vint Int.one] E0 mf (Vint Int.one) /\
    Mem.load Mint64 mf bw 32 = Some (Vlong (Int64.repr 16)) /\
    frame_fields_at mf bd 0 bw 0 260.
Proof.
  intros Separate Fields CursorAccess WordAccess Word.
  destruct (Mem.valid_access_store m Mint64 bd 8 (Vlong (Int64.repr 260)) CursorAccess)
    as (mo & CursorStore).
  assert (WordAccessO : Mem.valid_access mo Mint64 bw 32 Writable).
  { eapply Mem.store_valid_access_1; [exact CursorStore|exact WordAccess]. }
  destruct (Mem.valid_access_store mo Mint64 bw 32 (Vlong (Int64.repr 16)) WordAccessO)
    as (mf & WordStore).
  assert (Call : Clight2.eval_funcall ge0 m (Internal f_writeBit)
      [Vptr bd Ptrofs.zero; Vint Int.one] E0 mf (Vint Int.one)).
  { eapply (eval_writeBit_layout_raw m mo mf bd 0 bw 0 261 Int64.zero true).
    - unfold frame_base_valid. change (0 <= 0 /\ 16 <= 18446744073709551616). lia.
    - change (1 <= 261 <= 18446744073709551615). lia.
    - lia.
    - change (40 <= 18446744073709551615). lia.
    - exact Fields.
    - exact Word.
    - exact CursorStore.
    - exact WordStore.
    - left; exact Separate. }
  exists mo,mf. split; [exact CursorStore|]. split; [exact WordStore|].
  split; [exact Call|]. split.
  - exact (Mem.load_store_same _ _ _ _ _ _ WordStore).
  - destruct Fields as (Edge & Cursor). split.
    + rewrite (Mem.load_store_other _ _ _ _ _ _ WordStore Mptr bd 0)
        by (left; congruence).
      rewrite (Mem.load_store_other _ _ _ _ _ _ CursorStore Mptr bd 0)
        by (right; left; change (8 <= 8); lia).
      exact Edge.
    + change (Mem.load Mint64 mf bd 8 = Some (Vlong (Int64.repr 260))).
      rewrite (Mem.load_store_other _ _ _ _ _ _ WordStore Mint64 bd 8)
        by (left; congruence).
      exact (Mem.load_store_same _ _ _ _ _ _ CursorStore).
Qed.


Lemma word32_fromZ_value n : 0 <= n < 4294967296 ->
  @toZ (WordToZ 5) (@fromZ (WordToZ 5) n) = n.
Proof.
  intro N. rewrite to_fromZ.
  change (n mod 4294967296 = n). apply Z.mod_small; exact N.
Qed.

Lemma input32_low_word m bw n :
  0 <= n < 4294967296 ->
  Mem.load Mint64 m bw 32 = Some (Vlong (Int64.repr n)) ->
  frame_input_word_at m bw 40 32 (@fromZ (WordToZ 5) n).
Proof.
  intros N Load i bit At.
  assert (Index : (i < length (frame_input_word_bits (@fromZ (WordToZ 5) n)))%nat).
  { apply nth_error_Some. rewrite At; discriminate. }
  rewrite frame_input_word_bits_length in Index. change (i < 32)%nat in Index.
  unfold frame_input_word_bits in At.
  change (nth_error (map (fun j => Z.testbit (@toZ (WordToZ 5) (@fromZ (WordToZ 5) n))
    (Z.of_nat (32 - S j))) (seq 0 32)) i = Some bit) in At.
  rewrite nth_error_map, nth_error_seq_in in At by exact Index.
  change (Some (Z.testbit (@toZ (WordToZ 5) (@fromZ (WordToZ 5) n))
    (Z.of_nat (32 - S i))) = Some bit) in At.
  injection At as <-.
  unfold frame_input_bit_at.
  assert (Q : 0 <= 32 + Z.of_nat i < 64) by lia.
  split; [change (0 <= 32 + Z.of_nat i <= 18446744073709551615); lia|].
  split.
  - rewrite Z.div_small by exact Q.
    change (8 <= 40 <= 18446744073709551615). lia.
  - exists (Int64.repr n). split.
    + rewrite Z.div_small by exact Q. exact Load.
    + rewrite word32_fromZ_value by exact N.
      rewrite Int64.unsigned_repr by (change (0 <= n <= 18446744073709551615); lia).
      rewrite Z.mod_small by exact Q.
      assert (BitIndex : Z.of_nat (32 - S i) = 63 - (32 + Z.of_nat i)).
      { rewrite Nat2Z.inj_sub by lia. rewrite Nat2Z.inj_succ. lia. }
      exact (f_equal (Z.testbit n) BitIndex).
Qed.


Require Import C.jet_elements_linkage C.jet_elements_transport C.jet_wide.
Require C.jet_elements_current_reader.
Require Import C.jet_frame_constructible.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Require Import C.jet_elements_effects C.jet_output_layout C.jet_encoding.
Require Import C.jet_writeBit_layout_total C.jet_frame_spec.

(** Exact stores supply the ordinary output effect as well as the changed
    unread input; no determinism or execution premise is used. *)
Lemma tag_stores_effect m mo mt bd bw :
  Mem.load Mint64 m bw 32 = Some (Vlong Int64.zero) ->
  Mem.store Mint64 m bd 8 (Vlong (Int64.repr 260)) = Some mo ->
  Mem.store Mint64 mo bw 32 (Vlong (Int64.repr 16)) = Some mt ->
  frame_fields_at mt bd 0 bw 0 260 ->
  write_effect m mt bd 0 bw 0 261 1 [Some true].
Proof.
  intros Word SC SW Fields.
  assert (Out : Mem.load Mint64 mt bw 32 = Some (Vlong (Int64.repr 16))).
  { exact (Mem.load_store_same _ _ _ _ _ _ SW). }
  split.
  - intros [|i] c HC; [|destruct i; discriminate].
    injection HC as <-.
    split; [change (0 <= 260); lia|].
    exists (Int64.repr 16). split; [exact Out|reflexivity].
  - split.
    + intros old Load. change (Mem.load Mint64 m bw 32 = Some (Vlong old)) in Load.
      assert (old = Int64.zero) by congruence. subst old.
      exists (Int64.repr 16). split; [exact Out|].
      change (word_outside_eq 0 (write_word_shift 261)
        (write_bit_value 261 Int64.zero true) Int64.zero).
      apply write_bit_value_prefix. change (1 <= 261 <= 18446744073709551615); lia.
    + split; [exact Fields|]. split.
      * intros chunk b ofs HD HW.
        change (b <> bd \/ ofs + size_chunk chunk <= 8 \/ 16 <= ofs) in HD.
        change (b <> bw \/ ofs + size_chunk chunk <= 32 \/ 40 <= ofs) in HW.
        rewrite (Mem.load_store_other _ _ _ _ _ _ SW chunk b ofs) by (cbn; lia).
        exact (Mem.load_store_other _ _ _ _ _ _ SC chunk b ofs ltac:(cbn; lia)).
      * split.
        -- intros b ofs kind p HP. eauto using Mem.perm_store_1.
        -- intros b HV. eauto using Mem.store_valid_block_1.
Qed.


From compcert Require Import Maps.
Require Import C.jet_elements_null_data_output_guard C.jet_elements_bit_expr.
Require Import C.jet_elements_call.
Import Clightdefs.

Lemma overlap_outer_guard e le m bd bw be bt bout :
  bd <> bw ->
  e!C.jets_elements._writeBit = None ->
  le!C.jets_elements._dst = Some (Vptr bd Ptrofs.zero) ->
  le!C.jets_elements._env = Some (Vptr be Ptrofs.zero) ->
  le!C.jets_elements._i = Some (Vlong Int64.zero) ->
  elements_null_data_output_rep m be 0 bt 0 bout 0 Int64.zero Int64.one true ->
  frame_fields_at m bd 0 bw 0 261 ->
  Mem.valid_access m Mint64 bd 8 Writable ->
  Mem.valid_access m Mint64 bw 32 Writable ->
  Mem.load Mint64 m bw 32 = Some (Vlong Int64.zero) ->
  exists mo mt,
    Mem.store Mint64 m bd 8 (Vlong (Int64.repr 260)) = Some mo /\
    Mem.store Mint64 mo bw 32 (Vlong (Int64.repr 16)) = Some mt /\
    Clight2.exec_stmt elements_ge e le m elements_null_data_output_guard E0
      (elements_null_data_output_guard_temps bt 0 bout 0 Int64.zero Int64.one true le)
      mt Out_normal /\
    write_effect m mt bd 0 bw 0 261 1 [Some true] /\
    Mem.load Mint64 mt bw 32 = Some (Vlong (Int64.repr 16)).
Proof.
  intros DB HW HD HE HI Rep Fields DC WC Word.
  destruct (tag_overwrites_unread_index m bd bw DB Fields DC WC Word)
    as (mo & mt & SC & SW & CoreCall & Out & FieldsT).
  assert (Call : Clight2.eval_funcall elements_ge m (Internal C.jets.f_writeBit)
    [Vptr bd Ptrofs.zero; Vint Int.one] E0 mt (Vint Int.one)).
  { eapply elements_transport_call; [|exact CoreCall].
    unfold elements_core_helpers; cbn; tauto. }
  set (next := elements_null_data_output_prefix_temps bt 0 bout 0 Int64.zero Int64.one true le).
  assert (DN : next!C.jets_elements._dst = Some (Vptr bd Ptrofs.zero)).
  { unfold next. rewrite elements_null_data_output_prefix_other; [exact HD|].
    vm_compute; intuition discriminate. }
  assert (Bit : next!C.jets_elements._t'7 = Some (Vint Int.one)).
  { unfold next. apply elements_null_data_output_prefix_value. }
  exists mo,mt. split; [exact SC|]. split; [exact SW|]. split.
  - unfold elements_null_data_output_guard, elements_null_data_output_guard_temps.
    change (andb (Int64.ltu Int64.zero Int64.one) true) with true.
    fold next.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := next).
    + exact (exec_elements_null_data_output_prefix e le m be 0 bt 0 bout 0
        Int64.zero Int64.one true HE HI Rep).
    + unfold elements_bit_expr_stmt.
      eapply exec_elements_helper_call with (f := C.jets.f_writeBit)
        (vargs := [Vptr bd Ptrofs.zero; Vint Int.one]) (vres := Vint Int.one).
      * unfold elements_core_helpers; cbn; tauto.
      * exact HW.
      * eapply eval_Econs; [apply eval_Etempvar; exact DN|reflexivity|].
        eapply eval_Econs; [apply eval_Etempvar; exact Bit|reflexivity|apply eval_Enil].
      * reflexivity.
      * exact Call.
  - split; [eapply tag_stores_effect; eassumption|exact Out].
Qed.


Require Import Simplicity.Digest C.jet_elements_prim.
Require Import C.jet_elements_null_data_read_index C.jet_elements_null_data_guard_compose.
Require Import C.jet_elements_null_data_index.

(** The complete generated guard block, starting immediately after the first
    input read. Its changed second index follows from stores, not a premise. *)
Theorem overlap_guard_runs_absent e le m bl bd bw be bt bout :
  bd <> bw -> bl <> bd -> bl <> bw -> bl <> be -> bl <> bt -> bl <> bout ->
  e!C.jets_elements._simplicity_read32 = None ->
  e!C.jets_elements._src = Some (bl, Tstruct C.jets_elements._frameItem noattr) ->
  e!C.jets_elements._writeBit = None -> e!C.jets_elements._skipBits = None ->
  e!C.jets_elements._writeHash = None ->
  le!C.jets_elements._dst = Some (Vptr bd Ptrofs.zero) ->
  le!C.jets_elements._env = Some (Vptr be Ptrofs.zero) ->
  le!C.jets_elements._i = Some (Vlong Int64.zero) ->
  elements_null_data_output_rep m be 0 bt 0 bout 0 Int64.zero Int64.one true ->
  elements_null_data_count_path m be 0 bt 0 bout 0 Int64.zero Int64.one ->
  Forall (fun '(b,lo,hi) => C.jet_application_sep.out_sep bd 0 bw 0 261 261 b lo hi)
    (elements_null_data_count_footprint be 0 bt 0 bout 0 Int64.zero) ->
  frame_fields_at m bl 0 bw 40 32 ->
  Mem.valid_access m Mint64 bl 8 Writable ->
  write_frame_at m bd 0 bw 0 261 261 ->
  Mem.load Mint64 m bw 32 = Some (Vlong Int64.zero) ->
  exists le' mf,
    Clight2.exec_stmt elements_ge e le m elements_null_data_guard_block E0 le' mf Out_normal /\
    write_effect_private bl m mf bd 0 bw 0 261 261
      ([Some true; Some false] ++ repeat None 259).
Proof.
  intros DB LD LW LE LT LO HR HS HW HK HH HD HE HI Rep Count Sep Source LC Frame Word.
  pose proof Frame as (_ & Out & _ & _ & _ & DC & _).
  destruct (write_frame_at_head m bd 0 bw 0 261 261 ltac:(lia) Frame)
    as (_ & _ & WC & _).
  change (Mem.valid_access m Mint64 bw 32 Writable) in WC.
  destruct (overlap_outer_guard e le m bd bw be bt bout DB HW HD HE HI Rep Out DC WC Word)
    as (mo & mt & SC & SW & Guard & Eff & Changed).
  set (next := elements_null_data_output_guard_temps bt 0 bout 0 Int64.zero Int64.one true le).
  assert (SourceT : frame_fields_at mt bl 0 bw 40 32).
  { destruct Source as (SE & SCur). split.
    - rewrite (Mem.load_store_other _ _ _ _ _ _ SW Mptr bl 0) by (left; congruence).
      rewrite (Mem.load_store_other _ _ _ _ _ _ SC Mptr bl 0) by (left; congruence).
      exact SE.
    - change (Mem.load Mint64 mt bl 8 = Some (Vlong (Int64.repr 32))).
      rewrite (Mem.load_store_other _ _ _ _ _ _ SW Mint64 bl 8) by (left; congruence).
      rewrite (Mem.load_store_other _ _ _ _ _ _ SC Mint64 bl 8) by (left; congruence).
      exact SCur. }
  assert (LCT : Mem.valid_access mt Mint64 bl 8 Writable).
  { eapply Mem.store_valid_access_1; [exact SW|].
    eapply Mem.store_valid_access_1; [exact SC|exact LC]. }
  assert (CountT : elements_null_data_count_path mt be 0 bt 0 bout 0 Int64.zero Int64.one).
  { exact (elements_null_data_count_after_tag m mt bd 0 bw 0 261 true
      be 0 bt 0 bout 0 Int64.zero Int64.one ltac:(lia) Eff Sep Count). }
  assert (FrameT : write_frame_at mt bd 0 bw 0 260 260).
  { eapply write_frame_at_after_effect with (m := m) (cursor := 261) (n := 1) (cells := [Some true]);
      [reflexivity|lia|exact Frame|exact Eff]. }
  assert (DN : next!C.jets_elements._dst = Some (Vptr bd Ptrofs.zero)).
  { unfold next. rewrite elements_null_data_output_guard_other; [exact HD|].
    vm_compute; intuition discriminate. }
  assert (EN : next!C.jets_elements._env = Some (Vptr be Ptrofs.zero)).
  { unfold next. rewrite elements_null_data_output_guard_other; [exact HE|].
    vm_compute; intuition discriminate. }
  assert (IN : next!C.jets_elements._i = Some (Vlong Int64.zero)).
  { unfold next. rewrite elements_null_data_output_guard_other; [exact HI|].
    vm_compute; intuition discriminate. }
  assert (Selected : forall r, Int64.unsigned r = toZ (@fromZ (WordToZ 5) 16) ->
    elements_null_data_selected_private mt bl bd 0 bw 0 260 be 0 bt 0 bout 0 Int64.zero r
      [OP1] (byteStringHash [])).
  { intros r Value d At. rewrite word32_fromZ_value in Value by lia.
    rewrite Value in At. discriminate. }
  destruct (exec_elements_null_data_read_index_block [OP1] (byteStringHash []) e next mt
    bl bd 0 bw 0 260 bw 40 32 (@fromZ (WordToZ 5) 16) be 0 bt 0 bout 0 Int64.zero
    HR HS HW HK HH DN EN IN ltac:(change (0 <= 32 <= 18446744073709551615 - 32); lia)
    SourceT (input32_low_word mt bw 16 ltac:(lia) Changed) LCT LW LD LW LE LT LO
    ltac:(change (1 <= 18446744073709551615); lia) CountT Selected FrameT)
    as (le' & mf & r & Value & Index & Private & mr & Loads & Perm & Valid & IndexEff).
  rewrite word32_fromZ_value in Value by lia.
  assert (R : r = Int64.repr 16).
  { rewrite <- (Int64.repr_unsigned r) at 1. rewrite Value. reflexivity. }
  subst r.
  change (write_effect mr mf bd 0 bw 0 260 260 ([Some false] ++ repeat None 259)) in IndexEff.
  exists le',mf. split.
  - unfold elements_null_data_guard_block.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Guard|].
    eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
    + apply eval_Etempvar. unfold next. apply elements_null_data_output_guard_value.
    + reflexivity.
    + exact Index.
  - change 261 with (1 + 260) at 2.
    eapply write_effect_private_interleaved with (m1 := mt) (mr := mr);
      [exact LW|lia|exact Frame|exact Eff|exact Loads|exact Perm|exact Valid|exact IndexEff].
Qed.


Require Import C.jet_elements_null_data_rest C.jet_elements_current_reader C.jet_elements_wrapper.

Theorem overlap_rest_runs_absent e le m bl bd bw be bt bout :
  bd <> bw -> bl <> bd -> bl <> bw -> bl <> be -> bl <> bt -> bl <> bout ->
  e!C.jets_elements._simplicity_read32 = None ->
  e!C.jets_elements._src = Some (bl, Tstruct C.jets_elements._frameItem noattr) ->
  e!C.jets_elements._writeBit = None -> e!C.jets_elements._skipBits = None ->
  e!C.jets_elements._writeHash = None ->
  le!C.jets_elements._dst = Some (Vptr bd Ptrofs.zero) ->
  le!C.jets_elements._env = Some (Vptr be Ptrofs.zero) ->
  elements_null_data_output_rep m be 0 bt 0 bout 0 Int64.zero Int64.one true ->
  elements_null_data_count_path m be 0 bt 0 bout 0 Int64.zero Int64.one ->
  Forall (fun '(b,lo,hi) => C.jet_application_sep.out_sep bd 0 bw 0 261 261 b lo hi)
    (elements_null_data_count_footprint be 0 bt 0 bout 0 Int64.zero) ->
  frame_fields_at m bl 0 bw 40 0 ->
  frame_input_word_at m bw 40 0 (@fromZ (WordToZ 5) 0) ->
  Mem.valid_access m Mint64 bl 8 Writable ->
  write_frame_at m bd 0 bw 0 261 261 ->
  Mem.load Mint64 m bw 32 = Some (Vlong Int64.zero) ->
  exists le' mf,
    Clight2.exec_stmt elements_ge e le m elements_null_data_rest E0 le' mf elements_returned_one /\
    write_effect_private bl m mf bd 0 bw 0 261 261
      ([Some true; Some false] ++ repeat None 259).
Proof.
  intros DB LD LW LE LT LO HR HS HW HK HH HD HE Rep Count Sep Source Input LC Frame Word.
  destruct (exec_elements_read32_current C.jets_elements._t'1 C.jets_elements._i e le m
    bl bw 40 0 (@fromZ (WordToZ 5) 0) HR HS
    ltac:(change (0 <= 0 <= 18446744073709551615 - 32); lia) Source Input LC LW)
    as (mr & r & Read & Value & SourceR & Loads & Perm & Valid).
  rewrite word32_fromZ_value in Value by lia.
  assert (R : r = Int64.zero).
  { rewrite <- (Int64.repr_unsigned r) at 1. rewrite Value. reflexivity. }
  subst r.
  assert (HM : forall chunk b ofs, b <> bl -> Mem.load chunk mr b ofs = Mem.load chunk m b ofs).
  { intros chunk b ofs HB. apply Loads; left; exact HB. }
  set (next := PTree.set C.jets_elements._i (Vlong Int64.zero)
    (PTree.set C.jets_elements._t'1 (Vlong Int64.zero) le)).
  assert (DN : next!C.jets_elements._dst = Some (Vptr bd Ptrofs.zero)).
  { unfold next. rewrite !PTree.gso by discriminate. exact HD. }
  assert (EN : next!C.jets_elements._env = Some (Vptr be Ptrofs.zero)).
  { unfold next. rewrite !PTree.gso by discriminate. exact HE. }
  assert (IN : next!C.jets_elements._i = Some (Vlong Int64.zero)).
  { unfold next. apply PTree.gss. }
  assert (RepR : elements_null_data_output_rep mr be 0 bt 0 bout 0 Int64.zero Int64.one true).
  { eapply elements_null_data_output_rep_read_preserved; eassumption. }
  assert (CountR : elements_null_data_count_path mr be 0 bt 0 bout 0 Int64.zero Int64.one).
  { eapply elements_null_data_count_path_read_preserved; eassumption. }
  assert (FrameR : write_frame_at mr bd 0 bw 0 261 261).
  { eapply write_frame_at_preserved with (m := m); [|exact Perm|exact Frame].
    intros chunk b ofs v HB HL. rewrite HM; [exact HL|]. destruct HB; subst; congruence. }
  assert (LCR : Mem.valid_access mr Mint64 bl 8 Writable).
  { destruct LC as (LP & LA). split; [|exact LA]. intros ofs Range. apply Perm, LP; exact Range. }
  assert (WordR : Mem.load Mint64 mr bw 32 = Some (Vlong Int64.zero)).
  { rewrite HM by congruence. exact Word. }
  destruct (overlap_guard_runs_absent e next mr bl bd bw be bt bout
    DB LD LW LE LT LO HR HS HW HK HH DN EN IN RepR CountR Sep SourceR LCR FrameR WordR)
    as (le' & mf & Guard & Eff).
  exists le',mf. split.
  - unfold elements_null_data_rest.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact Read|].
    apply exec_elements_simple_rest; exact Guard.
  - eapply write_effect_private_lift_source; [exact LW|exact HM|exact Perm|exact Valid|exact Eff].
Qed.


Require Import C.jet_elements_null_data_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jet_bitmachine_rep C.jet_elements_version_exec.

(** Full original public call under physical initial-state predicates. No
    execution, allocation, initialized private-local, or output premise. A
    closed consistent-environment witness is still a separate obligation. *)
Theorem overlap_public_runs_absent m bd bs bw be bt bout :
  bd <> bw ->
  frame_fields_at m bs 0 bw 40 0 ->
  frame_input_word_at m bw 40 0 (@fromZ (WordToZ 5) 0) ->
  elements_null_data_output_rep m be 0 bt 0 bout 0 Int64.zero Int64.one true ->
  elements_null_data_count_path m be 0 bt 0 bout 0 Int64.zero Int64.one ->
  Forall (fun '(b,lo,hi) => C.jet_application_sep.out_sep bd 0 bw 0 261 261 b lo hi)
    (elements_null_data_count_footprint be 0 bt 0 bout 0 Int64.zero) ->
  write_frame_at m bd 0 bw 0 261 261 ->
  Mem.load Mint64 m bw 32 = Some (Vlong Int64.zero) ->
  exists mf,
    Clight2.eval_funcall elements_ge m (Internal C.jets_elements.f_simplicity_output_null_datum)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vptr be Ptrofs.zero] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw 0 261 ([Some true; Some false] ++ repeat None 259) /\
    write_prefix_at m mf bw 0 261 /\ frame_fields_at mf bd 0 bw 0 0 /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= 8 \/ 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= 0 \/ 40 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros DB Fields Input Rep Count Sep Frame Word.
  pose proof Fields as (SE & SCur).
  destruct (frame_loadbytes_at m bs 0 _ _ SE SCur) as (bytes & Bytes).
  eapply elements_wrapper_layout with (rest := elements_null_data_rest) (bytes := bytes)
    (f := C.jets_elements.f_simplicity_output_null_datum) (env := Vptr be Ptrofs.zero)
    (dbase := 0) (sbase := 0) (edge := 0) (cursor := 261) (count := 261);
    [exact elements_null_data_layout_shape| | |exact Bytes|lia|exact Frame|].
  - unfold frame_base_valid. change (0 <= 0 /\ 16 <= 18446744073709551616). lia.
  - exists 0. reflexivity.
  - intros ma mc bl HA SC HM HP FrameC.
    assert (VS : Mem.valid_block m bs) by (eapply load_valid_block; exact SE).
    assert (BytesA : Mem.loadbytes ma bs 0 16 = Some bytes).
    { erewrite Mem.loadbytes_alloc_unchanged; eauto. }
    assert (SEA : Mem.load Mptr ma bs 0 = Some (Vptr bw (Ptrofs.repr 40)))
      by (eapply Mem.load_alloc_other; eauto).
    assert (SCA : Mem.load Mint64 ma bs 8 = Some (Vlong (Int64.repr 0)))
      by (eapply Mem.load_alloc_other; eauto).
    destruct (frame_copy_fields_at ma mc bs 0 bl bytes _ _ BytesA SC SEA SCA)
      as (LEdge & LCur).
    assert (InputC : frame_input_word_at mc bw 40 0 (@fromZ (WordToZ 5) 0)).
    { eapply frame_input_bits_at_preserved; [|exact Input]. intros ofs w HL. apply HM; exact HL. }
    assert (LC : Mem.valid_access mc Mint64 bl 8 Writable).
    { eapply Mem.storebytes_valid_access_1; [exact SC|].
      eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
      eapply Mem.valid_access_alloc_same; [exact HA|lia|cbn; lia|]. exists 1; reflexivity. }
    pose proof Frame as (_ & (DEdge & DCur) & _).
    pose proof Rep as (_ & _ & _ & _ & EPtr & TCount & _).
    pose proof Count as (_ & _ & _ & _ & _ & _ & _ & _ & OCount).
    assert (LW : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
    assert (LD : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
    assert (LE : bl <> be) by (eapply fresh_frame_not_loaded; eauto).
    assert (LT : bl <> bt) by (eapply fresh_frame_not_loaded; eauto).
    assert (LO : bl <> bout) by (eapply fresh_frame_not_loaded; eauto).
    assert (RepC : elements_null_data_output_rep mc be 0 bt 0 bout 0 Int64.zero Int64.one true).
    { eapply elements_null_data_output_rep_mono; eassumption. }
    assert (CountC : elements_null_data_count_path mc be 0 bt 0 bout 0 Int64.zero Int64.one).
    { eapply elements_null_data_count_path_mono; eassumption. }
    assert (WordC : Mem.load Mint64 mc bw 32 = Some (Vlong Int64.zero)) by (apply HM; exact Word).
    destruct (overlap_rest_runs_absent (elements_version_locals bl)
      (elements_wrapper_temps C.jets_elements.f_simplicity_output_null_datum
        (Vptr be Ptrofs.zero) bd 0 bs 0) mc bl bd bw be bt bout
      DB LD LW LE LT LO eq_refl eq_refl eq_refl eq_refl eq_refl
      ltac:(unfold elements_wrapper_temps; rewrite !PTree.gso by discriminate; apply PTree.gss)
      ltac:(unfold elements_wrapper_temps; apply PTree.gss)
      RepC CountC Sep (conj LEdge LCur) InputC LC FrameC WordC)
      as (le' & mf & Call & Eff).
    exists le',mf. exact (conj Call Eff).
Qed.


Lemma input32_zero_in_shared_word m bw rc :
  0 <= rc <= 32 ->
  Mem.load Mint64 m bw 32 = Some (Vlong Int64.zero) ->
  frame_input_word_at m bw 40 rc (@fromZ (WordToZ 5) 0).
Proof.
  intros RC Load i bit At.
  assert (Index : (i < 32)%nat).
  { assert (i < length (frame_input_word_bits (@fromZ (WordToZ 5) 0)))%nat.
    { apply nth_error_Some. rewrite At; discriminate. }
    rewrite frame_input_word_bits_length in H. exact H. }
  unfold frame_input_word_bits in At.
  change (nth_error (map (fun j => Z.testbit (@toZ (WordToZ 5) (@fromZ (WordToZ 5) 0))
    (Z.of_nat (32 - S j))) (seq 0 32)) i = Some bit) in At.
  rewrite nth_error_map, nth_error_seq_in in At by exact Index.
  change (Some (Z.testbit (@toZ (WordToZ 5) (@fromZ (WordToZ 5) 0))
    (Z.of_nat (32 - S i))) = Some bit) in At.
  rewrite word32_fromZ_value, Z.bits_0 in At by lia. injection At as <-.
  unfold frame_input_bit_at.
  assert (Q : 0 <= rc + Z.of_nat i < 64) by lia.
  split; [change (0 <= rc + Z.of_nat i <= 18446744073709551615); lia|].
  split.
  - rewrite Z.div_small by exact Q. change (8 <= 40 <= 18446744073709551615); lia.
  - exists Int64.zero. split; [rewrite Z.div_small by exact Q; exact Load|].
    change (false = Z.testbit 0 (63 - (rc + Z.of_nat i) mod 64)).
    symmetry; apply Z.bits_0.
Qed.

(** The aliased frames are constructible; the environment is built first,
    then kept intact in these fresh allocations. *)
Theorem overlap_frames_constructible (m0 : mem) :
  exists m bd bs bw,
    bd <> bw /\ frame_fields_at m bs 0 bw 40 0 /\
    frame_input_word_at m bw 40 0 (@fromZ (WordToZ 5) 0) /\
    write_frame_at m bd 0 bw 0 261 261 /\
    Mem.load Mint64 m bw 32 = Some (Vlong Int64.zero) /\
    (forall b, Mem.valid_block m0 b ->
      b <> bd /\ b <> bw /\
      forall chunk ofs, Mem.load chunk m b ofs = Mem.load chunk m0 b ofs).
Proof.
  destruct (alloc_word_run m0 (repeat (Vlong Int64.zero) 5))
    as (m1 & bw & FreshW & VW & Words & WA & WP & WO & WX & WPerm & WV).
  destruct (alloc_word_run m1 [Vptr bw Ptrofs.zero; Vlong (Int64.repr 261)])
    as (m2 & bd & FreshD & VD & DWords & DA & DP & DO & DX & DPerm & DV).
  destruct (alloc_word_run m2 [Vptr bw (Ptrofs.repr 40); Vlong Int64.zero])
    as (m & bs & FreshS & VS & SWords & SA & SP & SO & SX & SPerm & SV).
  assert (VW2 : Mem.valid_block m2 bw) by (apply DV; exact VW).
  assert (DB : bd <> bw) by (intro E; subst; exact (FreshD VW)).
  assert (Zero : Mem.load Mint64 m bw 32 = Some (Vlong Int64.zero)).
  { rewrite SO by exact VW2. rewrite DO by exact VW. exact (Words 4%nat _ eq_refl). }
  exists m,bd,bs,bw. split; [exact DB|]. split.
  - split; [exact (SWords 0%nat _ eq_refl)|exact (SWords 1%nat _ eq_refl)].
  - split; [apply input32_zero_in_shared_word; [lia|exact Zero]|]. split.
    + apply output_run_frame; [change (0 <= 261 <= 18446744073709551615); lia|exact DB| | | | |].
      * change (Mem.load Mint64 m bd 0 = Some (Vptr bw Ptrofs.zero)).
        rewrite SO by exact VD. exact (DWords 0%nat _ eq_refl).
      * rewrite SO by exact VD. exact (DWords 1%nat _ eq_refl).
      * apply SX; [exact VD|exact (DA 1%nat ltac:(cbn;lia))].
      * intros i v At. rewrite SO by exact VW2. rewrite DO by exact VW. apply Words; exact At.
      * intros i At. apply SX; [exact VW2|]. apply DX; [exact VW|]. apply WA; exact At.
    + split; [exact Zero|]. intros b VB. split.
      * intro E; subst. exact (FreshD (WV _ VB)).
      * split; [intro E; subst; exact (FreshW VB)|]. intros chunk ofs.
        rewrite SO by (apply DV,WV;exact VB).
        rewrite DO by (apply WV;exact VB). apply WO; exact VB.
Qed.
