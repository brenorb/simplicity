(** Generic lifecycle of the Bitcoin application-jet wrappers.  Every getter has
    the generated shape  [src_local = src; MID; return 1]  with one local
    (the by-value source frame copy).  This module derives, once, function entry,
    the 16-byte allocation and source copy, the final free, and the transport of
    the output/prefix/field/framing observations from the post-copy memory back to
    the initial memory.  Jet-specific modules supply only the MID execution. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge.
Set Default Timeout 10.

Definition bitcoin_copy_stmt : statement :=
  Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)).

Definition bitcoin_wrapper_body (mid : statement) : statement :=
  Ssequence bitcoin_copy_stmt
    (Ssequence mid (Sreturn (Some (Econst_int (Int.repr 1) tint)))).

Definition bitcoin_wrapper_params : list (ident * type) :=
  [(_dst, tptr (Tstruct _frameItem noattr)); (_src, Tstruct _frameItem noattr);
   (_env, tptr (Tstruct _txEnv noattr))].

Definition bitcoin_wrapper_temps (f : function) env bd dbase bs sbase : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase)) (create_undef_temps (fn_temps f)))).

(** The generated wrapper shape.  Per-jet consumers establish it by computation. *)
Definition bitcoin_wrapper_shape (f : function) (mid : statement) : Prop :=
  fn_return f = tbool /\ fn_vars f = [(_src, Tstruct _frameItem noattr)] /\
  fn_params f = bitcoin_wrapper_params /\ fn_body f = bitcoin_wrapper_body mid /\
  list_disjoint [_dst; _src; _env] (map fst (fn_temps f)).

Lemma bitcoin_wrapper_entry f mid env m ma bl bd dbase bs sbase :
  bitcoin_wrapper_shape f mid -> Mem.alloc m 0 16 = (ma, bl) ->
  function_entry2 bitcoin_ge f
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
    m (bitcoin_version_locals bl) (bitcoin_wrapper_temps f env bd dbase bs sbase) ma.
Proof.
  intros (HRet & HVars & HParams & HBody & HDisj) HA. constructor.
  - rewrite HVars. change (list_norepet [_src]). repeat constructor; simpl; tauto.
  - rewrite HParams. change (list_norepet [_dst; _src; _env]); unfold _dst, _src, _env.
    repeat constructor; simpl; intuition discriminate.
  - rewrite HParams. exact HDisj.
  - rewrite HVars. eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma, bl)); exact HA.
    + constructor.
  - rewrite HParams. reflexivity.
Qed.

Lemma bitcoin_wrapper_eval f mid env m ma mc me mf bl bd dbase bs sbase bytes le1 :
  bitcoin_wrapper_shape f mid ->
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl)
    (bitcoin_wrapper_temps f env bd dbase bs sbase) mc mid E0 le1 me Out_normal ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall bitcoin_ge m (Internal f)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HShape HB HS HD HA HL SC HMid HF.
  pose proof HShape as (HRet & HVars & HParams & HBody & HDisj).
  eapply eval_funcall_internal with (e := bitcoin_version_locals bl)
    (le1 := bitcoin_wrapper_temps f env bd dbase bs sbase) (le2 := le1)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply bitcoin_wrapper_entry; eassumption.
  - rewrite HBody. unfold bitcoin_wrapper_body, bitcoin_copy_stmt.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
      (le1 := bitcoin_wrapper_temps f env bd dbase bs sbase).
    + eapply exec_bitcoin_version_copy; [exact HB|exact HS|exact HD| |exact HL|exact SC].
      unfold bitcoin_wrapper_temps. rewrite PTree.gso by discriminate.
      apply PTree.gss.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := le1).
      * exact HMid.
      * apply exec_Sreturn_some, eval_Econst_int.
  - rewrite HRet. cbn; split; [discriminate|reflexivity].
  - change (Mem.free_list me [(bl,0,16)] = Some mf). cbn. rewrite HF; reflexivity.
Qed.

Lemma frame_output_cells_load_preserved m mf bw edge cursor cells :
  (forall ofs w, Mem.load Mint64 m bw ofs = Some (Vlong w) ->
    Mem.load Mint64 mf bw ofs = Some (Vlong w)) ->
  frame_output_cells_at m bw edge cursor cells -> frame_output_cells_at mf bw edge cursor cells.
Proof.
  intros HP HO.
  assert (HB : forall q bit, frame_output_bit_at m bw edge q bit -> frame_output_bit_at mf bw edge q bit).
  { intros q bit [HQ [w [HL HE]]]. split; [exact HQ|]. exists w. split; [apply HP; exact HL|exact HE]. }
  intros i c Hi. specialize (HO i c Hi). destruct c as [bit|]; cbn [cell_matches] in *.
  - apply HB; exact HO.
  - destruct HO as [bit Hbit]. exists bit. apply HB; exact Hbit.
Qed.

Theorem bitcoin_wrapper_layout f mid (cells : list Cell) env m bd dbase bs sbase bw edge cursor count bytes :
  bitcoin_wrapper_shape f mid ->
  frame_base_valid sbase -> (8 | sbase) -> Mem.loadbytes m bs sbase 16 = Some bytes ->
  0 < count ->
  write_frame_at m bd dbase bw edge cursor count ->
  (forall ma mc bl,
     Mem.alloc m 0 16 = (ma, bl) -> Mem.storebytes ma bl 0 bytes = Some mc ->
     (forall chunk b ofs v, Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v) ->
     (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mc b ofs kind p) ->
     write_frame_at mc bd dbase bw edge cursor count ->
     exists le1 me,
       Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl)
         (bitcoin_wrapper_temps f env bd dbase bs sbase) mc mid E0 le1 me Out_normal /\
       frame_output_cells_at me bw edge cursor cells /\
       write_prefix_at mc me bw edge cursor /\
       frame_fields_at me bd dbase bw edge (cursor - count) /\
       loads_outside_ranges mc me bd (dbase + 8) (dbase + 16) bw
         (edge + 8 * ((cursor - count) / 64)) (write_word_address edge cursor + 8) /\
       (forall b ofs kind p, Mem.perm mc b ofs kind p -> Mem.perm me b ofs kind p) /\
       (forall b, Mem.valid_block mc b -> Mem.valid_block me b)) ->
  exists mf,
    Clight2.eval_funcall bitcoin_ge m (Internal f)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw edge cursor cells /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bd dbase bw edge (cursor - count) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cursor - count) / 64) \/
        write_word_address edge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HShape HSbase HSAlign HB HCount HFrame.
  assert (HVs : Mem.valid_block m bs).
  { eapply Mem.perm_valid_block. eapply (Mem.loadbytes_range_perm _ _ _ _ _ HB sbase); lia. }
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA. intros HMid.
  assert (HLs : bl <> bs).
  { intro Heq; subst bs. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HVs). }
  pose proof HFrame as [HDbase [[HDE HDO] _]].
  destruct (write_frame_at_head m bd dbase bw edge cursor count HCount HFrame)
    as [_ [_ [_ [initialword HInitialWord]]]].
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (HBa : Mem.loadbytes ma bs sbase 16 = Some bytes).
  { erewrite Mem.loadbytes_alloc_unchanged; eauto. }
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hlen.
  assert (PL : Mem.range_perm ma bl 0 16 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_alloc_2; eauto. }
  assert (PLW : Mem.range_perm ma bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlen. change (Mem.range_perm ma bl 0 16 Cur Writable).
    intros ofs Hrange. eapply Mem.perm_implies; [apply PL; exact Hrange|constructor]. }
  destruct (Mem.range_perm_storebytes ma bl 0 bytes PLW) as [mc SC].
  assert (HBeforeLoad : forall chunk b ofs v,
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v).
  { intros chunk b ofs v HL.
    assert (Hbl : bl <> b) by (eapply fresh_frame_not_loaded; eauto).
    erewrite Mem.load_storebytes_other; [eapply Mem.load_alloc_other; eauto|exact SC|auto]. }
  assert (HBeforePerm : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mc b ofs kind p).
  { intros b ofs kind p HP. eapply Mem.perm_storebytes_1; [exact SC|]. eapply Mem.perm_alloc_1; eauto. }
  assert (HFrameC : write_frame_at mc bd dbase bw edge cursor count).
  { eapply write_frame_at_preserved with (m := m).
    - intros chunk b ofs v _ HL. apply HBeforeLoad; exact HL.
    - exact HBeforePerm.
    - exact HFrame. }
  destruct (HMid ma mc bl eq_refl SC HBeforeLoad HBeforePerm HFrameC)
    as (le1 & me & HExec & Houtput & Hprefix & Hfields & Hmemory & Hperm & Hvalid).
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Hrange. apply Hperm. eapply Mem.perm_storebytes_1; [exact SC|]. apply PL; exact Hrange. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mf HF].
  exists mf. split.
  - eapply bitcoin_wrapper_eval with (mc := mc) (me := me) (ma := ma) (bl := bl) (bytes := bytes);
      eauto.
  - split.
    + eapply frame_output_cells_load_preserved; [|exact Houtput].
      intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
    + split.
      * eapply write_prefix_at_preserved; [| |exact Hprefix].
        -- intros ofs w HL. eapply HBeforeLoad; eauto.
        -- intros ofs w HL. erewrite Mem.load_free; [exact HL|exact HF|auto].
      * split.
        -- destruct Hfields as [Hedge Hcursor]. split.
           ++ erewrite Mem.load_free; [exact Hedge|exact HF|auto].
           ++ erewrite Mem.load_free; [exact Hcursor|exact HF|auto].
        -- intros chunk b ofs HV Hbd Hbw.
           assert (Hbl : b <> bl).
           { intro Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV). }
           erewrite Mem.load_free; [|exact HF|auto].
           rewrite Hmemory by assumption.
           erewrite Mem.load_storebytes_other; [|exact SC|auto].
           eapply Mem.load_alloc_unchanged; eauto.
Qed.
