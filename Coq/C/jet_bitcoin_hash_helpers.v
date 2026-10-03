(** The static Bitcoin helpers writeHash and prevOutpoint, executed from initial
    memory: writeHash copies eight hash words with write32s, prevOutpoint is a
    writeHash of the txid followed by a write32 of the output index. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_uint32_array_init C.jet_application_sep.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_field_eval C.jet_bitcoin_effects.
Require Import C.jet_output_layout_step C.jet_wide C.jet_wide_spec C.jet_bitcoin_steps C.jet_bitcoin_env_load C.jet_bitcoin_write32s_layout C.jet_bitcoin_hash_write C.jet_bitcoin_call.
Require C.jets.
Require Import C.jet_bitcoin_transport.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge ge0.
Set Default Timeout 60.

Lemma eval_bitcoin_midstate_array e le m x b hbase :
  le!x = Some (Vptr b (Ptrofs.repr hbase)) -> 0 <= hbase ->
  eval_expr bitcoin_ge e le m
    (Efield (Ederef (Etempvar x (tptr (Tstruct _sha256_midstate noattr))) (Tstruct _sha256_midstate noattr))
      _s (tarray tuint 8)) (Vptr b (Ptrofs.repr hbase)).
Proof.
  intros HX H0.
  assert (Hr : Ptrofs.repr hbase = Ptrofs.add (Ptrofs.repr hbase) (Ptrofs.repr 0))
    by (rewrite Ptrofs.add_zero; reflexivity).
  rewrite Hr.
  eapply eval_bitcoin_field_array with (sid := _sha256_midstate) (delta := 0);
    [reflexivity|exact bitcoin_midstate_s|intros chunk; discriminate|reflexivity|].
  apply eval_bitcoin_deref_struct; exact HX.
Qed.

Theorem eval_bitcoin_writeHash_layout m bh hbase bf base bw edge cursor xs :
  length xs = 8%nat -> 0 <= hbase -> hbase + 32 <= Ptrofs.max_unsigned ->
  out_sep bf base bw edge cursor 256 bh hbase (hbase + 32) ->
  uint32_array_at m bh hbase xs ->
  write_frame_at m bf base bw edge cursor 256 ->
  exists mf,
    Clight2.eval_funcall bitcoin_ge m (Internal f_writeHash)
      [Vptr bf (Ptrofs.repr base); Vptr bh (Ptrofs.repr hbase)] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor 256 (hash_cells xs).
Proof.
  intros HL H0 HM HSep HA HF.
  destruct (eval_bitcoin_write_hash_array m bh hbase bf base bw edge cursor xs HL H0 HM HSep HA HF)
    as (mf & HCall & HEff).
  exists mf. split; [|exact HEff].
  set (le := PTree.set _h (Vptr bh (Ptrofs.repr hbase))
    (PTree.set _dst (Vptr bf (Ptrofs.repr base)) (create_undef_temps (fn_temps f_writeHash)))).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le) (le2 := le)
    (m1 := m) (m2 := mf) (out := Out_normal).
  - constructor.
    + constructor.
    + change (list_norepet [_dst; _h]). unfold _dst, _h. repeat constructor; simpl; intuition discriminate.
    + intros i j HI HJ. cbn in HI, HJ. contradiction.
    + constructor.
    + reflexivity.
  - unfold f_writeHash; cbn [fn_body].
    assert (Hargs : eval_exprlist bitcoin_ge empty_env le m
      [Etempvar _dst (tptr (Tstruct _frameItem noattr));
       Efield (Ederef (Etempvar _h (tptr (Tstruct _sha256_midstate noattr))) (Tstruct _sha256_midstate noattr))
         _s (tarray tuint 8);
       Econst_int (Int.repr 8) tint]
      (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr tuint) (Tcons tulong Tnil)))
      [Vptr bf (Ptrofs.repr base); Vptr bh (Ptrofs.repr hbase); Vlong (Int64.repr 8)]).
    { eapply eval_Econs; [apply eval_Etempvar; unfold le; rewrite PTree.gso by discriminate; apply PTree.gss|reflexivity|].
      eapply eval_Econs; [eapply eval_bitcoin_midstate_array; [unfold le; apply PTree.gss|exact H0]|reflexivity|].
      eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil]. }
    exact (exec_bitcoin_helper_call empty_env le m None _write32s jets.f_write32s _ _ _ _ _ _ mf
      ltac:(unfold bitcoin_core_helpers; simpl; tauto) ltac:(reflexivity) Hargs ltac:(reflexivity)
      HCall).
  - reflexivity.
  - reflexivity.
Qed.

Lemma bitcoin_outpoint_txid : bitcoin_field_at _outpoint _txid 0.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_outpoint_ix : bitcoin_field_at _outpoint _ix 32.
Proof. vm_compute; reflexivity. Qed.

Definition bitcoin_outpoint_cells (xs : list int) (ixv : int64) : list Cell :=
  hash_cells xs ++ encode (decode_wide W32 (Int64.zero_ext (wide_bits W32) ixv)).

Theorem eval_bitcoin_prevOutpoint_layout m bo obase bf base bw edge cursor xs ixv :
  length xs = 8%nat -> 0 <= obase -> obase + 40 <= Ptrofs.max_unsigned ->
  out_sep bf base bw edge cursor 288 bo obase (obase + 40) ->
  uint32_array_at m bo obase xs -> Mem.load Mint64 m bo (obase + 32) = Some (Vlong ixv) ->
  write_frame_at m bf base bw edge cursor 288 ->
  exists mf,
    Clight2.eval_funcall bitcoin_ge m (Internal f_prevOutpoint)
      [Vptr bf (Ptrofs.repr base); Vptr bo (Ptrofs.repr obase)] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor 288 (bitcoin_outpoint_cells xs ixv).
Proof.
  intros HL H0 HM HSep HA HIx HF.
  pose proof HF as [_ [_ [_ [HCur _]]]].
  assert (HSepH : out_sep bf base bw edge cursor 256 bo obase (obase + 32)).
  { destruct HSep as [Hf Hw]. unfold out_sep, out_low, out_high in *.
    pose proof (Z.div_le_mono (cursor - 288) (cursor - 256) 64 ltac:(lia) ltac:(lia)) as Hd.
    split; [destruct Hf as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]|].
    destruct Hw as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]. }
  assert (HF256 : write_frame_at m bf base bw edge cursor 256).
  { eapply write_frame_at_shorter; [|exact HF]. lia. }
  destruct (eval_bitcoin_writeHash_layout m bo obase bf base bw edge cursor xs HL H0 ltac:(lia) HSepH HA HF256)
    as (mh & HCallH & E1).
  assert (Hw32 : wide_bits W32 = 32) by reflexivity.
  assert (HFb : write_frame_at mh bf base bw edge (cursor - 256) (wide_bits W32)).
  { eapply write_frame_at_after_effect with (cells := hash_cells xs) (m := m);
      [apply hash_cells_length_Z; exact HL|lia| |exact E1].
    change (256 + wide_bits W32) with 288. exact HF. }
  assert (HIxB : Mem.load Mint64 mh bo (obase + 32) = Some (Vlong ixv)).
  { rewrite <- HIx. eapply write_effect_env_load with (bf := bf) (base := base) (bw := bw) (edge := edge)
      (cursor := cursor) (cursor0 := cursor) (count0 := 288) (n := 256) (cells := hash_cells xs)
      (lo := obase) (hi := obase + 40); [lia|lia|lia|lia|exact E1|exact HSep|lia|change (size_chunk Mint64) with 8; lia]. }
  destruct (bitcoin_write_wide_step W32 mh bf base bw edge (cursor - 256) ixv HFb) as (mf & HCallW & E2).
  exists mf. split.
  - set (le := PTree.set _op (Vptr bo (Ptrofs.repr obase))
      (PTree.set _dst (Vptr bf (Ptrofs.repr base)) (create_undef_temps (fn_temps f_prevOutpoint)))).
    eapply eval_funcall_internal with (e := empty_env)
      (le1 := le) (le2 := PTree.set _t'1 (Vlong ixv) le) (m1 := m) (m2 := mf) (out := Out_normal).
    + constructor.
      * constructor.
      * change (list_norepet [_dst; _op]). unfold _dst, _op. repeat constructor; simpl; intuition discriminate.
      * intros i j HI HJ. cbn in HI, HJ.
        destruct HI as [HI|[HI|HI]]; [|destruct HJ as [HJ|HJ]|contradiction];
          try (destruct HJ as [HJ|HJ]); vm_compute in HI, HJ; congruence.
      * constructor.
      * reflexivity.
    + unfold f_prevOutpoint; cbn [fn_body].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mh) (le1 := le).
      * eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block _writeHash) Ptrofs.zero)
          (f := Internal f_writeHash)
          (vargs := [Vptr bf (Ptrofs.repr base); Vptr bo (Ptrofs.repr obase)]) (vres := Vundef).
        -- reflexivity.
        -- eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact bitcoin_writeHash_symbol]|
             apply deref_loc_reference; reflexivity].
        -- eapply eval_Econs; [apply eval_Etempvar; unfold le; rewrite PTree.gso by discriminate; apply PTree.gss|reflexivity|].
           assert (Harg : eval_expr bitcoin_ge empty_env le m
             (Eaddrof (Efield (Ederef (Etempvar _op (tptr (Tstruct _outpoint noattr))) (Tstruct _outpoint noattr))
               _txid (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr)))
             (Vptr bo (Ptrofs.repr obase))).
           { eapply eval_Eaddrof.
             assert (Hr : Ptrofs.repr obase = Ptrofs.add (Ptrofs.repr obase) (Ptrofs.repr 0))
               by (rewrite Ptrofs.add_zero; reflexivity).
             rewrite Hr.
             eapply eval_bitcoin_field_lvalue; [reflexivity|exact bitcoin_outpoint_txid|].
             apply eval_bitcoin_deref_struct. unfold le. apply PTree.gss. }
           eapply eval_Econs; [exact Harg|reflexivity|apply eval_Enil].
        -- exact bitcoin_writeHash_funct.
        -- reflexivity.
        -- exact HCallH.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mh) (le1 := PTree.set _t'1 (Vlong ixv) le).
        -- apply exec_set.
           eapply eval_bitcoin_field_value with (sid := _outpoint) (delta := 32) (chunk := Mint64).
           ++ reflexivity.
           ++ exact bitcoin_outpoint_ix.
           ++ reflexivity.
           ++ apply eval_bitcoin_deref_struct. unfold le. apply PTree.gss.
           ++ rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HIxB].
        -- eapply exec_bitcoin_helper_call with (id := _simplicity_write32) (f := jets.f_simplicity_write32)
             (vargs := [Vptr bf (Ptrofs.repr base); Vlong ixv]) (vres := Vundef).
           ++ unfold bitcoin_core_helpers; simpl; tauto.
           ++ reflexivity.
           ++ eapply eval_Econs; [apply eval_Etempvar; unfold le; rewrite PTree.gso by discriminate;
                rewrite PTree.gso by discriminate; apply PTree.gss|reflexivity|].
              eapply eval_Econs; [apply eval_Etempvar; apply PTree.gss|reflexivity|apply eval_Enil].
           ++ reflexivity.
           ++ exact HCallW.
    + reflexivity.
    + reflexivity.
  - pose proof (write_effect_seq m mh mf bf base bw edge cursor 256 (wide_bits W32) (hash_cells xs)
      (encode (decode_wide W32 (Int64.zero_ext (wide_bits W32) ixv))) ltac:(apply hash_cells_length_Z; exact HL)
      ltac:(lia) ltac:(change (256 + wide_bits W32) with 288; exact HF) E1 E2) as Eseq.
    exact Eseq.
Qed.
