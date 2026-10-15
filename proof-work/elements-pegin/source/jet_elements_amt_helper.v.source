(** The static Elements helper [amt], executed from initial memory: a tag bit,
    then padding and the explicit 64-bit value, or the parity bit and the
    eight hash words of the commitment. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_uint32_array_init C.jet_application_sep.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval C.jet_elements_effects.
Require Import C.jet_output_layout_step C.jet_wide C.jet_wide_spec C.jet_elements_steps C.jet_elements_env_load C.jet_elements_write32s_layout C.jet_elements_hash_write C.jet_elements_call.
Require C.jets.
Require Import C.jet_elements_transport C.jet_elements_indexed_exec C.jet_elements_hash_helpers C.jet_elements_indexed_ptr C.jet_elements_asset_helper.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.


Definition _anon_union : ident := 18727075383868559167%positive.

Definition elements_union_field_at (uid field : ident) (delta : Z) : Prop :=
  match (Clight.genv_cenv elements_ge)!uid with
  | Some co => union_field_offset (Clight.genv_cenv elements_ge) field (co_members co) = OK (delta, Full)
  | None => False
  end.

Lemma eval_elements_union_field_lvalue e le m a uid field delta ty b ofs :
  typeof a = Tunion uid noattr -> elements_union_field_at uid field delta ->
  eval_expr elements_ge e le m a (Vptr b ofs) ->
  eval_lvalue elements_ge e le m (Efield a field ty) b (Ptrofs.add ofs (Ptrofs.repr delta)) Full.
Proof.
  intros HT HF HA. unfold elements_union_field_at in HF.
  destruct ((Clight.genv_cenv elements_ge)!uid) as [co|] eqn:HCo; [|contradiction].
  eapply eval_Efield_union with (co := co) (delta := delta); eauto.
Qed.

Lemma elements_confAmount_union : elements_field_at _confAmount _anon_union 0.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_confAmount_prefix : elements_field_at _confAmount _prefix 32.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_confAmount_explicit : elements_union_field_at __4799 _explicit 0.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_confAmount_confidential : elements_union_field_at __4799 _confidential 0.
Proof. vm_compute; reflexivity. Qed.

Lemma elements_amt_symbol :
  Genv.find_symbol (Clight.genv_genv elements_ge) _amt = Some (elements_symbol_block _amt).
Proof. vm_compute; reflexivity. Qed.
Lemma elements_amt_funct :
  Genv.find_funct (Clight.genv_genv elements_ge)
    (Vptr (elements_symbol_block _amt) Ptrofs.zero) = Some (Internal f_amt).
Proof. vm_compute; reflexivity. Qed.

(** An explicit amount is a set tag bit, 193 padding cells and the 64-bit
    value; a confidential one is as for an asset. *)
Definition amt_cells (pfx : int) (xs : list int) (v : int64) : list Cell :=
  if Int.eq (Int.repr 1) pfx
  then [Some true] ++ (repeat None 193 ++ encode (decode_wide W64 (Int64.zero_ext (wide_bits W64) v)))
  else [Some false] ++ ([Some (Int.eq (Int.repr 3) pfx)] ++ hash_cells xs).

Lemma amt_cells_length_Z pfx xs v : length xs = 8%nat -> Z.of_nat (length (amt_cells pfx xs v)) = 258.
Proof.
  intros HL. unfold amt_cells. destruct (Int.eq (Int.repr 1) pfx).
  - rewrite !app_length, encode_length. reflexivity.
  - cbn [app length]. rewrite !Nat2Z.inj_succ, (hash_cells_length_Z xs HL). reflexivity.
Qed.

Lemma elements_union_ofs abase :
  Ptrofs.add (Ptrofs.add (Ptrofs.repr abase) (Ptrofs.repr 0)) (Ptrofs.repr 0) = Ptrofs.repr abase.
Proof. change (Ptrofs.repr 0) with Ptrofs.zero. rewrite !Ptrofs.add_zero. reflexivity. Qed.

Lemma eval_elements_amt_union e le m aid ba abase :
  le!aid = Some (Vptr ba (Ptrofs.repr abase)) ->
  eval_expr elements_ge e le m
    (Efield (Ederef (Etempvar aid (tptr (Tstruct _confAmount noattr))) (Tstruct _confAmount noattr))
      _anon_union (Tunion __4799 noattr))
    (Vptr ba (Ptrofs.add (Ptrofs.repr abase) (Ptrofs.repr 0))).
Proof.
  intros HA. eapply eval_Elvalue.
  - eapply eval_elements_field_lvalue; [reflexivity|exact elements_confAmount_union|].
    apply eval_elements_deref_struct. exact HA.
  - apply deref_loc_copy; reflexivity.
Qed.

Theorem eval_elements_amt_layout m ba abase bf base bw edge cursor xs v pfx :
  length xs = 8%nat -> 0 <= abase -> abase + 40 <= Ptrofs.max_unsigned ->
  out_sep bf base bw edge cursor 258 ba abase (abase + 40) ->
  (Int.eq (Int.repr 1) pfx = true -> Mem.load Mint64 m ba abase = Some (Vlong v)) ->
  (Int.eq (Int.repr 1) pfx = false -> uint32_array_at m ba abase xs) ->
  Mem.load Mint32 m ba (abase + 32) = Some (Vint pfx) ->
  write_frame_at m bf base bw edge cursor 258 ->
  exists mf,
    Clight2.eval_funcall elements_ge m (Internal f_amt)
      [Vptr bf (Ptrofs.repr base); Vptr ba (Ptrofs.repr abase)] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor 258 (amt_cells pfx xs v).
Proof.
  intros HL H0 HM HSep HV HA HP HF.
  pose proof HF as [_ [_ [_ [HCur _]]]].
  set (b1 := Int.eq (Int.repr 1) pfx) in *.
  assert (HF1 : write_frame_at m bf base bw edge cursor 1).
  { eapply write_frame_at_shorter; [|exact HF]. lia. }
  destruct (elements_writeBit_step m bf base bw edge cursor b1 HF1) as (mb & HCallB & E1).
  assert (HFb : write_frame_at mb bf base bw edge (cursor - 1) 257).
  { eapply write_frame_at_after_effect with (cells := [Some b1]); [reflexivity|lia|exact HF|exact E1]. }
  assert (HLoadB : forall chunk ofs, abase <= ofs -> ofs + size_chunk chunk <= abase + 40 ->
    Mem.load chunk mb ba ofs = Mem.load chunk m ba ofs).
  { intros chunk ofs Hlo Hhi.
    eapply write_effect_env_load with (bf := bf) (base := base) (bw := bw) (edge := edge)
      (cursor := cursor) (cursor0 := cursor) (count0 := 258) (n := 1) (cells := [Some b1])
      (lo := abase) (hi := abase + 40); [lia|lia|lia|lia|exact E1|exact HSep|exact Hlo|exact Hhi]. }
  assert (HSepB : out_sep bf base bw edge (cursor - 1) 257 ba abase (abase + 40)).
  { eapply out_sep_sub with (cursor := cursor) (count := 258); [lia|lia|lia|lia|exact HSep]. }
  set (le0 := PTree.set _amt__1 (Vptr ba (Ptrofs.repr abase))
    (PTree.set _dst (Vptr bf (Ptrofs.repr base)) (create_undef_temps (fn_temps f_amt)))).
  set (le1 := PTree.set _t'4 (Vint pfx) le0).
  set (le2 := PTree.set _t'1 (Vint (conf_bit_int b1)) le1).
  assert (HD2 : le2!_dst = Some (Vptr bf (Ptrofs.repr base))).
  { unfold le2, le1, le0. repeat rewrite PTree.gso by discriminate. apply PTree.gss. }
  assert (HA2 : le2!_amt__1 = Some (Vptr ba (Ptrofs.repr abase))).
  { unfold le2, le1, le0. repeat rewrite PTree.gso by discriminate. apply PTree.gss. }
  assert (HTail : exists le3 mf tail,
    Clight2.exec_stmt elements_ge empty_env le2 mb
      (match fn_body f_amt with Ssequence _ (Sifthenelse _ s1 s2) => if b1 then s1 else s2 | _ => Sskip end)
      E0 le3 mf Out_normal /\
    write_effect mb mf bf base bw edge (cursor - 1) 257 tail /\
    amt_cells pfx xs v = [Some b1] ++ tail).
  { unfold f_amt; cbn [fn_body]. unfold amt_cells. fold b1. destruct b1 eqn:Hb1.
    - (* explicit *)
      assert (HFs : write_frame_at mb bf base bw edge (cursor - 1) (Z.of_nat 193)).
      { eapply write_frame_at_shorter; [|exact HFb]. lia. }
      destruct (elements_skipBits_step mb bf base bw edge (cursor - 1) 193%nat HFs) as (ms & HCallS & E2).
      assert (HFw : write_frame_at ms bf base bw edge (cursor - 1 - 193) (wide_bits W64)).
      { eapply write_frame_at_after_effect with (cells := repeat None 193) (m := mb);
          [reflexivity|change (wide_bits W64) with 64; lia|exact HFb|exact E2]. }
      assert (HVs : Mem.load Mint64 ms ba abase = Some (Vlong v)).
      { rewrite <- (HV eq_refl), <- (HLoadB Mint64 abase ltac:(lia) ltac:(change (size_chunk Mint64) with 8; lia)).
        eapply write_effect_env_load with (bf := bf) (base := base) (bw := bw) (edge := edge)
          (cursor := cursor - 1) (cursor0 := cursor - 1) (count0 := 257) (n := 193) (cells := repeat None 193)
          (lo := abase) (hi := abase + 40);
          [lia|lia|lia|lia|exact E2|exact HSepB|lia|change (size_chunk Mint64) with 8; lia]. }
      destruct (elements_write_wide_step W64 ms bf base bw edge (cursor - 1 - 193) v HFw) as (mf & HCallW & E3).
      set (le3 := PTree.set _t'3 (Vlong v) le2).
      exists le3, mf, (repeat None 193 ++ encode (decode_wide W64 (Int64.zero_ext (wide_bits W64) v))).
      split; [|split; [|reflexivity]].
      + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ms) (le1 := le2).
        * assert (Hargs : eval_exprlist elements_ge empty_env le2 mb
            [Etempvar _dst (tptr (Tstruct _frameItem noattr));
             Ebinop Osub (Ebinop Oadd (Econst_int (Int.repr 1) tint) (Econst_int (Int.repr 256) tint) tint)
               (Econst_int (Int.repr 64) tint) tint]
            (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
            [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr (Z.of_nat 193))]).
          { eapply eval_Econs; [apply eval_Etempvar; exact HD2|reflexivity|].
            eapply eval_Econs with (v1 := Vint (Int.repr 193)); [| |apply eval_Enil].
            - eapply eval_Ebinop with (v1 := Vint (Int.repr 257)) (v2 := Vint (Int.repr 64)).
              + eapply eval_Ebinop with (v1 := Vint (Int.repr 1)) (v2 := Vint (Int.repr 256));
                  [apply eval_Econst_int|apply eval_Econst_int|reflexivity].
              + apply eval_Econst_int.
              + reflexivity.
            - apply elements_cast_const'; lia. }
          exact (exec_elements_helper_call empty_env le2 mb None _skipBits jets.f_skipBits
            _ _ _ _ _ _ ms ltac:(unfold elements_core_helpers; simpl; tauto) ltac:(reflexivity) Hargs
            ltac:(reflexivity) HCallS).
        * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ms) (le1 := le3).
          -- apply exec_set. eapply eval_Elvalue.
             ++ eapply eval_elements_union_field_lvalue;
                  [reflexivity|exact elements_confAmount_explicit|].
                exact (eval_elements_amt_union empty_env le2 ms _amt__1 ba abase HA2).
             ++ eapply deref_loc_value; [reflexivity|].
                rewrite elements_union_ofs. apply elements_loadv_repr; [lia|exact HVs].
          -- eapply exec_elements_helper_call with (id := _simplicity_write64) (f := jets.f_simplicity_write64)
               (vargs := [Vptr bf (Ptrofs.repr base); Vlong v]) (vres := Vundef).
             ++ unfold elements_core_helpers; simpl; tauto.
             ++ reflexivity.
             ++ eapply eval_Econs; [apply eval_Etempvar; unfold le3; rewrite PTree.gso by discriminate;
                  exact HD2|reflexivity|].
                eapply eval_Econs; [apply eval_Etempvar; apply PTree.gss|reflexivity|apply eval_Enil].
             ++ reflexivity.
             ++ exact HCallW.
      + exact (write_effect_seq mb ms mf bf base bw edge (cursor - 1) 193 (wide_bits W64) (repeat None 193)
          (encode (decode_wide W64 (Int64.zero_ext (wide_bits W64) v))) eq_refl
          ltac:(change (wide_bits W64) with 64; lia) HFb E2 E3).
    - (* confidential *)
      set (b3 := Int.eq (Int.repr 3) pfx).
      assert (HFb1 : write_frame_at mb bf base bw edge (cursor - 1) 1).
      { eapply write_frame_at_shorter; [|exact HFb]. lia. }
      destruct (elements_writeBit_step mb bf base bw edge (cursor - 1) b3 HFb1) as (m2 & HCall2 & E2).
      assert (HF2 : write_frame_at m2 bf base bw edge (cursor - 1 - 1) 256).
      { eapply write_frame_at_after_effect with (cells := [Some b3]) (m := mb);
          [reflexivity|lia|exact HFb|exact E2]. }
      assert (HLoad2 : forall chunk ofs, abase <= ofs -> ofs + size_chunk chunk <= abase + 40 ->
        Mem.load chunk m2 ba ofs = Mem.load chunk m ba ofs).
      { intros chunk ofs Hlo Hhi. rewrite <- (HLoadB chunk ofs Hlo Hhi).
        eapply write_effect_env_load with (bf := bf) (base := base) (bw := bw) (edge := edge)
          (cursor := cursor - 1) (cursor0 := cursor - 1) (count0 := 257) (n := 1) (cells := [Some b3])
          (lo := abase) (hi := abase + 40); [lia|lia|lia|lia|exact E2|exact HSepB|exact Hlo|exact Hhi]. }
      assert (HA2' : uint32_array_at m2 ba abase xs).
      { intros i w Hi.
        assert (Hi8 : (i < 8)%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hi; discriminate).
        rewrite HLoad2 by (try change (size_chunk Mint32) with 4; lia). exact (HA eq_refl i w Hi). }
      assert (HPb : Mem.load Mint32 mb ba (abase + 32) = Some (Vint pfx)).
      { rewrite HLoadB by (try change (size_chunk Mint32) with 4; lia). exact HP. }
      assert (HSepH : out_sep bf base bw edge (cursor - 1 - 1) 256 ba abase (abase + 32)).
      { eapply out_sep_range with (lo := abase) (hi := abase + 40); [|lia|lia].
        eapply out_sep_sub with (cursor := cursor) (count := 258); [lia|lia|lia|lia|exact HSep]. }
      destruct (eval_elements_writeHash_layout m2 ba abase bf base bw edge (cursor - 1 - 1) xs HL H0 ltac:(lia)
        HSepH HA2' HF2) as (mf & HCallH & E3).
      set (le3 := PTree.set _t'2 (Vint pfx) le2).
      exists le3, mf, ([Some b3] ++ hash_cells xs). split; [|split; [|reflexivity]].
      + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2) (le1 := le3).
        * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le3).
          -- apply exec_set.
             eapply eval_elements_field_value with (sid := _confAmount) (delta := 32) (chunk := Mint32).
             ++ reflexivity.
             ++ exact elements_confAmount_prefix.
             ++ reflexivity.
             ++ apply eval_elements_deref_struct. exact HA2.
             ++ rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HPb].
          -- change le3 with (set_opttemp None (Vint (conf_bit_int b3)) le3) at 2.
             eapply exec_elements_helper_call with (id := _writeBit) (f := jets.f_writeBit)
               (vargs := [Vptr bf (Ptrofs.repr base); Vint (conf_bit_int b3)]) (vres := Vint (conf_bit_int b3)).
             ++ unfold elements_core_helpers. simpl. tauto.
             ++ reflexivity.
             ++ eapply eval_Econs.
                ** apply eval_Etempvar. unfold le3. rewrite PTree.gso by discriminate. exact HD2.
                ** reflexivity.
                ** eapply eval_Econs with (v1 := Val.of_bool b3).
                   --- eapply eval_Ebinop with (v1 := Vint (Int.repr 3)) (v2 := Vint pfx).
                       +++ apply eval_Econst_int.
                       +++ apply eval_Etempvar. unfold le3. apply PTree.gss.
                       +++ apply elements_eq_cmp.
                   --- apply elements_bool_cast.
                   --- apply eval_Enil.
             ++ reflexivity.
             ++ exact HCall2.
        * eapply exec_Scall with (vf := Vptr (elements_symbol_block _writeHash) Ptrofs.zero)
            (f := Internal f_writeHash)
            (vargs := [Vptr bf (Ptrofs.repr base); Vptr ba (Ptrofs.repr abase)]) (vres := Vundef).
          -- reflexivity.
          -- eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact elements_writeHash_symbol]|
               apply deref_loc_reference; reflexivity].
          -- eapply eval_Econs; [apply eval_Etempvar; unfold le3; rewrite PTree.gso by discriminate;
               exact HD2|reflexivity|].
             assert (Harg : eval_expr elements_ge empty_env le3 m2
               (Eaddrof (Efield (Efield (Ederef (Etempvar _amt__1 (tptr (Tstruct _confAmount noattr)))
                 (Tstruct _confAmount noattr)) _anon_union (Tunion __4799 noattr)) _confidential
                 (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr)))
               (Vptr ba (Ptrofs.repr abase))).
             { eapply eval_Eaddrof. rewrite <- (elements_union_ofs abase).
               eapply eval_elements_union_field_lvalue;
                 [reflexivity|exact elements_confAmount_confidential|].
               apply eval_elements_amt_union. unfold le3. rewrite PTree.gso by discriminate. exact HA2. }
             eapply eval_Econs; [exact Harg|reflexivity|apply eval_Enil].
          -- exact elements_writeHash_funct.
          -- reflexivity.
          -- exact HCallH.
      + exact (write_effect_seq mb m2 mf bf base bw edge (cursor - 1) 1 256 [Some b3] (hash_cells xs)
          eq_refl ltac:(lia) HFb E2 E3). }
  destruct HTail as (le3 & mf & tail & HT & E2 & HCells).
  exists mf. split.
  - eapply eval_funcall_internal with (e := empty_env)
      (le1 := le0) (le2 := le3) (m1 := m) (m2 := mf) (out := Out_normal).
    + constructor.
      * constructor.
      * change (list_norepet [_dst; _amt__1]). unfold _dst, _amt__1.
        repeat constructor; simpl; intuition discriminate.
      * intros i j HI HJ Hij. cbn in HI, HJ.
        repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
          first [contradiction | vm_compute in Hij; discriminate | congruence].
      * constructor.
      * reflexivity.
    + unfold f_amt in HT |- *; cbn [fn_body] in HT |- *.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le2).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le1).
        -- apply exec_set.
           eapply eval_elements_field_value with (sid := _confAmount) (delta := 32) (chunk := Mint32).
           ++ reflexivity.
           ++ exact elements_confAmount_prefix.
           ++ reflexivity.
           ++ apply eval_elements_deref_struct. unfold le0. apply PTree.gss.
           ++ rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HP].
        -- change le2 with (set_opttemp (Some _t'1) (Vint (conf_bit_int b1)) le1).
           eapply exec_elements_helper_call with (id := _writeBit) (f := jets.f_writeBit)
             (vargs := [Vptr bf (Ptrofs.repr base); Vint (conf_bit_int b1)]) (vres := Vint (conf_bit_int b1)).
           ++ unfold elements_core_helpers. simpl. tauto.
           ++ reflexivity.
           ++ eapply eval_Econs.
              ** apply eval_Etempvar. unfold le1, le0. repeat rewrite PTree.gso by discriminate. apply PTree.gss.
              ** reflexivity.
              ** eapply eval_Econs with (v1 := Val.of_bool b1).
                 --- eapply eval_Ebinop with (v1 := Vint (Int.repr 1)) (v2 := Vint pfx).
                     +++ apply eval_Econst_int.
                     +++ apply eval_Etempvar. unfold le1. apply PTree.gss.
                     +++ apply elements_eq_cmp.
                 --- apply elements_bool_cast.
                 --- apply eval_Enil.
           ++ reflexivity.
           ++ exact HCallB.
      * eapply exec_Sifthenelse with (v1 := Vint (conf_bit_int b1)) (b := b1).
        -- apply eval_Etempvar. unfold le2. apply PTree.gss.
        -- destruct b1; reflexivity.
        -- destruct b1; exact HT.
    + reflexivity.
    + reflexivity.
  - rewrite HCells.
    exact (write_effect_seq m mb mf bf base bw edge cursor 1 257 [Some b1] tail eq_refl ltac:(lia) HF E1 E2).
Qed.
