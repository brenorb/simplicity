(** The static Elements helper [asset], executed from initial memory: a tag
    bit (explicit or confidential), then padding or the parity bit, then the
    eight hash words of the confidential's data. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_uint32_array_init C.jet_application_sep.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval C.jet_elements_effects.
Require Import C.jet_output_layout_step C.jet_wide C.jet_wide_spec C.jet_elements_steps C.jet_elements_env_load C.jet_elements_write32s_layout C.jet_elements_hash_write C.jet_elements_call.
Require C.jets.
Require Import C.jet_elements_transport C.jet_elements_indexed_exec C.jet_elements_hash_helpers C.jet_elements_indexed_ptr.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.

Lemma elements_confidential_data : elements_field_at _confidential _data 0.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_confidential_prefix : elements_field_at _confidential _prefix 32.
Proof. vm_compute; reflexivity. Qed.

Lemma elements_asset_symbol :
  Genv.find_symbol (Clight.genv_genv elements_ge) _asset = Some (elements_symbol_block _asset).
Proof. vm_compute; reflexivity. Qed.
Lemma elements_asset_funct :
  Genv.find_funct (Clight.genv_genv elements_ge)
    (Vptr (elements_symbol_block _asset) Ptrofs.zero) = Some (Internal f_asset).
Proof. vm_compute; reflexivity. Qed.

Lemma elements_eq_cmp (k pfx : int) m :
  sem_binary_operation elements_ge Oeq (Vint k) tint (Vint pfx) tint m =
    Some (Val.of_bool (Int.eq k pfx)).
Proof. reflexivity. Qed.

Definition conf_bit_int (b : bool) : int := if b then Int.one else Int.zero.

(** The second cell: padding for an explicit value, the parity bit otherwise. *)
Definition asset_second_cell (pfx : int) : Cell :=
  if Int.eq (Int.repr 1) pfx then None else Some (Int.eq (Int.repr 3) pfx).

Definition asset_cells (pfx : int) (xs : list int) : list Cell :=
  [Some (Int.eq (Int.repr 1) pfx); asset_second_cell pfx] ++ hash_cells xs.

Lemma asset_cells_length_Z pfx xs : length xs = 8%nat -> Z.of_nat (length (asset_cells pfx xs)) = 258.
Proof.
  intros HL. unfold asset_cells. cbn [app length]. rewrite !Nat2Z.inj_succ, (hash_cells_length_Z xs HL). reflexivity.
Qed.

Definition asset_branch_stmt (aid tB tC : ident) : statement :=
  Sifthenelse (Etempvar tB tbool)
    (Scall None
      (Evar _skipBits (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
      ((Etempvar _dst (tptr (Tstruct _frameItem noattr))) :: (Econst_int (Int.repr 1) tint) :: nil))
    (Ssequence
      (Sset tC
        (Efield (Ederef (Etempvar aid (tptr (Tstruct _confidential noattr)))
          (Tstruct _confidential noattr)) _prefix tint))
      (Scall None
        (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
        ((Etempvar _dst (tptr (Tstruct _frameItem noattr))) ::
         (Ebinop Oeq (Econst_int (Int.repr 3) tint) (Etempvar tC tint) tint) :: nil))).

(** The body of [asset], also the present branch of [nonce], over the names
    of its compiler temporaries. *)
Definition conf_body_stmt (aid tA tB tC : ident) : statement :=
  Ssequence
    (Ssequence
      (Ssequence
        (Sset tA
          (Efield (Ederef (Etempvar aid (tptr (Tstruct _confidential noattr)))
            (Tstruct _confidential noattr)) _prefix tint))
        (Scall (Some tB)
          (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
          ((Etempvar _dst (tptr (Tstruct _frameItem noattr))) ::
           (Ebinop Oeq (Econst_int (Int.repr 1) tint) (Etempvar tA tint) tint) :: nil)))
      (asset_branch_stmt aid tB tC))
    (Scall None
      (Evar _writeHash (Tfunction (Tcons (tptr (Tstruct _frameItem noattr))
        (Tcons (tptr (Tstruct _sha256_midstate noattr)) Tnil)) tvoid cc_default))
      ((Etempvar _dst (tptr (Tstruct _frameItem noattr))) ::
       (Eaddrof (Efield (Ederef (Etempvar aid (tptr (Tstruct _confidential noattr)))
         (Tstruct _confidential noattr)) _data (Tstruct _sha256_midstate noattr))
         (tptr (Tstruct _sha256_midstate noattr))) :: nil)).

(** The explicit/parity branch: one cell at [cursor], given the tag bit in [tB]. *)
Lemma exec_elements_conf_branch e le m aid tB tC bf base bw edge cursor ba abase pfx :
  e!_skipBits = None -> e!_writeBit = None ->
  aid <> tC -> _dst <> tC ->
  le!_dst = Some (Vptr bf (Ptrofs.repr base)) ->
  le!aid = Some (Vptr ba (Ptrofs.repr abase)) ->
  le!tB = Some (Vint (conf_bit_int (Int.eq (Int.repr 1) pfx))) ->
  0 <= abase -> abase + 36 <= Ptrofs.max_unsigned ->
  Mem.load Mint32 m ba (abase + 32) = Some (Vint pfx) ->
  write_frame_at m bf base bw edge cursor 1 ->
  exists le' mf,
    Clight2.exec_stmt elements_ge e le m (asset_branch_stmt aid tB tC) E0 le' mf Out_normal /\
    write_effect m mf bf base bw edge cursor 1 [asset_second_cell pfx] /\
    le'!_dst = Some (Vptr bf (Ptrofs.repr base)) /\
    le'!aid = Some (Vptr ba (Ptrofs.repr abase)).
Proof.
  intros HeS HeW Ha2 Hd2 HD HA HT H0 HM HP HF.
  unfold asset_branch_stmt, asset_second_cell.
  destruct (Int.eq (Int.repr 1) pfx) eqn:Hb1.
  - destruct (elements_skipBits_step m bf base bw edge cursor 1%nat HF) as (mf & HCall & E).
    exists le, mf. split; [|split; [exact E|split; [exact HD|exact HA]]].
    eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
    + apply eval_Etempvar. exact HT.
    + reflexivity.
    + assert (Hargs : eval_exprlist elements_ge e le m
        [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 1) tint]
        (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
        [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr (Z.of_nat 1))]).
      { eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
        eapply eval_Econs; [apply eval_Econst_int| |apply eval_Enil].
        apply elements_cast_const'; lia. }
      exact (exec_elements_helper_call e le m None _skipBits jets.f_skipBits
        _ _ _ _ _ _ mf ltac:(unfold elements_core_helpers; simpl; tauto) HeS Hargs
        ltac:(reflexivity) HCall).
  - set (b3 := Int.eq (Int.repr 3) pfx).
    destruct (elements_writeBit_step m bf base bw edge cursor b3 HF) as (mf & HCall & E).
    set (le2 := PTree.set tC (Vint pfx) le).
    exists le2, mf. split; [|split; [exact E|split]].
    + eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
      * apply eval_Etempvar. exact HT.
      * reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le2).
        -- apply exec_set.
           eapply eval_elements_field_value with (sid := _confidential) (delta := 32) (chunk := Mint32).
           ++ reflexivity.
           ++ exact elements_confidential_prefix.
           ++ reflexivity.
           ++ apply eval_elements_deref_struct. exact HA.
           ++ rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HP].
        -- change le2 with (set_opttemp None (Vint (conf_bit_int b3)) le2) at 2.
           eapply exec_elements_helper_call with (id := _writeBit) (f := jets.f_writeBit)
             (vargs := [Vptr bf (Ptrofs.repr base); Vint (conf_bit_int b3)]) (vres := Vint (conf_bit_int b3)).
           ++ unfold elements_core_helpers. simpl. tauto.
           ++ exact HeW.
           ++ eapply eval_Econs.
              ** apply eval_Etempvar. unfold le2. rewrite PTree.gso by exact Hd2. exact HD.
              ** reflexivity.
              ** eapply eval_Econs with (v1 := Val.of_bool b3).
                 --- eapply eval_Ebinop with (v1 := Vint (Int.repr 3)) (v2 := Vint pfx).
                     +++ apply eval_Econst_int.
                     +++ apply eval_Etempvar. unfold le2. apply PTree.gss.
                     +++ apply elements_eq_cmp.
                 --- apply elements_bool_cast.
                 --- apply eval_Enil.
           ++ reflexivity.
           ++ exact HCall.
    + unfold le2. rewrite PTree.gso by exact Hd2. exact HD.
    + unfold le2. rewrite PTree.gso by exact Ha2. exact HA.
Qed.

Lemma exec_elements_conf_body e le m aid tA tB tC bf base bw edge cursor ba abase xs pfx :
  e!_skipBits = None -> e!_writeBit = None -> e!_writeHash = None ->
  aid <> tA -> aid <> tB -> aid <> tC -> _dst <> tA -> _dst <> tB -> _dst <> tC ->
  le!_dst = Some (Vptr bf (Ptrofs.repr base)) ->
  le!aid = Some (Vptr ba (Ptrofs.repr abase)) ->
  length xs = 8%nat -> 0 <= abase -> abase + 36 <= Ptrofs.max_unsigned ->
  out_sep bf base bw edge cursor 258 ba abase (abase + 36) ->
  uint32_array_at m ba abase xs -> Mem.load Mint32 m ba (abase + 32) = Some (Vint pfx) ->
  write_frame_at m bf base bw edge cursor 258 ->
  exists le' mf,
    Clight2.exec_stmt elements_ge e le m (conf_body_stmt aid tA tB tC) E0 le' mf Out_normal /\
    write_effect m mf bf base bw edge cursor 258 (asset_cells pfx xs).
Proof.
  intros HeS HeW HeH HaA HaB HaC HdA HdB HdC HD0 HA0 HL H0 HM HSep HA HP HF.
  pose proof HF as [_ [_ [_ [HCur _]]]].
  set (b1 := Int.eq (Int.repr 1) pfx).
  assert (HF1 : write_frame_at m bf base bw edge cursor 1).
  { eapply write_frame_at_shorter; [|exact HF]. lia. }
  destruct (elements_writeBit_step m bf base bw edge cursor b1 HF1) as (mb & HCallB & E1).
  assert (HFb : write_frame_at mb bf base bw edge (cursor - 1) 257).
  { eapply write_frame_at_after_effect with (cells := [Some b1]); [reflexivity|lia|exact HF|exact E1]. }
  assert (HFb1 : write_frame_at mb bf base bw edge (cursor - 1) 1).
  { eapply write_frame_at_shorter; [|exact HFb]. lia. }
  assert (HPb : Mem.load Mint32 mb ba (abase + 32) = Some (Vint pfx)).
  { rewrite <- HP. eapply write_effect_env_load with (bf := bf) (base := base) (bw := bw) (edge := edge)
      (cursor := cursor) (cursor0 := cursor) (count0 := 258) (n := 1) (cells := [Some b1])
      (lo := abase) (hi := abase + 36); [lia|lia|lia|lia|exact E1|exact HSep|lia|change (size_chunk Mint32) with 4; lia]. }
  set (le1 := PTree.set tA (Vint pfx) le).
  set (le2 := PTree.set tB (Vint (conf_bit_int b1)) le1).
  assert (HD2 : le2!_dst = Some (Vptr bf (Ptrofs.repr base))).
  { unfold le2, le1. rewrite PTree.gso by exact HdB. rewrite PTree.gso by exact HdA. exact HD0. }
  assert (HA2 : le2!aid = Some (Vptr ba (Ptrofs.repr abase))).
  { unfold le2, le1. rewrite PTree.gso by exact HaB. rewrite PTree.gso by exact HaA. exact HA0. }
  destruct (exec_elements_conf_branch e le2 mb aid tB tC bf base bw edge (cursor - 1) ba abase pfx
    HeS HeW HaC HdC HD2 HA2 ltac:(unfold le2; apply PTree.gss) H0 HM HPb HFb1)
    as (le3 & m2 & HBr & E2 & HD3 & HA3).
  pose proof (write_effect_seq m mb m2 bf base bw edge cursor 1 1 [Some b1] [asset_second_cell pfx]
    eq_refl ltac:(lia) ltac:(eapply write_frame_at_shorter; [|exact HF]; lia) E1 E2) as E12.
  change (1 + 1) with 2 in E12.
  assert (HF2 : write_frame_at m2 bf base bw edge (cursor - 2) 256).
  { eapply write_frame_at_after_effect with (cells := [Some b1] ++ [asset_second_cell pfx]) (m := m);
      [reflexivity|lia|exact HF|exact E12]. }
  assert (HLoad2 : forall chunk ofs, abase <= ofs -> ofs + size_chunk chunk <= abase + 36 ->
    Mem.load chunk m2 ba ofs = Mem.load chunk m ba ofs).
  { intros chunk ofs Hlo Hhi.
    eapply write_effect_env_load with (bf := bf) (base := base) (bw := bw) (edge := edge)
      (cursor := cursor) (cursor0 := cursor) (count0 := 258) (n := 2)
      (cells := [Some b1] ++ [asset_second_cell pfx]) (lo := abase) (hi := abase + 36);
      [lia|lia|lia|lia|exact E12|exact HSep|exact Hlo|exact Hhi]. }
  assert (HA2' : uint32_array_at m2 ba abase xs).
  { intros i w Hi.
    assert (Hi8 : (i < 8)%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hi; discriminate).
    rewrite HLoad2 by (try change (size_chunk Mint32) with 4; lia). exact (HA i w Hi). }
  assert (HSepH : out_sep bf base bw edge (cursor - 2) 256 ba abase (abase + 32)).
  { eapply out_sep_range with (lo := abase) (hi := abase + 36); [|lia|lia].
    eapply out_sep_sub with (cursor := cursor) (count := 258); [lia|lia|lia|lia|exact HSep]. }
  destruct (eval_elements_writeHash_layout m2 ba abase bf base bw edge (cursor - 2) xs HL H0 ltac:(lia)
    HSepH HA2' HF2) as (mf & HCallH & E3).
  exists le3, mf. split.
  - unfold conf_body_stmt.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2) (le1 := le3).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le2); [|exact HBr].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le1).
      * apply exec_set.
        eapply eval_elements_field_value with (sid := _confidential) (delta := 32) (chunk := Mint32).
        -- reflexivity.
        -- exact elements_confidential_prefix.
        -- reflexivity.
        -- apply eval_elements_deref_struct. exact HA0.
        -- rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HP].
      * change le2 with (set_opttemp (Some tB) (Vint (conf_bit_int b1)) le1).
        eapply exec_elements_helper_call with (id := _writeBit) (f := jets.f_writeBit)
          (vargs := [Vptr bf (Ptrofs.repr base); Vint (conf_bit_int b1)]) (vres := Vint (conf_bit_int b1)).
        -- unfold elements_core_helpers. simpl. tauto.
        -- exact HeW.
        -- eapply eval_Econs.
           ++ apply eval_Etempvar. unfold le1. rewrite PTree.gso by exact HdA. exact HD0.
           ++ reflexivity.
           ++ eapply eval_Econs with (v1 := Val.of_bool b1).
              ** eapply eval_Ebinop with (v1 := Vint (Int.repr 1)) (v2 := Vint pfx).
                 --- apply eval_Econst_int.
                 --- apply eval_Etempvar. unfold le1. apply PTree.gss.
                 --- apply elements_eq_cmp.
              ** apply elements_bool_cast.
              ** apply eval_Enil.
        -- reflexivity.
        -- exact HCallB.
    + eapply exec_Scall with (vf := Vptr (elements_symbol_block _writeHash) Ptrofs.zero)
        (f := Internal f_writeHash)
        (vargs := [Vptr bf (Ptrofs.repr base); Vptr ba (Ptrofs.repr abase)]) (vres := Vundef).
      * reflexivity.
      * eapply eval_Elvalue; [apply eval_Evar_global; [exact HeH|exact elements_writeHash_symbol]|
          apply deref_loc_reference; reflexivity].
      * eapply eval_Econs; [apply eval_Etempvar; exact HD3|reflexivity|].
        assert (Harg : eval_expr elements_ge e le3 m2
          (Eaddrof (Efield (Ederef (Etempvar aid (tptr (Tstruct _confidential noattr)))
            (Tstruct _confidential noattr)) _data (Tstruct _sha256_midstate noattr))
            (tptr (Tstruct _sha256_midstate noattr)))
          (Vptr ba (Ptrofs.repr abase))).
        { eapply eval_Eaddrof.
          assert (Hr : Ptrofs.repr abase = Ptrofs.add (Ptrofs.repr abase) (Ptrofs.repr 0))
            by (rewrite Ptrofs.add_zero; reflexivity).
          rewrite Hr.
          eapply eval_elements_field_lvalue; [reflexivity|exact elements_confidential_data|].
          apply eval_elements_deref_struct. exact HA3. }
        eapply eval_Econs; [exact Harg|reflexivity|apply eval_Enil].
      * exact elements_writeHash_funct.
      * reflexivity.
      * exact HCallH.
  - exact (write_effect_seq m m2 mf bf base bw edge cursor 2 256 ([Some b1] ++ [asset_second_cell pfx])
      (hash_cells xs) eq_refl ltac:(lia) HF E12 E3).
Qed.

Theorem eval_elements_asset_layout m ba abase bf base bw edge cursor xs pfx :
  length xs = 8%nat -> 0 <= abase -> abase + 36 <= Ptrofs.max_unsigned ->
  out_sep bf base bw edge cursor 258 ba abase (abase + 36) ->
  uint32_array_at m ba abase xs -> Mem.load Mint32 m ba (abase + 32) = Some (Vint pfx) ->
  write_frame_at m bf base bw edge cursor 258 ->
  exists mf,
    Clight2.eval_funcall elements_ge m (Internal f_asset)
      [Vptr bf (Ptrofs.repr base); Vptr ba (Ptrofs.repr abase)] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor 258 (asset_cells pfx xs).
Proof.
  intros HL H0 HM HSep HA HP HF.
  set (le0 := PTree.set _asset__1 (Vptr ba (Ptrofs.repr abase))
    (PTree.set _dst (Vptr bf (Ptrofs.repr base)) (create_undef_temps (fn_temps f_asset)))).
  destruct (exec_elements_conf_body empty_env le0 m _asset__1 _t'3 _t'1 _t'2 bf base bw edge cursor ba abase xs pfx
    ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(unfold le0; rewrite PTree.gso by discriminate; apply PTree.gss)
    ltac:(unfold le0; apply PTree.gss) HL H0 HM HSep HA HP HF) as (le3 & mf & HEx & E).
  exists mf. split; [|exact E].
  eapply eval_funcall_internal with (e := empty_env)
    (le1 := le0) (le2 := le3) (m1 := m) (m2 := mf) (out := Out_normal).
  - constructor.
    + constructor.
    + change (list_norepet [_dst; _asset__1]). unfold _dst, _asset__1.
      repeat constructor; simpl; intuition discriminate.
    + intros i j HI HJ Hij. cbn in HI, HJ.
      repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
        first [contradiction | vm_compute in Hij; discriminate | congruence].
    + constructor.
    + reflexivity.
  - exact HEx.
  - reflexivity.
  - reflexivity.
Qed.

(** * nonce *)

Lemma elements_nonce_symbol :
  Genv.find_symbol (Clight.genv_genv elements_ge) _nonce = Some (elements_symbol_block _nonce).
Proof. vm_compute; reflexivity. Qed.
Lemma elements_nonce_funct :
  Genv.find_funct (Clight.genv_genv elements_ge)
    (Vptr (elements_symbol_block _nonce) Ptrofs.zero) = Some (Internal f_nonce).
Proof. vm_compute; reflexivity. Qed.

Lemma elements_ne_cmp (k pfx : int) m :
  sem_binary_operation elements_ge One (Vint k) tint (Vint pfx) tint m =
    Some (Val.of_bool (negb (Int.eq k pfx))).
Proof. reflexivity. Qed.

(** An absent nonce (prefix NONE = 0) is a zero tag bit and 258 padding cells. *)
Definition nonce_cells (pfx : int) (xs : list int) : list Cell :=
  if Int.eq (Int.repr 0) pfx then Some false :: repeat None 258
  else Some true :: asset_cells pfx xs.

Lemma nonce_cells_length_Z pfx xs : length xs = 8%nat -> Z.of_nat (length (nonce_cells pfx xs)) = 259.
Proof.
  intros HL. unfold nonce_cells. destruct (Int.eq (Int.repr 0) pfx).
  - reflexivity.
  - cbn [length]. rewrite Nat2Z.inj_succ, (asset_cells_length_Z pfx xs HL). reflexivity.
Qed.

Definition nonce_skip_stmt : statement :=
  Scall None
    (Evar _skipBits (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
    ((Etempvar _dst (tptr (Tstruct _frameItem noattr))) ::
     (Ebinop Oadd (Ebinop Oadd (Econst_int (Int.repr 1) tint) (Econst_int (Int.repr 1) tint) tint)
       (Econst_int (Int.repr 256) tint) tint) :: nil).

Theorem eval_elements_nonce_layout m ba abase bf base bw edge cursor xs pfx :
  length xs = 8%nat -> 0 <= abase -> abase + 36 <= Ptrofs.max_unsigned ->
  out_sep bf base bw edge cursor 259 ba abase (abase + 36) ->
  (Int.eq (Int.repr 0) pfx = false -> uint32_array_at m ba abase xs) ->
  Mem.load Mint32 m ba (abase + 32) = Some (Vint pfx) ->
  write_frame_at m bf base bw edge cursor 259 ->
  exists mf,
    Clight2.eval_funcall elements_ge m (Internal f_nonce)
      [Vptr bf (Ptrofs.repr base); Vptr ba (Ptrofs.repr abase)] E0 mf Vundef /\
    write_effect m mf bf base bw edge cursor 259 (nonce_cells pfx xs).
Proof.
  intros HL H0 HM HSep HA HP HF.
  pose proof HF as [_ [_ [_ [HCur _]]]].
  set (b0 := negb (Int.eq (Int.repr 0) pfx)).
  assert (HF1 : write_frame_at m bf base bw edge cursor 1).
  { eapply write_frame_at_shorter; [|exact HF]. lia. }
  destruct (elements_writeBit_step m bf base bw edge cursor b0 HF1) as (mb & HCallB & E1).
  assert (HFb : write_frame_at mb bf base bw edge (cursor - 1) 258).
  { eapply write_frame_at_after_effect with (cells := [Some b0]); [reflexivity|lia|exact HF|exact E1]. }
  assert (HLoadB : forall chunk ofs, abase <= ofs -> ofs + size_chunk chunk <= abase + 36 ->
    Mem.load chunk mb ba ofs = Mem.load chunk m ba ofs).
  { intros chunk ofs Hlo Hhi.
    eapply write_effect_env_load with (bf := bf) (base := base) (bw := bw) (edge := edge)
      (cursor := cursor) (cursor0 := cursor) (count0 := 259) (n := 1) (cells := [Some b0])
      (lo := abase) (hi := abase + 36); [lia|lia|lia|lia|exact E1|exact HSep|exact Hlo|exact Hhi]. }
  set (le0 := PTree.set _nonce__1 (Vptr ba (Ptrofs.repr abase))
    (PTree.set _dst (Vptr bf (Ptrofs.repr base)) (create_undef_temps (fn_temps f_nonce)))).
  set (le1 := PTree.set _t'5 (Vint pfx) le0).
  set (le2 := PTree.set _t'2 (Vint (conf_bit_int b0)) le1).
  assert (HD2 : le2!_dst = Some (Vptr bf (Ptrofs.repr base))).
  { unfold le2, le1, le0. repeat rewrite PTree.gso by discriminate. apply PTree.gss. }
  assert (HA2 : le2!_nonce__1 = Some (Vptr ba (Ptrofs.repr abase))).
  { unfold le2, le1, le0. repeat rewrite PTree.gso by discriminate. apply PTree.gss. }
  assert (HTail : exists le3 mf tail,
    Clight2.exec_stmt elements_ge empty_env le2 mb
      (if b0 then conf_body_stmt _nonce__1 _t'4 _t'1 _t'3 else nonce_skip_stmt) E0 le3 mf Out_normal /\
    write_effect mb mf bf base bw edge (cursor - 1) 258 tail /\
    nonce_cells pfx xs = [Some b0] ++ tail).
  { unfold b0, nonce_cells. destruct (Int.eq (Int.repr 0) pfx) eqn:Hz; cbn [negb].
    - destruct (elements_skipBits_step mb bf base bw edge (cursor - 1) 258%nat HFb) as (mf & HCallS & E2).
      exists le2, mf, (repeat None 258). split; [|split; [exact E2|reflexivity]].
      unfold nonce_skip_stmt.
      assert (Hargs : eval_exprlist elements_ge empty_env le2 mb
        [Etempvar _dst (tptr (Tstruct _frameItem noattr));
         Ebinop Oadd (Ebinop Oadd (Econst_int (Int.repr 1) tint) (Econst_int (Int.repr 1) tint) tint)
           (Econst_int (Int.repr 256) tint) tint]
        (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
        [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr (Z.of_nat 258))]).
      { eapply eval_Econs; [apply eval_Etempvar; exact HD2|reflexivity|].
        eapply eval_Econs with (v1 := Vint (Int.repr 258)); [| |apply eval_Enil].
        - eapply eval_Ebinop with (v1 := Vint (Int.repr 2)) (v2 := Vint (Int.repr 256)).
          + eapply eval_Ebinop with (v1 := Vint (Int.repr 1)) (v2 := Vint (Int.repr 1));
              [apply eval_Econst_int|apply eval_Econst_int|reflexivity].
          + apply eval_Econst_int.
          + reflexivity.
        - apply elements_cast_const'; lia. }
      exact (exec_elements_helper_call empty_env le2 mb None _skipBits jets.f_skipBits
        _ _ _ _ _ _ mf ltac:(unfold elements_core_helpers; simpl; tauto) ltac:(reflexivity) Hargs
        ltac:(reflexivity) HCallS).
    - assert (HAb : uint32_array_at mb ba abase xs).
      { intros i w Hi.
        assert (Hi8 : (i < 8)%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hi; discriminate).
        rewrite HLoadB by (try change (size_chunk Mint32) with 4; lia). exact (HA eq_refl i w Hi). }
      assert (HPb : Mem.load Mint32 mb ba (abase + 32) = Some (Vint pfx)).
      { rewrite HLoadB by (try change (size_chunk Mint32) with 4; lia). exact HP. }
      assert (HSepB : out_sep bf base bw edge (cursor - 1) 258 ba abase (abase + 36)).
      { eapply out_sep_sub with (cursor := cursor) (count := 259); [lia|lia|lia|lia|exact HSep]. }
      destruct (exec_elements_conf_body empty_env le2 mb _nonce__1 _t'4 _t'1 _t'3 bf base bw edge (cursor - 1)
        ba abase xs pfx ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
        HD2 HA2 HL H0 HM HSepB HAb HPb HFb) as (le3 & mf & HEx & E2).
      exists le3, mf, (asset_cells pfx xs). split; [exact HEx|split; [exact E2|reflexivity]]. }
  destruct HTail as (le3 & mf & tail & HT & E2 & HCells).
  exists mf. split.
  - eapply eval_funcall_internal with (e := empty_env)
      (le1 := le0) (le2 := le3) (m1 := m) (m2 := mf) (out := Out_normal).
    + constructor.
      * constructor.
      * change (list_norepet [_dst; _nonce__1]). unfold _dst, _nonce__1.
        repeat constructor; simpl; intuition discriminate.
      * intros i j HI HJ Hij. cbn in HI, HJ.
        repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
          first [contradiction | vm_compute in Hij; discriminate | congruence].
      * constructor.
      * reflexivity.
    + unfold f_nonce; cbn [fn_body].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le2).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le1).
        -- apply exec_set.
           eapply eval_elements_field_value with (sid := _confidential) (delta := 32) (chunk := Mint32).
           ++ reflexivity.
           ++ exact elements_confidential_prefix.
           ++ reflexivity.
           ++ apply eval_elements_deref_struct. unfold le0. apply PTree.gss.
           ++ rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HP].
        -- change le2 with (set_opttemp (Some _t'2) (Vint (conf_bit_int b0)) le1).
           eapply exec_elements_helper_call with (id := _writeBit) (f := jets.f_writeBit)
             (vargs := [Vptr bf (Ptrofs.repr base); Vint (conf_bit_int b0)]) (vres := Vint (conf_bit_int b0)).
           ++ unfold elements_core_helpers. simpl. tauto.
           ++ reflexivity.
           ++ eapply eval_Econs.
              ** apply eval_Etempvar. unfold le1, le0. repeat rewrite PTree.gso by discriminate. apply PTree.gss.
              ** reflexivity.
              ** eapply eval_Econs with (v1 := Val.of_bool b0).
                 --- eapply eval_Ebinop with (v1 := Vint (Int.repr 0)) (v2 := Vint pfx).
                     +++ apply eval_Econst_int.
                     +++ apply eval_Etempvar. unfold le1. apply PTree.gss.
                     +++ apply elements_ne_cmp.
                 --- apply elements_bool_cast.
                 --- apply eval_Enil.
           ++ reflexivity.
           ++ exact HCallB.
      * eapply exec_Sifthenelse with (v1 := Vint (conf_bit_int b0)) (b := b0).
        -- apply eval_Etempvar. unfold le2. apply PTree.gss.
        -- destruct b0; reflexivity.
        -- destruct b0; exact HT.
    + reflexivity.
    + reflexivity.
  - rewrite HCells.
    assert (HTl : Z.of_nat (length tail) = 258).
    { pose proof (nonce_cells_length_Z pfx xs HL) as Hn. rewrite HCells in Hn.
      cbn [app length] in Hn. lia. }
    exact (write_effect_seq m mb mf bf base bw edge cursor 1 258 [Some b0] tail eq_refl ltac:(lia) HF E1 E2).
Qed.
