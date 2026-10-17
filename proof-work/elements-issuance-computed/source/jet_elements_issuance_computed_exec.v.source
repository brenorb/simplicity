(** Original inline issuance entropy/asset/token getters. The initial relation
    states the logical cached value; it does not assume execution or output.
    Establishing it from the real Elements builder remains a separate task. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option C.jet_elements_prim.
Require Import C.jet_application_sep C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_elements_issuance_status_exec C.jet_elements_issuance_jets.
Require Import C.jet_elements_hash_helpers C.jet_elements_hash_write C.jet_uint32_array_init.
Require Import C.jet_elements_effects C.jet_elements_env_load C.jet_output_layout_step.
Require Import C.jet_elements_steps C.jet_elements_call C.jet_elements_version_exec.
Require Import C.jet_elements_indexed_exec C.jet_elements_transport C.jet_encoding.
Require Import C.jet_elements_indexed_scalar.
Require Import C.jet_elements_indexed_ptr C.jet_elements_indexed_ptr_jets.
Require Import C.jet_elements_input_hash_jets C.jet_elements_issuance_helper.
Require Import C.jet_elements_script_cmr_local.
Require Import C.jet_elements_field_eval C.jet_elements_index_eval C.jet_elements_linkage C.jets_elements C.jet_exec.
Require Import C.jet_elements_issuance_entropy_spec.
Require C.jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 10.

Definition computed_issuance_present (v : Ty.tySem (Ty.Sum Ty.Unit Word256)) : bool :=
  match v with inl _ => false | inr _ => true end.

Definition computed_issuance_hash_rep (delta : Z)
    (value : sigTxInput -> Ty.tySem (Ty.Sum Ty.Unit Word256))
    (m : mem) (b : block) (ofs : Z) (txi : sigTxInput) : Prop :=
  issuance_status_enum_rep m b ofs txi /\
  forall h, value txi = inr h ->
    uint32_array_at m b (ofs + 256 + delta) (hash256_reg (to_hash256 h)).

Definition computed_issuance_hash_addr (field : ident) : expr :=
  Eaddrof (Efield (Efield
    (Ederef (Etempvar _input (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr))
    _issuance (Tstruct _assetIssuance noattr)) field (Tstruct _sha256_midstate noattr))
    (tptr (Tstruct _sha256_midstate noattr)).

Definition computed_issuance_hash_stmt (field : ident) : statement :=
  Scall None
    (Evar _writeHash (Tfunction (Tcons (tptr (Tstruct _frameItem noattr))
      (Tcons (tptr (Tstruct _sha256_midstate noattr)) Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); computed_issuance_hash_addr field].

Definition computed_issuance_payload_stmt (field : ident) : statement :=
  Ssequence (issuance_status_compare_stmt _t'4 (Some _t'2) One (Int.repr 0))
    (Sifthenelse (Etempvar _t'2 tbool) (computed_issuance_hash_stmt field) (elements_skip_stmt 256)).

Lemma eval_computed_issuance_hash_addr field delta e le m bin ofs :
  elements_field_at _assetIssuance field delta -> 0 <= delta -> delta + 32 <= 280 ->
  le!_input = Some (Vptr bin (Ptrofs.repr ofs)) ->
  0 <= ofs -> ofs + 544 <= Ptrofs.max_unsigned ->
  eval_expr elements_ge e le m (computed_issuance_hash_addr field)
    (Vptr bin (Ptrofs.repr (ofs + 256 + delta))).
Proof.
  intros HField Hd0 Hd1 HI H0 HM. unfold computed_issuance_hash_addr.
  eapply eval_Eaddrof.
  replace (Ptrofs.repr (ofs + 256 + delta)) with
    (Ptrofs.add (Ptrofs.add (Ptrofs.repr ofs) (Ptrofs.repr 256)) (Ptrofs.repr delta))
    by (rewrite !elements_ptr_add_repr by lia; reflexivity).
  eapply eval_elements_field_lvalue; [reflexivity|exact HField|].
  eapply eval_elements_field_struct; [reflexivity|exact elements_sigInput_issuance|].
  apply eval_elements_deref_struct; exact HI.
Qed.

Definition computed_issuance_setup_stmt : statement :=
  Ssequence
    (Sset _t'5 (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
      _tx (tptr (Tstruct _elementsTransaction noattr))))
    (Ssequence
      (Sset _t'6 (Efield (Ederef (Etempvar _t'5 (tptr (Tstruct _elementsTransaction noattr)))
        (Tstruct _elementsTransaction noattr)) _input (tptr (Tstruct _sigInput noattr))))
      (Sset _input (Ebinop Oadd (Etempvar _t'6 (tptr (Tstruct _sigInput noattr)))
        (Etempvar _i tulong) (tptr (Tstruct _sigInput noattr))))).

Definition computed_issuance_then_stmt field : statement :=
  Ssequence computed_issuance_setup_stmt (computed_issuance_payload_stmt field).

Lemma exec_computed_issuance_setup bl le m be ebase bt txbase bin inbase r :
  le!_i = Some (Vlong r) -> le!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
  0 <= ebase -> ebase + 88 <= Ptrofs.max_unsigned ->
  0 <= txbase -> txbase + 760 <= Ptrofs.max_unsigned ->
  0 <= inbase -> inbase + 544 * Int64.unsigned r + 544 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr m bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  let la := PTree.set _t'5 (Vptr bt (Ptrofs.repr txbase)) le in
  let lb := PTree.set _t'6 (Vptr bin (Ptrofs.repr inbase)) la in
  let lc := PTree.set _input (Vptr bin (Ptrofs.repr (inbase + 544 * Int64.unsigned r))) lb in
  Clight2.exec_stmt elements_ge (elements_version_locals bl) le m
    computed_issuance_setup_stmt E0 lc m Out_normal.
Proof.
  intros HI HE He0 He1 Ht0 Ht1 Hi0 Hi1 HLtx HLin la lb lc.
  pose proof (Int64.unsigned_range r) as Hr0.
  unfold computed_issuance_setup_stmt.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := la).
  - apply exec_set.
    eapply eval_elements_field_value with (sid := _txEnv) (delta := 0) (chunk := Mptr).
    + reflexivity.
    + exact elements_txEnv_tx.
    + reflexivity.
    + apply eval_elements_deref_struct; exact HE.
    + rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HLtx].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := lb).
    + apply exec_set.
      eapply eval_elements_field_value with (sid := _elementsTransaction) (delta := 0) (chunk := Mptr).
      * reflexivity.
      * exact elements_elementsTransaction_input.
      * reflexivity.
      * apply eval_elements_deref_struct. unfold la; apply PTree.gss.
      * rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HLin].
    + apply exec_set. eapply eval_Ebinop with (v1 := Vptr bin (Ptrofs.repr inbase)) (v2 := Vlong r).
      * apply eval_Etempvar. unfold lb; apply PTree.gss.
      * apply eval_Etempvar. unfold lb, la. repeat rewrite PTree.gso by discriminate. exact HI.
      * cbn [typeof]. unfold sem_binary_operation.
        rewrite (sem_add_ptr_long_sizeof (Clight.genv_cenv elements_ge) (Tstruct _sigInput noattr)
          r (Ptrofs.repr inbase) bin 544 m elements_sizeof_sigInput).
        replace r with (Int64.repr (Int64.unsigned r)) by apply Int64.repr_unsigned.
        rewrite elements_ptr_index_repr by lia.
        rewrite Int64.unsigned_repr by apply Int64.unsigned_range_2. reflexivity.
Qed.

Lemma exec_computed_issuance_payload field delta value
    (HP : forall x, computed_issuance_present (value x) = opt_is_some (sigTxiIssuance x))
    bl le m txi bin ofs bd dbase bw edge cur :
  elements_field_at _assetIssuance field delta -> 0 <= delta -> delta + 32 <= 280 ->
  le!_input = Some (Vptr bin (Ptrofs.repr ofs)) ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ofs -> ofs + 544 <= Ptrofs.max_unsigned ->
  computed_issuance_hash_rep delta value m bin ofs txi ->
  out_sep bd dbase bw edge cur 257 bin ofs (ofs + 544) ->
  write_frame_at m bd dbase bw edge cur 257 ->
  exists le' mf,
    Clight2.exec_stmt elements_ge (elements_version_locals bl) le m
      (computed_issuance_payload_stmt field) E0 le' mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 257 (@encode (Ty.Sum Ty.Unit Word256) (value txi)).
Proof.
  intros HField Hd0 Hd1 HI HD H0 HM [HT HA] HS HF.
  set (has := computed_issuance_present (value txi)).
  set (tag := issuance_tag (sigTxiIssuance txi)).
  assert (HC : sem_binary_operation elements_ge One (Vint (Int.repr 0)) tint (Vint tag) tint m =
      Some (Val.of_bool has)).
  { unfold has. rewrite HP. unfold tag, issuance_tag, opt_is_some.
    destruct (sigTxiIssuance txi) as [[new | re] | ]; reflexivity. }
  assert (HF1 : write_frame_at m bd dbase bw edge cur 1) by
    (eapply write_frame_at_shorter with (count := 257); [lia|exact HF]).
  destruct (exec_issuance_status_compare (elements_version_locals bl) le m _t'4 (Some _t'2)
    One (Int.repr 0) tag has bin ofs bd dbase bw edge cur ltac:(discriminate) ltac:(reflexivity)
    HI HD H0 HM HT HC HF1) as (mb & HB & E1).
  set (le_after := PTree.set _t'2 (Vint (if has then Int.one else Int.zero)) (PTree.set _t'4 (Vint tag) le)).
  assert (HID : le_after!_input = Some (Vptr bin (Ptrofs.repr ofs))).
  { unfold le_after. repeat rewrite PTree.gso by discriminate. exact HI. }
  assert (HDD : le_after!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold le_after. repeat rewrite PTree.gso by discriminate. exact HD. }
  assert (HFb : write_frame_at mb bd dbase bw edge (cur - 1) 256).
  { eapply write_frame_at_after_effect with (cells := [Some has]); [reflexivity|lia|exact HF|exact E1]. }
  assert (HLoad : forall chunk o, ofs <= o -> o + size_chunk chunk <= ofs + 544 ->
      Mem.load chunk mb bin o = Mem.load chunk m bin o).
  { intros chunk o Ho Hsz.
    eapply write_effect_env_load with (bf := bd) (base := dbase) (bw := bw)
      (edge := edge) (cursor := cur) (n := 1) (cells := [Some has])
      (cursor0 := cur) (count0 := 257) (lo := ofs) (hi := ofs + 544);
      [lia|destruct HF as [_ [_ [_ [Hc _]]]]; lia|lia|lia|exact E1|exact HS|exact Ho|exact Hsz]. }
  assert (HTail : exists mf,
    Clight2.exec_stmt elements_ge (elements_version_locals bl) le_after mb
      (if has then computed_issuance_hash_stmt field else elements_skip_stmt 256)
      E0 le_after mf Out_normal /\
    write_effect mb mf bd dbase bw edge (cur - 1) 256
      (match value txi with inl _ => repeat None 256 | inr h => @encode Word256 h end)).
  { unfold has. destruct (value txi) as [[] | h] eqn:HV.
    - destruct (elements_skipBits_step mb bd dbase bw edge (cur - 1) 256 HFb) as (mf & HX & HE).
      exists mf. split; [|exact HE]. unfold elements_skip_stmt.
      eapply exec_elements_helper_call with (id := _skipBits) (f := jets.f_skipBits)
        (vargs := [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr 256)]) (vres := Vundef).
      + unfold elements_core_helpers; simpl; tauto.
      + reflexivity.
      + eapply eval_Econs; [apply eval_Etempvar; exact HDD|reflexivity|].
        eapply eval_Econs; [apply eval_Econst_int|apply elements_cast_const'; lia|apply eval_Enil].
      + reflexivity.
      + exact HX.
    - assert (HAb : uint32_array_at mb bin (ofs + 256 + delta) (hash256_reg (to_hash256 h))).
      { eapply uint32_array_at_mono; [exact (hash256_len (to_hash256 h))|exact (HA h eq_refl)|].
        intros chunk o v Ho Hsz HL. rewrite HLoad by lia. exact HL. }
      assert (HSepH : out_sep bd dbase bw edge (cur - 1) 256 bin
          (ofs + 256 + delta) (ofs + 256 + delta + 32)).
      { eapply out_sep_range with (lo := ofs) (hi := ofs + 544); [|lia|lia].
        eapply out_sep_sub with (cursor := cur) (count := 257);
          [lia|destruct HF as [_ [_ [_ [Hc _]]]]; lia|lia|lia|exact HS]. }
      destruct (eval_elements_writeHash_layout mb bin (ofs + 256 + delta) bd dbase bw edge (cur - 1)
        (hash256_reg (to_hash256 h)) (hash256_len (to_hash256 h)) ltac:(lia) ltac:(lia) HSepH HAb HFb)
        as (mf & HX & HE).
      exists mf. split.
      + unfold computed_issuance_hash_stmt.
        change le_after with (set_opttemp None Vundef le_after) at 2.
        eapply exec_Scall with
          (vf := Vptr (elements_symbol_block _writeHash) Ptrofs.zero) (f := Internal f_writeHash)
          (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr (ofs + 256 + delta))]) (vres := Vundef).
        * reflexivity.
        * eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact elements_writeHash_symbol]|
            apply deref_loc_reference; reflexivity].
        * eapply eval_Econs; [apply eval_Etempvar; exact HDD|reflexivity|].
          eapply eval_Econs; [eapply eval_computed_issuance_hash_addr; eassumption|reflexivity|apply eval_Enil].
        * exact elements_writeHash_funct.
        * reflexivity.
        * exact HX.
      + rewrite <- (from_to_hash256 h), encode_from_hash256. exact HE. }
  destruct HTail as (mf & HX & E2).
  exists le_after, mf. split.
  - unfold computed_issuance_payload_stmt.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le_after); [exact HB|].
    eapply exec_Sifthenelse with (v1 := Vint (if has then Int.one else Int.zero)) (b := has).
    + apply eval_Etempvar. unfold le_after. apply PTree.gss.
    + destruct has; reflexivity.
    + destruct has; exact HX.
  - pose proof (write_effect_seq m mb mf bd dbase bw edge cur 1 256 [Some has] _ eq_refl ltac:(lia) HF E1 E2) as ES.
    assert (HEq : [Some has] ++
      (match value txi with inl _ => repeat None 256 | inr h => @encode Word256 h end) =
      @encode (Ty.Sum Ty.Unit Word256) (value txi)).
    { unfold has. destruct (value txi) as [[] | h]; reflexivity. }
    exact (eq_rect _ (fun cells => write_effect m mf bd dbase bw edge cur 257 cells) ES _ HEq).
Qed.
