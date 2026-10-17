(** Execution of the actual selected-input branch of simplicity_issuance.
    Only the issuance enum is represented; cached hashes are not premises. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_elements_prim C.jet_elements_issuance_status_spec.
Require Import C.jet_application_sep C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_output_layout_step C.jet_encoding C.jet_exec.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval C.jet_elements_effects.
Require Import C.jet_elements_index_eval C.jet_elements_issuance_helper C.jet_elements_issuance_jets.
Require Import C.jet_elements_steps C.jet_elements_call C.jet_elements_transport C.jet_elements_indexed_exec C.jet_elements_env_load.
Require Import C.jet_elements_indexed_scalar C.jet_elements_indexed_ptr C.jet_elements_version_exec.
Require Import C.jet_elements_input_hash_jets.
Require C.jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 10.

Definition issuance_status_type_expr : expr :=
  Efield (Efield (Ederef (Etempvar _input (tptr (Tstruct _sigInput noattr)))
    (Tstruct _sigInput noattr)) _issuance (Tstruct _assetIssuance noattr)) _type tint.

Definition issuance_status_compare_stmt (temp : ident) (ret : option ident) (op : binary_operation) (k : int) : statement :=
  Ssequence (Sset temp issuance_status_type_expr)
    (Scall ret
      (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
      [Etempvar _dst (tptr (Tstruct _frameItem noattr));
       Ebinop op (Econst_int k tint) (Etempvar temp tint) tint]).

Definition issuance_status_payload_stmt : statement :=
  Ssequence (issuance_status_compare_stmt _t'5 (Some _t'2) One (Int.repr 0))
    (Sifthenelse (Etempvar _t'2 tbool)
      (issuance_status_compare_stmt _t'4 None Oeq (Int.repr 2)) (elements_skip_stmt 1)).

Definition issuance_status_setup_stmt : statement :=
  Ssequence
    (Sset _t'6 (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
      _tx (tptr (Tstruct _elementsTransaction noattr))))
    (Ssequence
      (Sset _t'7 (Efield (Ederef (Etempvar _t'6 (tptr (Tstruct _elementsTransaction noattr)))
        (Tstruct _elementsTransaction noattr)) _input (tptr (Tstruct _sigInput noattr))))
      (Sset _input (Ebinop Oadd (Etempvar _t'7 (tptr (Tstruct _sigInput noattr)))
        (Etempvar _i tulong) (tptr (Tstruct _sigInput noattr))))).

Definition issuance_status_then_stmt : statement :=
  Ssequence issuance_status_setup_stmt issuance_status_payload_stmt.

Definition issuance_status_enum_rep (m : mem) (b : block) (ofs : Z) (txi : sigTxInput) : Prop :=
  Mem.load Mint32 m b (ofs + 528) = Some (Vint (issuance_tag (sigTxiIssuance txi))).

Definition issuance_status_pcells (txi : sigTxInput) : list Cell :=
  @encode issuance_status_payload (issuance_status_of_input txi).

Lemma issuance_status_pcells_length txi : Z.of_nat (length (issuance_status_pcells txi)) = 2.
Proof.
  unfold issuance_status_pcells, issuance_status_of_input.
  destruct (sigTxiIssuance txi) as [[n | r] | ]; reflexivity.
Qed.



Lemma eval_issuance_status_type e le m bin ofs ty :
  le!_input = Some (Vptr bin (Ptrofs.repr ofs)) ->
  0 <= ofs -> ofs + 544 <= Ptrofs.max_unsigned ->
  Mem.load Mint32 m bin (ofs + 528) = Some (Vint ty) ->
  eval_expr elements_ge e le m issuance_status_type_expr (Vint ty).
Proof.
  intros HI H0 HM HL. unfold issuance_status_type_expr.
  eapply eval_elements_field_value with (sid := _assetIssuance) (delta := 272) (chunk := Mint32).
  - reflexivity.
  - exact elements_assetIssuance_type.
  - reflexivity.
  - eapply eval_elements_field_struct; [reflexivity|exact elements_sigInput_issuance|].
    apply eval_elements_deref_struct; exact HI.
  - rewrite !elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|].
    replace (ofs + 256 + 272) with (ofs + 528) by lia. exact HL.
Qed.

Lemma exec_issuance_status_compare e le m temp ret op k ty bit bin ofs bd dbase bw edge cur :
  temp <> _dst -> e!_writeBit = None ->
  le!_input = Some (Vptr bin (Ptrofs.repr ofs)) ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ofs -> ofs + 544 <= Ptrofs.max_unsigned ->
  Mem.load Mint32 m bin (ofs + 528) = Some (Vint ty) ->
  sem_binary_operation elements_ge op (Vint k) tint (Vint ty) tint m = Some (Val.of_bool bit) ->
  write_frame_at m bd dbase bw edge cur 1 ->
  exists mf,
    Clight2.exec_stmt elements_ge e le m (issuance_status_compare_stmt temp ret op k) E0
      (set_opttemp ret (Vint (if bit then Int.one else Int.zero)) (PTree.set temp (Vint ty) le)) mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 1 [Some bit].
Proof.
  intros Htemp Hwb HI HD H0 HM HL HC HF.
  destruct (elements_writeBit_step m bd dbase bw edge cur bit HF) as (mf & HCall & HE).
  exists mf. split; [|exact HE]. unfold issuance_status_compare_stmt.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := PTree.set temp (Vint ty) le).
  - apply exec_set. exact (eval_issuance_status_type e le m bin ofs ty HI H0 HM HL).
  - eapply exec_elements_helper_call with (id := _writeBit) (f := jets.f_writeBit)
      (vargs := [Vptr bd (Ptrofs.repr dbase); Vint (if bit then Int.one else Int.zero)])
      (vres := Vint (if bit then Int.one else Int.zero)).
    + unfold elements_core_helpers; simpl; tauto.
    + exact Hwb.
    + eapply eval_Econs.
      * apply eval_Etempvar. rewrite PTree.gso by (intro; congruence). exact HD.
      * reflexivity.
      * eapply eval_Econs.
        -- eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar, PTree.gss|exact HC].
        -- apply elements_bool_cast.
        -- apply eval_Enil.
    + reflexivity.
    + exact HCall.
Qed.

Lemma exec_issuance_status_payload bl le m txi bin ofs bd dbase bw edge cur :
  le!_input = Some (Vptr bin (Ptrofs.repr ofs)) ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ofs -> ofs + 544 <= Ptrofs.max_unsigned ->
  issuance_status_enum_rep m bin ofs txi ->
  out_sep bd dbase bw edge cur 2 bin ofs (ofs + 544) ->
  write_frame_at m bd dbase bw edge cur 2 ->
  exists le' mf,
    Clight2.exec_stmt elements_ge (elements_version_locals bl) le m issuance_status_payload_stmt
      E0 le' mf Out_normal /\ write_effect m mf bd dbase bw edge cur 2 (issuance_status_pcells txi).
Proof.
  intros HI HD H0 HM HT HS HF.
  set (has := opt_is_some (sigTxiIssuance txi)).
  set (tag := issuance_tag (sigTxiIssuance txi)).
  assert (HC : sem_binary_operation elements_ge One (Vint (Int.repr 0)) tint (Vint tag) tint m =
      Some (Val.of_bool has)).
  { unfold tag, has, issuance_tag, opt_is_some. destruct (sigTxiIssuance txi) as [[n | r] | ]; reflexivity. }
  assert (HF1 : write_frame_at m bd dbase bw edge cur 1) by
    (eapply write_frame_at_shorter with (count := 2); [lia|exact HF]).
  destruct (exec_issuance_status_compare (elements_version_locals bl) le m _t'5 (Some _t'2)
    One (Int.repr 0) tag has bin ofs bd dbase bw edge cur ltac:(discriminate) ltac:(reflexivity)
    HI HD H0 HM HT HC HF1) as (mb & HB & E1).
  set (le_after := PTree.set _t'2 (Vint (if has then Int.one else Int.zero)) (PTree.set _t'5 (Vint tag) le)).
  assert (HID : le_after!_input = Some (Vptr bin (Ptrofs.repr ofs))).
  { unfold le_after. repeat rewrite PTree.gso by discriminate. exact HI. }
  assert (HDD : le_after!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold le_after. repeat rewrite PTree.gso by discriminate. exact HD. }
  assert (HFb : write_frame_at mb bd dbase bw edge (cur - 1) 1).
  { eapply write_frame_at_after_effect with (cells := [Some has]); [reflexivity|lia|exact HF|exact E1]. }
  assert (Htb : Mem.load Mint32 mb bin (ofs + 528) = Some (Vint tag)).
  { erewrite write_effect_env_load with (m := m) (bf := bd) (base := dbase) (bw := bw)
      (edge := edge) (cursor := cur) (n := 1) (cells := [Some has])
      (cursor0 := cur) (count0 := 2) (lo := ofs) (hi := ofs + 544);
      [exact HT|lia|destruct HF as [_ [_ [_ [Hc _]]]]; lia|lia|lia|exact E1|exact HS|lia|
       change (size_chunk Mint32) with 4; lia]. }
  assert (HTail : exists le' mf,
    Clight2.exec_stmt elements_ge (elements_version_locals bl) le_after mb
      (if has then issuance_status_compare_stmt _t'4 None Oeq (Int.repr 2) else elements_skip_stmt 1)
      E0 le' mf Out_normal /\
    write_effect mb mf bd dbase bw edge (cur - 1) 1
      (match sigTxiIssuance txi with None => [None] | Some (inl _) => [Some false] | Some (inr _) => [Some true] end)).
  { unfold has, opt_is_some. destruct (sigTxiIssuance txi) as [[new | re] | ] eqn:HIss.
    - destruct (exec_issuance_status_compare (elements_version_locals bl) le_after mb _t'4 None Oeq
        (Int.repr 2) tag false bin ofs bd dbase bw edge (cur - 1) ltac:(discriminate)
        ltac:(reflexivity) HID HDD H0 HM Htb ltac:(unfold tag, issuance_tag; reflexivity) HFb)
        as (mf & HX & HE). eexists; exists mf; exact (conj HX HE).
    - destruct (exec_issuance_status_compare (elements_version_locals bl) le_after mb _t'4 None Oeq
        (Int.repr 2) tag true bin ofs bd dbase bw edge (cur - 1) ltac:(discriminate)
        ltac:(reflexivity) HID HDD H0 HM Htb ltac:(unfold tag, issuance_tag; reflexivity) HFb)
        as (mf & HX & HE). eexists; exists mf; exact (conj HX HE).
    - destruct (elements_skipBits_step mb bd dbase bw edge (cur - 1) 1 HFb) as (mf & HX & HE).
      exists le_after, mf. split; [|exact HE]. unfold elements_skip_stmt.
      eapply exec_elements_helper_call with (id := _skipBits) (f := jets.f_skipBits)
        (vargs := [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr 1)]) (vres := Vundef).
      + unfold elements_core_helpers; simpl; tauto.
      + reflexivity.
      + eapply eval_Econs; [apply eval_Etempvar; exact HDD|reflexivity|].
        eapply eval_Econs; [apply eval_Econst_int|apply elements_cast_const'; lia|apply eval_Enil].
      + reflexivity.
      + exact HX. }
  destruct HTail as (lef & mf & HX & E2).
  exists lef, mf. split.
  - unfold issuance_status_payload_stmt.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le_after); [exact HB|].
    eapply exec_Sifthenelse with (v1 := Vint (if has then Int.one else Int.zero)) (b := has).
    + apply eval_Etempvar. unfold le_after. apply PTree.gss.
    + destruct has; reflexivity.
    + destruct has; exact HX.
  - pose proof (write_effect_seq m mb mf bd dbase bw edge cur 1 1 [Some has] _ eq_refl ltac:(lia) HF E1 E2) as ES.
    assert (HEq : [Some has] ++
      (match sigTxiIssuance txi with None => [None] | Some (inl _) => [Some false] | Some (inr _) => [Some true] end)
      = issuance_status_pcells txi).
    { unfold has, issuance_status_pcells, issuance_status_of_input, opt_is_some.
      destruct (sigTxiIssuance txi) as [[n | r] | ]; reflexivity. }
    exact (eq_rect _ (fun cells => write_effect m mf bd dbase bw edge cur 2 cells) ES _ HEq).
Qed.

Lemma exec_issuance_status_then bl le m txi be ebase bt txbase bin inbase r bd dbase bw edge cur :
  le!_i = Some (Vlong r) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
  0 <= ebase -> ebase + 88 <= Ptrofs.max_unsigned ->
  0 <= txbase -> txbase + 760 <= Ptrofs.max_unsigned ->
  0 <= inbase -> inbase + 544 * Int64.unsigned r + 544 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr m bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  issuance_status_enum_rep m bin (inbase + 544 * Int64.unsigned r) txi ->
  out_sep bd dbase bw edge cur 2 bin (inbase + 544 * Int64.unsigned r)
    (inbase + 544 * Int64.unsigned r + 544) ->
  write_frame_at m bd dbase bw edge cur 2 ->
  exists le' mf,
    Clight2.exec_stmt elements_ge (elements_version_locals bl) le m issuance_status_then_stmt
      E0 le' mf Out_normal /\ write_effect m mf bd dbase bw edge cur 2 (issuance_status_pcells txi).
Proof.
  intros HI HD HE He0 He1 Ht0 Ht1 Hi0 Hi1 HLtx HLin HT HS HF.
  set (ofs := inbase + 544 * Int64.unsigned r).
  assert (Hr0 : 0 <= Int64.unsigned r) by apply Int64.unsigned_range.
  assert (Hofs : 0 <= ofs) by (unfold ofs; lia).
  set (la := PTree.set _t'6 (Vptr bt (Ptrofs.repr txbase)) le).
  set (lb := PTree.set _t'7 (Vptr bin (Ptrofs.repr inbase)) la).
  set (lc := PTree.set _input (Vptr bin (Ptrofs.repr ofs)) lb).
  assert (Hsetup : Clight2.exec_stmt elements_ge (elements_version_locals bl) le m
    issuance_status_setup_stmt E0 lc m Out_normal).
  { unfold issuance_status_setup_stmt.
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
          rewrite elements_ptr_index_repr by lia. reflexivity. }
  assert (HID : lc!_input = Some (Vptr bin (Ptrofs.repr ofs))) by (unfold lc; apply PTree.gss).
  assert (HDD : lc!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold lc, lb, la. repeat rewrite PTree.gso by discriminate. exact HD. }
  destruct (exec_issuance_status_payload bl lc m txi bin ofs bd dbase bw edge cur HID HDD Hofs Hi1 HT HS HF)
    as (lef & mf & HX & E).
  exists lef, mf. split; [|exact E]. unfold issuance_status_then_stmt.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := lc); [exact Hsetup|exact HX].
Qed.
