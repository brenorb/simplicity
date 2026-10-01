(** The actual peekBit/readBit bodies at arbitrary non-wrapping input cursors.
    This reader is shared by single-bit jets and carry-input arithmetic. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_constants.
Require Import C.jet_read8_layout C.jet_input_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Transparent Archi.ptr64.

Definition bit_int (b : bool) := if b then Int.one else Int.zero.
Definition bit_long (b : bool) := if b then Int64.one else Int64.zero.

Lemma peekBit_extract w shift : 0 <= shift < 64 ->
  Int64.and Int64.one (Int64.shru w (Int64.repr shift)) =
    bit_long (Int64.testbit w shift).
Proof.
  intros HS. apply Int64.same_bits_eq. intros j Hj.
  change (0 <= j < 64) in Hj.
  rewrite Int64.bits_and by exact Hj. rewrite Int64.bits_one.
  destruct (zeq j 0) as [HJ|HJ].
  - subst j. cbn [andb]. rewrite Int64.bits_shru by (change (0 <= 0 < 64); lia).
    rewrite Int64.unsigned_repr by (change (0 <= shift <= 18446744073709551615); lia).
    rewrite zlt_true by (change (0 + shift < 64); lia).
    replace (0 + shift) with shift by lia.
    unfold bit_long. destruct (Int64.testbit w shift); reflexivity.
  - cbn [andb]. unfold bit_long. destruct (Int64.testbit w shift).
    + rewrite Int64.bits_one. destruct (zeq j 0); [contradiction|reflexivity].
    + rewrite Int64.bits_zero. reflexivity.
Qed.

Definition bit_reader_env f bf base :=
  PTree.set _frame (Vptr bf (Ptrofs.repr base)) (create_undef_temps f.(fn_temps)).

Lemma bit_reader_entry f m bf base :
  f = f_peekBit \/ f = f_readBit ->
  function_entry2 ge0 f [Vptr bf (Ptrofs.repr base)] m empty_env (bit_reader_env f bf base) m.
Proof.
  intros [Hf|Hf]; subst f; constructor.
  all: try solve [constructor].
  all: try solve [constructor; [simpl; tauto|constructor]].
  all: try solve [reflexivity].
  all: intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
    vm_compute in *; congruence.
Qed.

Lemma eval_peekBit_layout m bf base bw edge cursor w :
  frame_base_valid base -> 0 <= cursor <= Int64.max_unsigned ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong w) ->
  Clight2.eval_funcall ge0 m (Internal f_peekBit) [Vptr bf (Ptrofs.repr base)] E0 m
    (Vint (bit_int (Int64.testbit w (63 - cursor mod 64)))).
Proof.
  intros HB HC HE [HF HO] HW.
  assert (HQ : 0 <= cursor / 64 <= Int64.max_unsigned).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia. }
  assert (HM : 0 <= cursor mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  assert (HIdiv : Int64.divu (Int64.repr cursor) (Int64.repr 64) = Int64.repr (cursor / 64)).
  { unfold Int64.divu. rewrite Int64.unsigned_repr by lia. reflexivity. }
  assert (HImod : Int64.modu (Int64.repr cursor) (Int64.repr 64) = Int64.repr (cursor mod 64)).
  { unfold Int64.modu. rewrite Int64.unsigned_repr by lia. reflexivity. }
  destruct (read8_layout_pointer edge (cursor / 64) HQ HE) as [HPfirst HPword].
  assert (HSub : Int64.sub (Int64.repr 64) (Int64.repr (cursor mod 64)) =
      Int64.repr (64 - cursor mod 64)).
  { unfold Int64.sub. rewrite (Int64.unsigned_repr (cursor mod 64)) by
      (change (0 <= cursor mod 64 <= 18446744073709551615); lia).
    reflexivity. }
  assert (HShift : Int64.sub (Int64.repr (64 - cursor mod 64)) Int64.one =
      Int64.repr (63 - cursor mod 64)).
  { unfold Int64.sub. rewrite (Int64.unsigned_repr (64 - cursor mod 64)) by
      (change (0 <= 64 - cursor mod 64 <= 18446744073709551615); lia).
    change (Int64.unsigned Int64.one) with 1. f_equal; lia. }
  assert (HValid : Int64.ltu (Int64.repr (63 - cursor mod 64)) Int64.iwordsize = true).
  { unfold Int64.ltu. rewrite Int64.unsigned_repr by (change (0 <= 63 - cursor mod 64 <= 18446744073709551615); lia).
    change (Int64.unsigned Int64.iwordsize) with 64. apply zlt_true; lia. }
  assert (HL : Mem.load Mint64 m bw
      (Ptrofs.unsigned (Ptrofs.repr (edge - 8 * (1 + cursor / 64)))) = Some (Vlong w)).
  { rewrite Ptrofs.unsigned_repr by lia. exact HW. }
  pose proof (peekBit_extract w (63 - cursor mod 64) ltac:(lia)) as HExtract.
  eapply eval_funcall_internal with (e := empty_env) (le1 := bit_reader_env f_peekBit bf base)
    (m1 := m) (m2 := m) (out := Out_return (Some
      (Vlong (bit_long (Int64.testbit w (63 - cursor mod 64))), tulong))).
  - apply bit_reader_entry. left; reflexivity.
  - unfold f_peekBit; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [apply exec_set; readlayout_expr|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [apply exec_set; readlayout_expr|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + apply exec_set. eapply eval_Elvalue.
      * eapply eval_Ederef. readlayout_expr.
      * apply deref_loc_value with (chunk := Mint64); [reflexivity|exact HL].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [apply exec_set; readlayout_expr|].
      apply exec_Sreturn_some.
      eapply eval_Ebinop with (v1 := Vint Int.one)
        (v2 := Vlong (Int64.shru w (Int64.repr (63 - cursor mod 64)))).
      * apply eval_Econst_int.
      * eapply eval_Ebinop with (v1 := Vlong w)
          (v2 := Vlong (Int64.repr (63 - cursor mod 64))).
        { eapply eval_Etempvar. reflexivity. }
        { eapply eval_Ebinop with (v1 := Vlong (Int64.repr (64 - cursor mod 64)))
            (v2 := Vint Int.one).
          - readlayout_expr.
          - apply eval_Econst_int.
          - change (Some (Vlong (Int64.sub (Int64.repr (64 - cursor mod 64)) Int64.one)) =
              Some (Vlong (Int64.repr (63 - cursor mod 64)))). rewrite HShift. reflexivity. }
        { change ((if Int64.ltu (Int64.repr (63 - cursor mod 64)) Int64.iwordsize
            then Some (Vlong (Int64.shru w (Int64.repr (63 - cursor mod 64)))) else None) =
            Some (Vlong (Int64.shru w (Int64.repr (63 - cursor mod 64))))).
          rewrite HValid. reflexivity. }
      * change (Some (Vlong (Int64.and Int64.one (Int64.shru w (Int64.repr (63 - cursor mod 64))))) =
          Some (Vlong (bit_long (Int64.testbit w (63 - cursor mod 64))))).
        rewrite HExtract. reflexivity.
  - cbn [fn_return]. split; [discriminate|].
    unfold bit_long, bit_int. destruct (Int64.testbit w (63 - cursor mod 64)); reflexivity.
  - reflexivity.
Qed.

Lemma symbol_peekBit : Genv.find_symbol (Clight.genv_genv ge0) _peekBit = Some (jet_symbol_block _peekBit).
Proof. vm_compute; reflexivity. Qed.
Lemma funct_peekBit : Genv.find_funct (Clight.genv_genv ge0) (Vptr (jet_symbol_block _peekBit) Ptrofs.zero) =
  Some (Internal f_peekBit).
Proof. vm_compute; reflexivity. Qed.
Lemma symbol_readBit : Genv.find_symbol (Clight.genv_genv ge0) _readBit = Some (jet_symbol_block _readBit).
Proof. vm_compute; reflexivity. Qed.
Lemma funct_readBit : Genv.find_funct (Clight.genv_genv ge0) (Vptr (jet_symbol_block _readBit) Ptrofs.zero) =
  Some (Internal f_readBit).
Proof. vm_compute; reflexivity. Qed.

Lemma call_peekBit_layout le m bf base bit :
  le!_frame = Some (Vptr bf (Ptrofs.repr base)) ->
  Clight2.eval_funcall ge0 m (Internal f_peekBit) [Vptr bf (Ptrofs.repr base)] E0 m (Vint (bit_int bit)) ->
  Clight2.exec_stmt ge0 empty_env le m
    (Scall (Some _t'1) (Evar _peekBit
      (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tbool cc_default))
      [Etempvar _frame (tptr (Tstruct _frameItem noattr))])
    E0 (PTree.set _t'1 (Vint (bit_int bit)) le) m Out_normal.
Proof.
  intros HP HC. eapply exec_Scall with
    (vf := Vptr (jet_symbol_block _peekBit) Ptrofs.zero)
    (vargs := [Vptr bf (Ptrofs.repr base)]) (f := Internal f_peekBit) (vres := Vint (bit_int bit)).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|apply symbol_peekBit].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [eapply eval_Etempvar; exact HP|reflexivity|apply eval_Enil].
  - apply funct_peekBit.
  - reflexivity.
  - exact HC.
Qed.

Lemma eval_readBit_layout_raw m mf bf base bw edge cursor w :
  frame_base_valid base -> 0 <= cursor <= Int64.max_unsigned - 1 ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong w) ->
  Mem.store Mint64 m bf (base + 8) (Vlong (Int64.repr (cursor + 1))) = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_readBit) [Vptr bf (Ptrofs.repr base)] E0 mf
    (Vint (bit_int (Int64.testbit w (63 - cursor mod 64)))).
Proof.
  intros HB HC HE HF HW SF.
  pose proof (eval_peekBit_layout m bf base bw edge cursor w HB ltac:(lia) HE HF HW) as Hpeek.
  destruct HF as [HF HO].
  assert (HAdd : Int64.add (Int64.repr cursor) Int64.one = Int64.repr (cursor + 1)).
  { unfold Int64.add. rewrite Int64.unsigned_repr by lia. reflexivity. }
  eapply eval_funcall_internal with (e := empty_env) (le1 := bit_reader_env f_readBit bf base)
    (m1 := m) (m2 := mf) (out := Out_return (Some
      (Vint (bit_int (Int64.testbit w (63 - cursor mod 64))), tbool))).
  - apply bit_reader_entry. right; reflexivity.
  - unfold f_readBit; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * eapply call_peekBit_layout; [reflexivity|exact Hpeek].
      * apply exec_set with (v := Vint (bit_int (Int64.testbit w (63 - cursor mod 64)))).
        eapply eval_Ecast with (v1 := Vint (bit_int (Int64.testbit w (63 - cursor mod 64)))).
        -- eapply eval_Etempvar; reflexivity.
        -- unfold bit_int. destruct (Int64.testbit w (63 - cursor mod 64)); reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply exec_set. eapply eval_frame_offset_at; [exact HB|reflexivity|exact HO].
        -- eapply exec_Sassign_value with (v := Vlong (Int64.repr (cursor + 1)))
             (v2 := Vlong (Int64.repr (cursor + 1))).
           ++ apply eval_frame_offset_lvalue_at; reflexivity.
           ++ eapply eval_Ebinop with (v1 := Vlong (Int64.repr cursor)) (v2 := Vint Int.one).
              ** eapply eval_Etempvar; reflexivity.
              ** apply eval_Econst_int.
              ** change (Some (Vlong (Int64.add (Int64.repr cursor) Int64.one)) =
                   Some (Vlong (Int64.repr (cursor + 1)))). rewrite HAdd. reflexivity.
           ++ reflexivity.
           ++ eapply assign_frame_offset_at; eauto.
      * apply exec_Sreturn_some. eapply eval_Etempvar; reflexivity.
  - cbn [fn_return]. split; [discriminate|].
    unfold bit_int. destruct (Int64.testbit w (63 - cursor mod 64)); reflexivity.
  - reflexivity.
Qed.

Theorem eval_readBit_layout m bf base bw edge cursor bit :
  frame_base_valid base -> 0 <= cursor <= Int64.max_unsigned - 1 ->
  frame_fields_at m bf base bw edge cursor -> frame_input_bit_at m bw edge cursor bit ->
  Mem.valid_access m Mint64 bf (base + 8) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_readBit) [Vptr bf (Ptrofs.repr base)] E0 mf (Vint (bit_int bit)) /\
    frame_fields_at mf bf base bw edge (cursor + 1) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HC [HF HO] [_ [HE [w [HW Hbit]]]] PW.
  destruct (Mem.valid_access_store m Mint64 bf (base + 8) (Vlong (Int64.repr (cursor + 1))) PW)
    as [mf SF].
  exists mf. split.
  - rewrite Hbit. eapply eval_readBit_layout_raw; eauto; split; assumption.
  - split.
    + split.
      * erewrite Mem.load_store_other; [exact HF|exact SF|].
        right; left; change (base + 8 <= base + 8); lia.
      * exact (Mem.load_store_same _ _ _ _ _ _ SF).
    + split.
      * intros chunk b ofs Hsep. eapply Mem.load_store_other; [exact SF|].
        change (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 8 + 8 <= ofs). lia.
      * split.
        -- intros b ofs kind p HP. eapply Mem.perm_store_1; eauto.
        -- intros b HV. eapply Mem.store_valid_block_1; eauto.
Qed.
