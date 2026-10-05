(** The context reader [simplicity_read_sha256_context] in the SHA
    translation unit.  The function reads the constant global
    [sha256_max_counter], so it is outside the scope of [jet_transport.v];
    its callees are transported and its own (identical) body is executed
    again in the SHA global environment.  The lemmas below are the
    statements of [jet_sha256_context_fields.v], [jet_sha256_read_local.v],
    [jet_read_sha256_counter.v], [jet_read_sha256_overflow.v] and
    [jet_read_sha256_context_exec.v] for that environment. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_wide C.jet_sha256_context_fields C.jet_sha256_read_local.
Require Import C.jet_read_sha256_counter C.jet_read_sha256_overflow C.jet_readBit_layout.
Require Import C.jet_read_sha256_context_exec.
Require Import C.jet_sha_linkage.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 60.

Lemma sg_read64_symbol : Genv.find_symbol (Clight.genv_genv sha_ge) _simplicity_read64 =
  Some (sha_symbol_block _simplicity_read64).
Proof. vm_compute; reflexivity. Qed.
Lemma sg_read64_funct : Genv.find_funct (Clight.genv_genv sha_ge)
  (Vptr (sha_symbol_block _simplicity_read64) Ptrofs.zero) = Some (Internal f_simplicity_read64).
Proof. vm_compute; reflexivity. Qed.
Lemma sg_max_counter_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_max_counter = Some (sha_symbol_block _sha256_max_counter).
Proof. vm_compute; reflexivity. Qed.
Lemma sg_read_context_symbol : Genv.find_symbol (Clight.genv_genv sha_ge) _simplicity_read_sha256_context =
  Some (sha_symbol_block _simplicity_read_sha256_context).
Proof. vm_compute; reflexivity. Qed.
Lemma sg_read_context_funct : Genv.find_funct (Clight.genv_genv sha_ge)
  (Vptr (sha_symbol_block _simplicity_read_sha256_context) Ptrofs.zero) =
    Some (Internal f_simplicity_read_sha256_context).
Proof. vm_compute; reflexivity. Qed.

Lemma sg_eval_sha256_context_field_lvalue k id e le m bc base :
  le!id = Some (Vptr bc (Ptrofs.repr base)) ->
  eval_lvalue sha_ge e le m (sha256_context_field_expr k id)
    bc (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr (sha256_context_offset k))) Full.
Proof.
  intros HP. eapply eval_Efield_struct.
  - eapply eval_Elvalue.
    + apply eval_Ederef. apply eval_Etempvar; exact HP.
    + apply deref_loc_copy; reflexivity.
  - reflexivity.
  - vm_compute; reflexivity.
  - destruct k; vm_compute; reflexivity.
Qed.

Lemma sg_eval_sha256_context_field k id e le m bc base chunk v :
  0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  access_mode (sha256_context_field_type k) = By_value chunk ->
  le!id = Some (Vptr bc (Ptrofs.repr base)) ->
  Mem.load chunk m bc (base + sha256_context_offset k) = Some v ->
  eval_expr sha_ge e le m (sha256_context_field_expr k id) v.
Proof.
  intros HB HM HK HP HL. eapply eval_Elvalue.
  - apply sg_eval_sha256_context_field_lvalue; exact HP.
  - apply deref_loc_value with (chunk := chunk); [exact HK|].
    unfold Mem.loadv. rewrite sha256_context_address by assumption; exact HL.
Qed.

Lemma sg_eval_sha256_context_block id e le m bc base :
  le!id = Some (Vptr bc (Ptrofs.repr base)) ->
  eval_expr sha_ge e le m (sha256_context_field_expr CtxBlock id)
    (Vptr bc (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 16))).
Proof.
  intros HP. eapply eval_Elvalue; [apply sg_eval_sha256_context_field_lvalue; exact HP|].
  apply deref_loc_reference; reflexivity.
Qed.

Lemma sg_sha256_read_local_entry m ma bl bc cbase bf base :
  Mem.alloc m 0 8 = (ma,bl) ->
  function_entry2 sha_ge f_simplicity_read_sha256_context
    [Vptr bc (Ptrofs.repr cbase); Vptr bf (Ptrofs.repr base)] m
    (sha256_read_env bl) (sha256_read_temps bc cbase bf base) ma.
Proof.
  intro HA. constructor.
  - change (list_norepet [_len]); repeat constructor; simpl; tauto.
  - change (list_norepet [_ctx; _src]); vm_compute.
    repeat (apply list_norepet_cons; [simpl; intuition discriminate|]); constructor.
  - change (list_disjoint [_ctx; _src] [_compressionCount; _t'1; _t'5; _t'4; _t'3; _t'2]).
    vm_compute; intuition congruence.
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 8 = (ma,bl)); exact HA.
    + constructor.
  - reflexivity.
Qed.

Lemma sg_sha256_read_local_blocks bl : blocks_of_env sha_ge (sha256_read_env bl) = [(bl,0,8)].
Proof. reflexivity. Qed.

Theorem sg_free_sha256_read_local m bl :
  Mem.range_perm m bl 0 8 Cur Freeable ->
  exists mf,
    Mem.free_list m (blocks_of_env sha_ge (sha256_read_env bl)) = Some mf /\
    (forall chunk b ofs, b <> bl -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, b <> bl -> Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    Mem.nextblock mf = Mem.nextblock m.
Proof.
  intro HP. destruct (Mem.range_perm_free m bl 0 8 HP) as [mf HF].
  exists mf. split.
  - rewrite sg_sha256_read_local_blocks. cbn [Mem.free_list]. rewrite HF; reflexivity.
  - split.
    + intros chunk b ofs HOther. eapply Mem.load_free; [exact HF|left; exact HOther].
    + split.
      * intros b ofs kind p HOther HPerm. eapply Mem.perm_free_1; [exact HF|left; exact HOther|exact HPerm].
      * exact (Mem.nextblock_free _ _ _ _ _ HF).
Qed.

Theorem sg_eval_sha256_read_context_from_body m ma mb bl bc cbase bf base le overflow :
  Mem.alloc m 0 8 = (ma,bl) ->
  Clight2.exec_stmt sha_ge (sha256_read_env bl) (sha256_read_temps bc cbase bf base)
    ma (fn_body f_simplicity_read_sha256_context) E0 le mb
    (Out_return (Some (Vint (bit_int (negb overflow)), tint))) ->
  Mem.range_perm mb bl 0 8 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_read_sha256_context)
      [Vptr bc (Ptrofs.repr cbase); Vptr bf (Ptrofs.repr base)] E0 mf
      (Vint (bit_int (negb overflow))) /\
    Mem.free_list mb (blocks_of_env sha_ge (sha256_read_env bl)) = Some mf /\
    (forall chunk b ofs, b <> bl -> Mem.load chunk mf b ofs = Mem.load chunk mb b ofs) /\
    (forall b ofs kind p, b <> bl -> Mem.perm mb b ofs kind p -> Mem.perm mf b ofs kind p) /\
    Mem.nextblock mf = Mem.nextblock mb.
Proof.
  intros HA HBody HFree.
  destruct (sg_free_sha256_read_local mb bl HFree) as (mf & HF & HLoads & HPerms & HNext).
  exists mf. split; [|auto].
  eapply eval_funcall_internal with (e := sha256_read_env bl)
    (le1 := sha256_read_temps bc cbase bf base) (le2 := le)
    (m1 := ma) (m2 := mb)
    (out := Out_return (Some (Vint (bit_int (negb overflow)), tint))).
  - apply sg_sha256_read_local_entry; exact HA.
  - exact HBody.
  - cbn; split; [discriminate|destruct overflow; reflexivity].
  - exact HF.
Qed.

Lemma sg_exec_sha256_read_counter_store e le m mf bc base count len :
  0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  le!_ctx = Some (Vptr bc (Ptrofs.repr base)) ->
  le!_compressionCount = Some (Vlong count) -> le!_t'5 = Some (Vlong len) ->
  Mem.store Mint64 m bc (base + 8) (Vlong (sha256_read_counter count len)) = Some mf ->
  Clight2.exec_stmt sha_ge e le m
    (Sassign (sha256_context_field_expr CtxCounter _ctx)
      (Ebinop Oadd
        (Ebinop Oshl (Ebinop Omul (Etempvar _compressionCount tulong)
          (Econst_int (Int.repr 1) tuint) tulong)
          (Econst_int (Int.repr 6) tint) tulong)
        (Etempvar _t'5 tulong) tulong)) E0 le mf Out_normal.
Proof.
  intros HB HM HC HCount HLen HS.
  eapply exec_Sassign_value with (v := Vlong (sha256_read_counter count len))
    (v2 := Vlong (sha256_read_counter count len))
    (b := bc) (ofs := Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 8)).
  - apply sg_eval_sha256_context_field_lvalue; exact HC.
  - eapply eval_Ebinop with
      (v1 := Vlong (Int64.shl (Int64.mul count (Int64.repr 1)) (Int64.repr 6))) (v2 := Vlong len).
    + eapply eval_Ebinop with (v1 := Vlong (Int64.mul count (Int64.repr 1))) (v2 := Vint (Int.repr 6)).
      * eapply eval_Ebinop with (v1 := Vlong count) (v2 := Vint (Int.repr 1));
          [apply eval_Etempvar; exact HCount|apply eval_Econst_int|reflexivity].
      * apply eval_Econst_int.
      * reflexivity.
    + apply eval_Etempvar; exact HLen.
    + reflexivity.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint64); [reflexivity|].
    unfold Mem.storev. change (Mem.store Mint64 m bc
      (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr (sha256_context_offset CtxCounter))))
      (Vlong (sha256_read_counter count len)) = Some mf).
    rewrite sha256_context_address by assumption; exact HS.
Qed.

Lemma sg_exec_sha256_read_overflow_store e le m mf bc base count :
  0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  le!_ctx = Some (Vptr bc (Ptrofs.repr base)) ->
  le!_compressionCount = Some (Vlong count) ->
  le!_t'3 = Some (Vlong (Int64.repr 2305843009213693952)) ->
  Mem.store Mint8unsigned m bc (base + 80) (Vint (bit_int (sha256_read_overflow count))) = Some mf ->
  Clight2.exec_stmt sha_ge e le m
    (Sassign (sha256_context_field_expr CtxOverflow _ctx)
      (Ebinop Ole (Ebinop Oshr (Etempvar _t'3 tulong)
        (Econst_int (Int.repr 6) tint) tulong)
        (Etempvar _compressionCount tulong) tint)) E0 le mf Out_normal.
Proof.
  intros HB HM HC HCount HT HS.
  eapply exec_Sassign_value with (v := Vint (bit_int (sha256_read_overflow count)))
    (v2 := Vint (bit_int (sha256_read_overflow count)))
    (b := bc) (ofs := Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 80)).
  - apply sg_eval_sha256_context_field_lvalue; exact HC.
  - eapply eval_Ebinop with (v1 := Vlong (Int64.repr 36028797018963968)) (v2 := Vlong count).
    + eapply eval_Ebinop with (v1 := Vlong (Int64.repr 2305843009213693952)) (v2 := Vint (Int.repr 6));
        [apply eval_Etempvar; exact HT|apply eval_Econst_int|reflexivity].
    + apply eval_Etempvar; exact HCount.
    + change (Some (Val.of_bool (sha256_read_overflow count)) =
        Some (Vint (bit_int (sha256_read_overflow count)))).
      destruct (sha256_read_overflow count); reflexivity.
  - destruct (sha256_read_overflow count); reflexivity.
  - apply assign_loc_value with (chunk := Mint8unsigned); [reflexivity|].
    unfold Mem.storev. change (Mem.store Mint8unsigned m bc
      (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr (sha256_context_offset CtxOverflow))))
      (Vint (bit_int (sha256_read_overflow count))) = Some mf).
    rewrite sha256_context_address by assumption; exact HS.
Qed.

Theorem sg_exec_sha256_read_overflow_from_observation e le m bc base count :
  0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  e!_sha256_max_counter = None ->
  Mem.load Mint64 m (sha_symbol_block _sha256_max_counter) 0 =
    Some (Vlong (Int64.repr 2305843009213693952)) ->
  bc <> sha_symbol_block _sha256_max_counter ->
  le!_ctx = Some (Vptr bc (Ptrofs.repr base)) ->
  le!_compressionCount = Some (Vlong count) ->
  Mem.valid_access m Mint8unsigned bc (base + 80) Writable ->
  exists mf lef,
    Clight2.exec_stmt sha_ge e le m sha256_read_overflow_stmt E0 lef mf
      (Out_return (Some (Vint (bit_int (negb (sha256_read_overflow count))), tint))) /\
    Mem.store Mint8unsigned m bc (base + 80) (Vint (bit_int (sha256_read_overflow count))) = Some mf /\
    Mem.load Mint8unsigned mf bc (base + 80) = Some (Vint (bit_int (sha256_read_overflow count))) /\
    Mem.load Mint64 mf (sha_symbol_block _sha256_max_counter) 0 =
      Some (Vlong (Int64.repr 2305843009213693952)).
Proof.
  intros HB HM HE HGlobal HOther HC HCount HW.
  destruct (Mem.valid_access_store m Mint8unsigned bc (base + 80)
    (Vint (bit_int (sha256_read_overflow count))) HW) as [mf HS].
  set (le1 := PTree.set _t'3 (Vlong (Int64.repr 2305843009213693952)) le).
  set (le2 := PTree.set _t'2 (Vint (bit_int (sha256_read_overflow count))) le1).
  assert (HL : Mem.load Mint8unsigned mf bc (base + 80) =
    Some (Vint (bit_int (sha256_read_overflow count)))).
  { rewrite (Mem.load_store_same _ _ _ _ _ _ HS).
    destruct (sha256_read_overflow count); reflexivity. }
  exists mf, le2. split.
  - unfold sha256_read_overflow_stmt.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mf).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
      * apply exec_set. eapply eval_Elvalue.
        -- apply eval_Evar_global; [exact HE|exact sg_max_counter_symbol].
        -- apply deref_loc_value with (chunk := Mint64); [reflexivity|exact HGlobal].
      * eapply sg_exec_sha256_read_overflow_store; [exact HB|exact HM|
          unfold le1; rewrite PTree.gso by discriminate; exact HC|
          unfold le1; rewrite PTree.gso by discriminate; exact HCount|
          unfold le1; apply PTree.gss|exact HS].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mf).
      * apply exec_set. eapply sg_eval_sha256_context_field with (chunk := Mint8unsigned);
          [exact HB|exact HM|reflexivity|
           unfold le1; rewrite PTree.gso by discriminate; exact HC|exact HL].
      * apply exec_Sreturn_some. eapply eval_Eunop;
          [apply eval_Etempvar; unfold le2; apply PTree.gss|].
        destruct (sha256_read_overflow count); reflexivity.
  - split; [exact HS|]. split; [exact HL|].
    erewrite Mem.load_store_other; [exact HGlobal|exact HS|left; congruence].
Qed.

Lemma sg_sha256_read_buffer_symbol : Genv.find_symbol (Clight.genv_genv sha_ge) _simplicity_read_buffer8 =
  Some (sha_symbol_block _simplicity_read_buffer8).
Proof. vm_compute; reflexivity. Qed.

Lemma sg_sha256_read_buffer_funct : Genv.find_funct (Clight.genv_genv sha_ge)
  (Vptr (sha_symbol_block _simplicity_read_buffer8) Ptrofs.zero) = Some (Internal f_simplicity_read_buffer8).
Proof. vm_compute; reflexivity. Qed.

Lemma sg_sha256_read_state_symbol : Genv.find_symbol (Clight.genv_genv sha_ge) _read32s =
  Some (sha_symbol_block _read32s).
Proof. vm_compute; reflexivity. Qed.

Lemma sg_sha256_read_state_funct : Genv.find_funct (Clight.genv_genv sha_ge)
  (Vptr (sha_symbol_block _read32s) Ptrofs.zero) = Some (Internal f_read32s).
Proof. vm_compute; reflexivity. Qed.

Lemma sg_call_sha256_read_buffer le m mb bl bc cbase bf base :
  le!_ctx = Some (Vptr bc (Ptrofs.repr cbase)) -> le!_src = Some (Vptr bf (Ptrofs.repr base)) ->
  Clight2.eval_funcall sha_ge m (Internal f_simplicity_read_buffer8)
    [Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16)); Vptr bl Ptrofs.zero;
     Vptr bf (Ptrofs.repr base); Vint (Int.repr 5)] E0 mb Vundef ->
  Clight2.exec_stmt sha_ge (sha256_read_env bl) le m sha256_read_buffer_call E0 le mb Out_normal.
Proof.
  intros HC HF HCall. eapply exec_Scall with
    (vf := Vptr (sha_symbol_block _simplicity_read_buffer8) Ptrofs.zero)
    (vargs := [Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16)); Vptr bl Ptrofs.zero;
      Vptr bf (Ptrofs.repr base); Vint (Int.repr 5)])
    (f := Internal f_simplicity_read_buffer8) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sg_sha256_read_buffer_symbol]|
      apply deref_loc_reference; reflexivity].
  - eapply eval_Econs; [apply sg_eval_sha256_context_block; exact HC|reflexivity|].
    eapply eval_Econs; [apply eval_Eaddrof, eval_Evar_local; reflexivity|reflexivity|].
    eapply eval_Econs; [apply eval_Etempvar; exact HF|reflexivity|].
    eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
  - exact sg_sha256_read_buffer_funct.
  - reflexivity.
  - exact HCall.
Qed.

Lemma sg_call_sha256_read_count le m mc bl bf base count :
  le!_src = Some (Vptr bf (Ptrofs.repr base)) ->
  Clight2.eval_funcall sha_ge m (Internal f_simplicity_read64)
    [Vptr bf (Ptrofs.repr base)] E0 mc (Vlong count) ->
  Clight2.exec_stmt sha_ge (sha256_read_env bl) le m sha256_read_count_stmt E0
    (PTree.set _compressionCount (Vlong count) (PTree.set _t'1 (Vlong count) le)) mc Out_normal.
Proof.
  intros HF HCall. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
    (le1 := PTree.set _t'1 (Vlong count) le) (m1 := mc).
  - eapply exec_Scall with (vf := Vptr (sha_symbol_block _simplicity_read64) Ptrofs.zero)
      (vargs := [Vptr bf (Ptrofs.repr base)]) (f := Internal f_simplicity_read64) (vres := Vlong count).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sg_read64_symbol]|
        apply deref_loc_reference; reflexivity].
    + eapply eval_Econs; [apply eval_Etempvar; exact HF|reflexivity|apply eval_Enil].
    + exact sg_read64_funct.
    + reflexivity.
    + exact HCall.
  - apply exec_set. apply eval_Etempvar, PTree.gss.
Qed.

Lemma sg_call_sha256_read_state le m me bl bc cbase bf base bi output :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  le!_ctx = Some (Vptr bc (Ptrofs.repr cbase)) -> le!_src = Some (Vptr bf (Ptrofs.repr base)) ->
  Mem.load Mptr m bc cbase = Some (Vptr bi (Ptrofs.repr output)) ->
  Clight2.eval_funcall sha_ge m (Internal f_read32s)
    [Vptr bi (Ptrofs.repr output); Vlong (Int64.repr 8); Vptr bf (Ptrofs.repr base)] E0 me Vundef ->
  Clight2.exec_stmt sha_ge (sha256_read_env bl) le m sha256_read_state_stmt E0
    (PTree.set _t'4 (Vptr bi (Ptrofs.repr output)) le) me Out_normal.
Proof.
  intros HB HM HC HF HL HCall.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
    (le1 := PTree.set _t'4 (Vptr bi (Ptrofs.repr output)) le) (m1 := m).
  - apply exec_set. eapply sg_eval_sha256_context_field with (k := CtxOutput) (id := _ctx) (chunk := Mptr);
      [exact HB|exact HM|reflexivity|exact HC|].
    change (Mem.load Mptr m bc (cbase + 0) = Some (Vptr bi (Ptrofs.repr output))).
    rewrite Z.add_0_r; exact HL.
  - eapply exec_Scall with (vf := Vptr (sha_symbol_block _read32s) Ptrofs.zero)
      (vargs := [Vptr bi (Ptrofs.repr output); Vlong (Int64.repr 8); Vptr bf (Ptrofs.repr base)])
      (f := Internal f_read32s) (vres := Vundef).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sg_sha256_read_state_symbol]|
        apply deref_loc_reference; reflexivity].
    + eapply eval_Econs; [apply eval_Etempvar, PTree.gss|reflexivity|].
      eapply eval_Econs; [apply eval_Econst_int|reflexivity|].
      eapply eval_Econs; [apply eval_Etempvar; rewrite PTree.gso by discriminate; exact HF|reflexivity|apply eval_Enil].
    + exact sg_sha256_read_state_funct.
    + reflexivity.
    + exact HCall.
Qed.

Theorem sg_exec_sha256_read_context_composes m mb mc md me bl bc cbase bf base bi output count len :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  Clight2.eval_funcall sha_ge m (Internal f_simplicity_read_buffer8)
    [Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16)); Vptr bl Ptrofs.zero;
      Vptr bf (Ptrofs.repr base); Vint (Int.repr 5)] E0 mb Vundef ->
  Clight2.eval_funcall sha_ge mb (Internal f_simplicity_read64) [Vptr bf (Ptrofs.repr base)] E0 mc (Vlong count) ->
  Mem.load Mint64 mc bl 0 = Some (Vlong len) ->
  Mem.store Mint64 mc bc (cbase + 8) (Vlong (sha256_read_counter count len)) = Some md ->
  Mem.load Mptr md bc cbase = Some (Vptr bi (Ptrofs.repr output)) ->
  Clight2.eval_funcall sha_ge md (Internal f_read32s)
    [Vptr bi (Ptrofs.repr output); Vlong (Int64.repr 8); Vptr bf (Ptrofs.repr base)] E0 me Vundef ->
  Mem.load Mint64 me (sha_symbol_block _sha256_max_counter) 0 = Some (Vlong (Int64.repr 2305843009213693952)) ->
  bc <> sha_symbol_block _sha256_max_counter ->
  Mem.valid_access me Mint8unsigned bc (cbase + 80) Writable ->
  exists mf lef,
    Clight2.exec_stmt sha_ge (sha256_read_env bl) (sha256_read_temps bc cbase bf base) m
      (fn_body f_simplicity_read_sha256_context) E0 lef mf
      (Out_return (Some (Vint (bit_int (negb (sha256_read_overflow count))), tint))) /\
    Mem.store Mint8unsigned me bc (cbase + 80) (Vint (bit_int (sha256_read_overflow count))) = Some mf.
Proof.
  intros HB HM HBuffer HCount HLen HCounter HOutput HState HGlobal HOther HW.
  set (le0 := sha256_read_temps bc cbase bf base).
  set (le1 := PTree.set _compressionCount (Vlong count) (PTree.set _t'1 (Vlong count) le0)).
  set (le2 := PTree.set _t'5 (Vlong len) le1).
  set (le3 := PTree.set _t'4 (Vptr bi (Ptrofs.repr output)) le2).
  assert (HC : le0!_ctx = Some (Vptr bc (Ptrofs.repr cbase))) by reflexivity.
  assert (HF : le0!_src = Some (Vptr bf (Ptrofs.repr base))) by reflexivity.
  assert (HC3 : le3!_ctx = Some (Vptr bc (Ptrofs.repr cbase))).
  { unfold le3, le2, le1. repeat rewrite PTree.gso by discriminate; exact HC. }
  assert (HCount3 : le3!_compressionCount = Some (Vlong count)).
  { unfold le3, le2, le1. repeat rewrite PTree.gso by discriminate; apply PTree.gss. }
  destruct (sg_exec_sha256_read_overflow_from_observation (sha256_read_env bl) le3 me bc cbase count
    HB HM eq_refl HGlobal HOther HC3 HCount3 HW) as (mf & lef & HOverflow & HS & HL & HG).
  exists mf, lef. split; [|exact HS]. rewrite sha256_read_body_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := mb).
  - eapply sg_call_sha256_read_buffer; eauto.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mc).
    + eapply sg_call_sha256_read_count; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := md).
      * unfold sha256_read_counter_stmt.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mc).
        -- apply exec_set. eapply eval_Elvalue;
             [apply eval_Evar_local; reflexivity|apply deref_loc_value with (chunk := Mint64); [reflexivity|exact HLen]].
        -- eapply sg_exec_sha256_read_counter_store; [exact HB|exact HM|
             unfold le2, le1; repeat rewrite PTree.gso by discriminate; exact HC|
             unfold le2, le1; repeat rewrite PTree.gso by discriminate; apply PTree.gss|
             unfold le2; apply PTree.gss|exact HCounter].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := me).
        -- eapply sg_call_sha256_read_state; [exact HB|exact HM|
             unfold le2, le1; repeat rewrite PTree.gso by discriminate; exact HC|
             unfold le2, le1; repeat rewrite PTree.gso by discriminate; exact HF|exact HOutput|exact HState].
        -- exact HOverflow.
Qed.

Theorem sg_eval_sha256_read_context_composes m ma mb mc md me bl bc cbase bf base bi output count len :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  Mem.alloc m 0 8 = (ma,bl) ->
  Clight2.eval_funcall sha_ge ma (Internal f_simplicity_read_buffer8)
    [Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16)); Vptr bl Ptrofs.zero;
      Vptr bf (Ptrofs.repr base); Vint (Int.repr 5)] E0 mb Vundef ->
  Clight2.eval_funcall sha_ge mb (Internal f_simplicity_read64) [Vptr bf (Ptrofs.repr base)] E0 mc (Vlong count) ->
  Mem.load Mint64 mc bl 0 = Some (Vlong len) ->
  Mem.store Mint64 mc bc (cbase + 8) (Vlong (sha256_read_counter count len)) = Some md ->
  Mem.load Mptr md bc cbase = Some (Vptr bi (Ptrofs.repr output)) ->
  Clight2.eval_funcall sha_ge md (Internal f_read32s)
    [Vptr bi (Ptrofs.repr output); Vlong (Int64.repr 8); Vptr bf (Ptrofs.repr base)] E0 me Vundef ->
  Mem.load Mint64 me (sha_symbol_block _sha256_max_counter) 0 = Some (Vlong (Int64.repr 2305843009213693952)) ->
  bc <> sha_symbol_block _sha256_max_counter ->
  Mem.valid_access me Mint8unsigned bc (cbase + 80) Writable ->
  Mem.range_perm me bl 0 8 Cur Freeable ->
  exists mx mf,
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_read_sha256_context)
      [Vptr bc (Ptrofs.repr cbase); Vptr bf (Ptrofs.repr base)] E0 mf
      (Vint (bit_int (negb (sha256_read_overflow count)))) /\
    Mem.store Mint8unsigned me bc (cbase + 80) (Vint (bit_int (sha256_read_overflow count))) = Some mx /\
    Mem.free_list mx (blocks_of_env sha_ge (sha256_read_env bl)) = Some mf /\
    (forall chunk b ofs, b <> bl -> Mem.load chunk mf b ofs = Mem.load chunk mx b ofs) /\
    (forall b ofs kind p, b <> bl -> Mem.perm mx b ofs kind p -> Mem.perm mf b ofs kind p) /\
    Mem.nextblock mf = Mem.nextblock mx.
Proof.
  intros HB HM HA HBuffer HCount HLen HCounter HOutput HState HGlobal HOther HW HFree.
  destruct (sg_exec_sha256_read_context_composes ma mb mc md me bl bc cbase bf base bi output count len
    HB HM HBuffer HCount HLen HCounter HOutput HState HGlobal HOther HW)
    as (mx & le & HBody & HS).
  assert (HFreeX : Mem.range_perm mx bl 0 8 Cur Freeable).
  { intros ofs HR. eapply Mem.perm_store_1; [exact HS|apply HFree; exact HR]. }
  destruct (sg_eval_sha256_read_context_from_body m ma mx bl bc cbase bf base le
    (sha256_read_overflow count) HA HBody HFreeX) as (mf & HCall & HF & HLoads & HPerm & HNext).
  exists mx, mf. split; [exact HCall|]. split; [exact HS|]. auto.
Qed.
