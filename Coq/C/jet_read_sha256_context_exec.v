(** Actual full reader body composition. INTERNAL adapter: calls and current
    memory observations below must be derived by an initial-only consumer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_wide C.jet_sha256_context_fields C.jet_sha256_read_local.
Require Import C.jet_read_sha256_counter C.jet_read_sha256_overflow C.jet_readBit_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition sha256_read_buffer_call := match fn_body f_simplicity_read_sha256_context with
  | Ssequence s _ => s | _ => Sskip end.
Definition sha256_read_count_stmt := match fn_body f_simplicity_read_sha256_context with
  | Ssequence _ (Ssequence s _) => s | _ => Sskip end.
Definition sha256_read_state_stmt := match fn_body f_simplicity_read_sha256_context with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence s _))) => s | _ => Sskip end.
Lemma sha256_read_body_shape : fn_body f_simplicity_read_sha256_context =
  Ssequence sha256_read_buffer_call (Ssequence sha256_read_count_stmt
    (Ssequence sha256_read_counter_stmt (Ssequence sha256_read_state_stmt sha256_read_overflow_stmt))).
Proof. reflexivity. Qed.

Lemma sha256_read_buffer_symbol : Genv.find_symbol (Clight.genv_genv ge0) _simplicity_read_buffer8 =
  Some (jet_symbol_block _simplicity_read_buffer8).
Proof. vm_compute; reflexivity. Qed.
Lemma sha256_read_buffer_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _simplicity_read_buffer8) Ptrofs.zero) = Some (Internal f_simplicity_read_buffer8).
Proof. vm_compute; reflexivity. Qed.
Lemma sha256_read_state_symbol : Genv.find_symbol (Clight.genv_genv ge0) _read32s =
  Some (jet_symbol_block _read32s).
Proof. vm_compute; reflexivity. Qed.
Lemma sha256_read_state_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _read32s) Ptrofs.zero) = Some (Internal f_read32s).
Proof. vm_compute; reflexivity. Qed.

Lemma call_sha256_read_buffer le m mb bl bc cbase bf base :
  le!_ctx = Some (Vptr bc (Ptrofs.repr cbase)) -> le!_src = Some (Vptr bf (Ptrofs.repr base)) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_read_buffer8)
    [Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16)); Vptr bl Ptrofs.zero;
     Vptr bf (Ptrofs.repr base); Vint (Int.repr 5)] E0 mb Vundef ->
  Clight2.exec_stmt ge0 (sha256_read_env bl) le m sha256_read_buffer_call E0 le mb Out_normal.
Proof.
  intros HC HF HCall. eapply exec_Scall with
    (vf := Vptr (jet_symbol_block _simplicity_read_buffer8) Ptrofs.zero)
    (vargs := [Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16)); Vptr bl Ptrofs.zero;
      Vptr bf (Ptrofs.repr base); Vint (Int.repr 5)])
    (f := Internal f_simplicity_read_buffer8) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha256_read_buffer_symbol]|
      apply deref_loc_reference; reflexivity].
  - eapply eval_Econs; [apply eval_sha256_context_block; exact HC|reflexivity|].
    eapply eval_Econs; [apply eval_Eaddrof, eval_Evar_local; reflexivity|reflexivity|].
    eapply eval_Econs; [apply eval_Etempvar; exact HF|reflexivity|].
    eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
  - exact sha256_read_buffer_funct.
  - reflexivity.
  - exact HCall.
Qed.

Lemma call_sha256_read_count le m mc bl bf base count :
  le!_src = Some (Vptr bf (Ptrofs.repr base)) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_read64)
    [Vptr bf (Ptrofs.repr base)] E0 mc (Vlong count) ->
  Clight2.exec_stmt ge0 (sha256_read_env bl) le m sha256_read_count_stmt E0
    (PTree.set _compressionCount (Vlong count) (PTree.set _t'1 (Vlong count) le)) mc Out_normal.
Proof.
  intros HF HCall. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
    (le1 := PTree.set _t'1 (Vlong count) le) (m1 := mc).
  - eapply exec_Scall with (vf := Vptr (jet_symbol_block _simplicity_read64) Ptrofs.zero)
      (vargs := [Vptr bf (Ptrofs.repr base)]) (f := Internal f_simplicity_read64) (vres := Vlong count).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact (wide_reader_symbol W64)]|
        apply deref_loc_reference; reflexivity].
    + eapply eval_Econs; [apply eval_Etempvar; exact HF|reflexivity|apply eval_Enil].
    + exact (wide_reader_funct W64).
    + reflexivity.
    + exact HCall.
  - apply exec_set. apply eval_Etempvar, PTree.gss.
Qed.

Lemma call_sha256_read_state le m me bl bc cbase bf base bi output :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  le!_ctx = Some (Vptr bc (Ptrofs.repr cbase)) -> le!_src = Some (Vptr bf (Ptrofs.repr base)) ->
  Mem.load Mptr m bc cbase = Some (Vptr bi (Ptrofs.repr output)) ->
  Clight2.eval_funcall ge0 m (Internal f_read32s)
    [Vptr bi (Ptrofs.repr output); Vlong (Int64.repr 8); Vptr bf (Ptrofs.repr base)] E0 me Vundef ->
  Clight2.exec_stmt ge0 (sha256_read_env bl) le m sha256_read_state_stmt E0
    (PTree.set _t'4 (Vptr bi (Ptrofs.repr output)) le) me Out_normal.
Proof.
  intros HB HM HC HF HL HCall.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
    (le1 := PTree.set _t'4 (Vptr bi (Ptrofs.repr output)) le) (m1 := m).
  - apply exec_set. eapply eval_sha256_context_field with (k := CtxOutput) (id := _ctx) (chunk := Mptr);
      [exact HB|exact HM|reflexivity|exact HC|].
    change (Mem.load Mptr m bc (cbase + 0) = Some (Vptr bi (Ptrofs.repr output))).
    rewrite Z.add_0_r; exact HL.
  - eapply exec_Scall with (vf := Vptr (jet_symbol_block _read32s) Ptrofs.zero)
      (vargs := [Vptr bi (Ptrofs.repr output); Vlong (Int64.repr 8); Vptr bf (Ptrofs.repr base)])
      (f := Internal f_read32s) (vres := Vundef).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha256_read_state_symbol]|
        apply deref_loc_reference; reflexivity].
    + eapply eval_Econs; [apply eval_Etempvar, PTree.gss|reflexivity|].
      eapply eval_Econs; [apply eval_Econst_int|reflexivity|].
      eapply eval_Econs; [apply eval_Etempvar; rewrite PTree.gso by discriminate; exact HF|reflexivity|apply eval_Enil].
    + exact sha256_read_state_funct.
    + reflexivity.
    + exact HCall.
Qed.

Theorem exec_sha256_read_context_composes m mb mc md me bl bc cbase bf base bi output count len :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_read_buffer8)
    [Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16)); Vptr bl Ptrofs.zero;
      Vptr bf (Ptrofs.repr base); Vint (Int.repr 5)] E0 mb Vundef ->
  Clight2.eval_funcall ge0 mb (Internal f_simplicity_read64) [Vptr bf (Ptrofs.repr base)] E0 mc (Vlong count) ->
  Mem.load Mint64 mc bl 0 = Some (Vlong len) ->
  Mem.store Mint64 mc bc (cbase + 8) (Vlong (sha256_read_counter count len)) = Some md ->
  Mem.load Mptr md bc cbase = Some (Vptr bi (Ptrofs.repr output)) ->
  Clight2.eval_funcall ge0 md (Internal f_read32s)
    [Vptr bi (Ptrofs.repr output); Vlong (Int64.repr 8); Vptr bf (Ptrofs.repr base)] E0 me Vundef ->
  Mem.load Mint64 me (jet_symbol_block _sha256_max_counter) 0 = Some (Vlong (Int64.repr 2305843009213693952)) ->
  bc <> jet_symbol_block _sha256_max_counter ->
  Mem.valid_access me Mint8unsigned bc (cbase + 80) Writable ->
  exists mf lef,
    Clight2.exec_stmt ge0 (sha256_read_env bl) (sha256_read_temps bc cbase bf base) m
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
  destruct (exec_sha256_read_overflow_from_observation (sha256_read_env bl) le3 me bc cbase count
    HB HM eq_refl HGlobal HOther HC3 HCount3 HW) as (mf & lef & HOverflow & HS & HL & HG).
  exists mf, lef. split; [|exact HS]. rewrite sha256_read_body_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := mb).
  - eapply call_sha256_read_buffer; eauto.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mc).
    + eapply call_sha256_read_count; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := md).
      * unfold sha256_read_counter_stmt.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mc).
        -- apply exec_set. eapply eval_Elvalue;
             [apply eval_Evar_local; reflexivity|apply deref_loc_value with (chunk := Mint64); [reflexivity|exact HLen]].
        -- eapply exec_sha256_read_counter_store; [exact HB|exact HM|
             unfold le2, le1; repeat rewrite PTree.gso by discriminate; exact HC|
             unfold le2, le1; repeat rewrite PTree.gso by discriminate; apply PTree.gss|
             unfold le2; apply PTree.gss|exact HCounter].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := me).
        -- eapply call_sha256_read_state; [exact HB|exact HM|
             unfold le2, le1; repeat rewrite PTree.gso by discriminate; exact HC|
             unfold le2, le1; repeat rewrite PTree.gso by discriminate; exact HF|exact HOutput|exact HState].
        -- exact HOverflow.
Qed.

Theorem eval_sha256_read_context_composes m ma mb mc md me bl bc cbase bf base bi output count len :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  Mem.alloc m 0 8 = (ma,bl) ->
  Clight2.eval_funcall ge0 ma (Internal f_simplicity_read_buffer8)
    [Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16)); Vptr bl Ptrofs.zero;
      Vptr bf (Ptrofs.repr base); Vint (Int.repr 5)] E0 mb Vundef ->
  Clight2.eval_funcall ge0 mb (Internal f_simplicity_read64) [Vptr bf (Ptrofs.repr base)] E0 mc (Vlong count) ->
  Mem.load Mint64 mc bl 0 = Some (Vlong len) ->
  Mem.store Mint64 mc bc (cbase + 8) (Vlong (sha256_read_counter count len)) = Some md ->
  Mem.load Mptr md bc cbase = Some (Vptr bi (Ptrofs.repr output)) ->
  Clight2.eval_funcall ge0 md (Internal f_read32s)
    [Vptr bi (Ptrofs.repr output); Vlong (Int64.repr 8); Vptr bf (Ptrofs.repr base)] E0 me Vundef ->
  Mem.load Mint64 me (jet_symbol_block _sha256_max_counter) 0 = Some (Vlong (Int64.repr 2305843009213693952)) ->
  bc <> jet_symbol_block _sha256_max_counter ->
  Mem.valid_access me Mint8unsigned bc (cbase + 80) Writable ->
  Mem.range_perm me bl 0 8 Cur Freeable ->
  exists mx mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_read_sha256_context)
      [Vptr bc (Ptrofs.repr cbase); Vptr bf (Ptrofs.repr base)] E0 mf
      (Vint (bit_int (negb (sha256_read_overflow count)))) /\
    Mem.store Mint8unsigned me bc (cbase + 80) (Vint (bit_int (sha256_read_overflow count))) = Some mx /\
    Mem.free_list mx (blocks_of_env ge0 (sha256_read_env bl)) = Some mf /\
    (forall chunk b ofs, b <> bl -> Mem.load chunk mf b ofs = Mem.load chunk mx b ofs) /\
    (forall b ofs kind p, b <> bl -> Mem.perm mx b ofs kind p -> Mem.perm mf b ofs kind p) /\
    Mem.nextblock mf = Mem.nextblock mx.
Proof.
  intros HB HM HA HBuffer HCount HLen HCounter HOutput HState HGlobal HOther HW HFree.
  destruct (exec_sha256_read_context_composes ma mb mc md me bl bc cbase bf base bi output count len
    HB HM HBuffer HCount HLen HCounter HOutput HState HGlobal HOther HW)
    as (mx & le & HBody & HS).
  assert (HFreeX : Mem.range_perm mx bl 0 8 Cur Freeable).
  { intros ofs HR. eapply Mem.perm_store_1; [exact HS|apply HFree; exact HR]. }
  destruct (eval_sha256_read_context_from_body m ma mx bl bc cbase bf base le
    (sha256_read_overflow count) HA HBody HFreeX) as (mf & HCall & HF & HLoads & HPerm & HNext).
  exists mx, mf. split; [exact HCall|]. split; [exact HS|]. auto.
Qed.
