(** Actual two-local eq_256 function entry, source copy and call boundary.
    Reader/array/loop premises are internal and must be derived by the
    initial-only layout contract before this counts as jet equivalence. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_eq256_array C.jet_eq256_loop C.jet_uint32_array_init.
Require Import C.jet_readBit_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition eq256_temps env bd dbase bs sbase :=
  le_arith8_layout env f_simplicity_eq_256 bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase).

Lemma eq256_entry env m ma mb bl ba bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 64 = (mb, ba) ->
  function_entry2 ge0 f_simplicity_eq_256
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
    m (eq256_env bl ba) (eq256_temps env bd dbase bs sbase) mb.
Proof.
  intros HA HB. constructor.
  - change (list_norepet [_src; _arr]). unfold _src, _arr.
    repeat constructor; simpl; intuition discriminate.
  - change (list_norepet [_dst; _src; _env]). unfold _dst, _src, _env.
    repeat constructor; simpl; intuition discriminate.
  - change (list_disjoint [_dst; _src; _env] [_i; _t'2; _t'1]).
    intros i j HI HJ Heq. cbn in HI, HJ; subst j.
    destruct HI as [HI|[HI|[HI|HI]]]; destruct HJ as [HJ|[HJ|[HJ|HJ]]];
      try contradiction; vm_compute in HI, HJ; congruence.
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma, bl)); exact HA.
    + eapply alloc_variables_cons with (m1 := mb) (b1 := ba).
      * change (Mem.alloc ma 0 64 = (mb, ba)); exact HB.
      * constructor.
  - reflexivity.
Qed.

Lemma exec_eq256_source_copy m mc bl ba bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt ge0 (eq256_env bl ba) le m
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    E0 le mc Out_normal.
Proof.
  intros HB HS HD HL Hload Hstore.
  assert (HA : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr. unfold frame_base_valid in HB; lia. }
  eapply exec_Sassign_copy.
  - eapply eval_Evar_local; reflexivity.
  - eapply eval_Etempvar; exact HL.
  - reflexivity.
  - eapply assign_frameItem_copy.
    + reflexivity.
    + intros _. rewrite HA; exact HS.
    + intros _. exists 0; reflexivity.
    + left; exact HD.
    + rewrite HA; exact Hload.
    + exact Hstore.
Qed.

Lemma read32s_symbol : Genv.find_symbol (Clight.genv_genv ge0) _read32s =
  Some (jet_symbol_block _read32s).
Proof. vm_compute; reflexivity. Qed.
Lemma read32s_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _read32s) Ptrofs.zero) = Some (Internal f_read32s).
Proof. vm_compute; reflexivity. Qed.
Definition eq256_read_call :=
  Scall None (Evar _read32s (Tfunction
    (Tcons (tptr tuint) (Tcons tulong (Tcons (tptr (Tstruct _frameItem noattr)) Tnil)))
    tvoid cc_default))
    [Evar _arr (tarray tuint 16); Econst_int (Int.repr 16) tint;
      Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))].
Definition eq256_compare_block :=
  Ssequence (Ssequence (Sset _i (Econst_int Int.zero tint)) eq256_loop)
    (Ssequence (eq256_write Datatypes.true) eq256_return).
Lemma eq256_body_shape : f_simplicity_eq_256.(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence eq256_read_call eq256_compare_block).
Proof. reflexivity. Qed.
Lemma call_eq256_read32s bl ba le m mf :
  Clight2.eval_funcall ge0 m (Internal f_read32s)
    [Vptr ba Ptrofs.zero; Vlong (Int64.repr 16); Vptr bl Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt ge0 (eq256_env bl ba) le m eq256_read_call E0 le mf Out_normal.
Proof.
  intros HR. eapply exec_Scall with (vf := Vptr (jet_symbol_block _read32s) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero; Vlong (Int64.repr 16); Vptr bl Ptrofs.zero])
    (f := Internal f_read32s) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [eapply eval_Evar_global; [reflexivity|apply read32s_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + eapply eval_Elvalue; [eapply eval_Evar_local; reflexivity|].
      apply deref_loc_reference; reflexivity.
    + reflexivity.
    + eapply eval_Econs; [apply eval_Econst_int|reflexivity|].
      eapply eval_Econs; [eapply eval_Eaddrof; eapply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
  - apply read32s_funct.
  - reflexivity.
  - exact HR.
Qed.

Theorem eval_eq256_composes env m ma mb mc mr me mt mf bl ba bd dbase bs sbase bytes xs ys :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 64 = (mb, ba) ->
  Mem.loadbytes mb bs sbase 16 = Some bytes -> Mem.storebytes mb bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_read32s)
    [Vptr ba Ptrofs.zero; Vlong (Int64.repr 16); Vptr bl Ptrofs.zero] E0 mr Vundef ->
  length xs = 8%nat -> length ys = 8%nat -> uint32_array_at mr ba 0 (xs ++ ys) ->
  Clight2.eval_funcall ge0 mr (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (eq256_words_equal xs ys))]
    E0 me (Vint (bit_int (eq256_words_equal xs ys))) ->
  Mem.free me bl 0 16 = Some mt -> Mem.free mt ba 0 64 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_eq_256)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HS HA HD HallocS HallocA Hbytes Hstore Hread HX HY Harray Hwrite HfreeS HfreeA.
  set (le := eq256_temps env bd dbase bs sbase).
  assert (HDst : le!_dst = Some (Vptr bd (Ptrofs.repr dbase))) by reflexivity.
  assert (HFirst : forall j x, nth_error xs j = Some x ->
    Mem.load Mint32 mr ba (4 * Z.of_nat j) = Some (Vint x)).
  { intros j x Hj. apply (Harray j x).
    rewrite nth_error_app1; [exact Hj|].
    apply nth_error_Some; rewrite Hj; discriminate. }
  assert (HSecond : forall j y, nth_error ys j = Some y ->
    Mem.load Mint32 mr ba (4 * (Z.of_nat j + 8)) = Some (Vint y)).
  { intros j y Hj.
    replace (4 * (Z.of_nat j + 8)) with (0 + 4 * Z.of_nat (8 + j)) by lia.
    apply Harray. rewrite nth_error_app2 by (rewrite HX; lia).
    rewrite HX. replace (8 + j - 8)%nat with j by lia. exact Hj. }
  destruct (exec_eq256_compare bl ba le mr me bd dbase xs ys HX HY HDst HFirst HSecond Hwrite)
    as [lef HCompare].
  eapply eval_funcall_internal with (e := eq256_env bl ba) (le1 := le) (le2 := lef)
    (m1 := mb) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply eq256_entry; eauto.
  - rewrite eq256_body_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
    + eapply exec_eq256_source_copy; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le).
      * apply call_eq256_read32s; exact Hread.
      * exact HCompare.
  - cbn; split; [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16); (ba, 0, 64)] = Some mf).
    cbn. rewrite HfreeS, HfreeA; reflexivity.
Qed.
