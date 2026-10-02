(** Actual full_multiply_64 body composition. Layout consumers discharge
    every intermediate call from original frames; this rule is not coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_wide C.jet_binary_wide_exec C.jet_multiply64_exec.
Require Import C.jet_umul128_layout C.jet_u128_accum_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition frame_u128_mul_call := Scall None
  (Evar _secp256k1_u128_mul (Tfunction (Tcons (tptr (Tstruct _secp256k1_uint128 noattr))
    (Tcons tulong (Tcons tulong Tnil))) tvoid cc_default))
  [Eaddrof (Evar _r (Tstruct _secp256k1_uint128 noattr)) (tptr (Tstruct _secp256k1_uint128 noattr));
    Etempvar _x tulong; Etempvar _y tulong].
Definition frame_u128_accum_call id := Scall None
  (Evar _secp256k1_u128_accum_u64 (Tfunction (Tcons (tptr (Tstruct _secp256k1_uint128 noattr))
    (Tcons tulong Tnil)) tvoid cc_default))
  [Eaddrof (Evar _r (Tstruct _secp256k1_uint128 noattr)) (tptr (Tstruct _secp256k1_uint128 noattr));
    Etempvar id tulong].
Definition full_multiply64_temps env bd dbase bs sbase :=
  le_arith8_layout env f_simplicity_full_multiply_64 bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase).
Definition full_multiply64_read_temps env bd dbase bs sbase a b u v :=
  PTree.set _w (Vlong v) (PTree.set _t'4 (Vlong v)
    (PTree.set _z (Vlong u) (PTree.set _t'3 (Vlong u)
      (PTree.set _y (Vlong b) (PTree.set _t'2 (Vlong b)
        (PTree.set _x (Vlong a) (PTree.set _t'1 (Vlong a)
          (full_multiply64_temps env bd dbase bs sbase)))))))).

Lemma call_frame_u128_mul le m mk bl br a b :
  le!_x = Some (Vlong a) -> le!_y = Some (Vlong b) ->
  Clight2.eval_funcall ge0 m (Internal f_secp256k1_u128_mul)
    [Vptr br Ptrofs.zero; Vlong a; Vlong b] E0 mk Vundef ->
  Clight2.exec_stmt ge0 (e_frame_u128 bl br) le m frame_u128_mul_call E0 le mk Out_normal.
Proof.
  intros HX HY HC. eapply exec_Scall with (vf := Vptr (jet_symbol_block _secp256k1_u128_mul) Ptrofs.zero)
    (vargs := [Vptr br Ptrofs.zero; Vlong a; Vlong b]) (f := Internal f_secp256k1_u128_mul) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [reflexivity|exact u128_mul_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof, eval_Evar_local. unfold e_frame_u128; apply PTree.gss.
    + reflexivity.
    + eapply eval_Econs; [apply eval_Etempvar; exact HX|reflexivity|].
      eapply eval_Econs; [apply eval_Etempvar; exact HY|reflexivity|apply eval_Enil].
  - exact u128_mul_funct.
  - reflexivity.
  - exact HC.
Qed.

Lemma call_frame_u128_accum id le m mk bl br a :
  le!id = Some (Vlong a) ->
  Clight2.eval_funcall ge0 m (Internal f_secp256k1_u128_accum_u64)
    [Vptr br Ptrofs.zero; Vlong a] E0 mk Vundef ->
  Clight2.exec_stmt ge0 (e_frame_u128 bl br) le m (frame_u128_accum_call id) E0 le mk Out_normal.
Proof.
  intros HA HC. eapply exec_Scall with (vf := Vptr (jet_symbol_block _secp256k1_u128_accum_u64) Ptrofs.zero)
    (vargs := [Vptr br Ptrofs.zero; Vlong a]) (f := Internal f_secp256k1_u128_accum_u64) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [reflexivity|exact u128_accum_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof, eval_Evar_local. unfold e_frame_u128; apply PTree.gss.
    + reflexivity.
    + eapply eval_Econs; [apply eval_Etempvar; exact HA|reflexivity|apply eval_Enil].
  - exact u128_accum_funct.
  - reflexivity.
  - exact HC.
Qed.

Ltac full_multiply64_read_step mi leNext HC :=
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leNext) (m1 := mi);
  [eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi);
    [apply (call_frame_u128_read W64); exact HC|apply exec_set, eval_Etempvar, PTree.gss]|].

Lemma eval_full_multiply64_composes env m ma mb mc mr1 mr2 mr3 mr4 mk mz mw me mf
    bl br bd dbase bs sbase bytes a b u v :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 16 = (mb,br) ->
  Mem.loadbytes mb bs sbase 16 = Some bytes -> Mem.storebytes mb bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read64) [Vptr bl Ptrofs.zero] E0 mr1 (Vlong a) ->
  Clight2.eval_funcall ge0 mr1 (Internal f_simplicity_read64) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong b) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_read64) [Vptr bl Ptrofs.zero] E0 mr3 (Vlong u) ->
  Clight2.eval_funcall ge0 mr3 (Internal f_simplicity_read64) [Vptr bl Ptrofs.zero] E0 mr4 (Vlong v) ->
  Clight2.eval_funcall ge0 mr4 (Internal f_secp256k1_u128_mul) [Vptr br Ptrofs.zero; Vlong a; Vlong b] E0 mk Vundef ->
  Clight2.eval_funcall ge0 mk (Internal f_secp256k1_u128_accum_u64) [Vptr br Ptrofs.zero; Vlong u] E0 mz Vundef ->
  Clight2.eval_funcall ge0 mz (Internal f_secp256k1_u128_accum_u64) [Vptr br Ptrofs.zero; Vlong v] E0 mw Vundef ->
  Clight2.eval_funcall ge0 mw (Internal f_write128) [Vptr bd (Ptrofs.repr dbase); Vptr br Ptrofs.zero] E0 me Vundef ->
  Mem.free_list me (blocks_of_env ge0 (e_frame_u128 bl br)) = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_full_multiply_64)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HSbase HAlign HN HA HB Hbytes Hcopy HR1 HR2 HR3 HR4 HM HZ HW Hwrite HF.
  set (le0 := full_multiply64_temps env bd dbase bs sbase).
  set (le1 := PTree.set _x (Vlong a) (PTree.set _t'1 (Vlong a) le0)).
  set (le2 := PTree.set _y (Vlong b) (PTree.set _t'2 (Vlong b) le1)).
  set (le3 := PTree.set _z (Vlong u) (PTree.set _t'3 (Vlong u) le2)).
  set (le4 := full_multiply64_read_temps env bd dbase bs sbase a b u v).
  eapply eval_funcall_internal with (e := e_frame_u128 bl br) (le1 := le0) (le2 := le4)
    (m1 := mb) (m2 := me) (out := Out_return (Some (Vint Int.one,tint))).
  - eapply entry_frame_u128_jet; try eassumption; try reflexivity.
    change (list_disjoint [_dst; _src; _env] [_x; _y; _z; _w; _t'4; _t'3; _t'2; _t'1]).
    vm_compute; intuition congruence.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := mc).
    + eapply exec_frame_u128_copy; try eassumption; reflexivity.
    + full_multiply64_read_step mr1 le1 HR1.
      full_multiply64_read_step mr2 le2 HR2.
      full_multiply64_read_step mr3 le3 HR3.
      full_multiply64_read_step mr4 le4 HR4.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := mk).
      * eapply call_frame_u128_mul with (a := a) (b := b); [| |exact HM];
          unfold le4, full_multiply64_read_temps; umul128_lookup.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := mz).
        -- eapply call_frame_u128_accum with (a := u); [|exact HZ]. unfold le4, full_multiply64_read_temps; umul128_lookup.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := mw).
           ++ eapply call_frame_u128_accum with (a := v); [|exact HW]. unfold le4, full_multiply64_read_temps; umul128_lookup.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := me).
              ** eapply call_frame_writer with (f := f_write128) (b := jet_symbol_block _write128)
                   (v := Vptr br Ptrofs.zero) (vret := Vundef).
                 --- reflexivity.
                 --- reflexivity.
                 --- reflexivity.
                 --- exact write128_symbol.
                 --- exact write128_funct.
                 --- apply eval_Eaddrof, eval_Evar_local. unfold e_frame_u128; apply PTree.gss.
                 --- reflexivity.
                 --- exact Hwrite.
              ** apply exec_Sreturn_some, eval_Econst_int.
  - cbn; split; solve [discriminate|reflexivity].
  - exact HF.
Qed.
