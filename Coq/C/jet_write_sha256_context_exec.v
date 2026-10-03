(** Actual context writer with arbitrary counters and either overflow flag.
    Internal composition only: initial-only consumers must derive all calls
    and intermediate field loads before this supports public jet coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_sha256_context_fields C.jet_umul128_layout.
Require Import C.jet_arith8_layout_exec C.jet_wide C.jet_sha256_iv_exec.
Require Import C.jet_write_sha256_context_empty_exec C.jet_readBit_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma call_ctx8_buffer le m mf bf base bc cbase counter :
  le!_dst = Some (Vptr bf (Ptrofs.repr base)) -> le!_ctx = Some (Vptr bc (Ptrofs.repr cbase)) ->
  le!_t'4 = Some (Vlong counter) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_write_buffer8)
    [Vptr bf (Ptrofs.repr base); Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16));
     Vlong (Int64.modu counter (Int64.repr 64)); Vint (Int.repr 5)] E0 mf Vundef ->
  Clight2.exec_stmt ge0 empty_env le m ctx8_buffer_call E0 le mf Out_normal.
Proof.
  intros HD HC H4 Hcall. eapply exec_Scall with
    (vf := Vptr (jet_symbol_block _simplicity_write_buffer8) Ptrofs.zero)
    (vargs := [Vptr bf (Ptrofs.repr base); Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16));
      Vlong (Int64.modu counter (Int64.repr 64)); Vint (Int.repr 5)]) (f := Internal f_simplicity_write_buffer8) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact ctx8_buffer_symbol]|apply deref_loc_reference; reflexivity].
  - eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs; [apply eval_sha256_context_block; exact HC|reflexivity|].
    eapply eval_Econs.
    + eapply eval_Ebinop with (v1 := Vlong counter) (v2 := Vint (Int.repr 64));
        [apply eval_Etempvar; exact H4|apply eval_Econst_int|reflexivity].
    + reflexivity.
    + eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
  - exact ctx8_buffer_funct.
  - reflexivity.
  - exact Hcall.
Qed.

Theorem eval_write_sha256_context_composes m mb mc mf bf base bc cbase bi input counter overflow :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m bc (cbase + 8) = Some (Vlong counter) ->
  Mem.load Mint64 mb bc (cbase + 8) = Some (Vlong counter) ->
  Mem.load Mptr mc bc cbase = Some (Vptr bi (Ptrofs.repr input)) ->
  Mem.load Mint8unsigned mf bc (cbase + 80) = Some (Vint (bit_int overflow)) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_write_buffer8)
    [Vptr bf (Ptrofs.repr base); Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16));
     Vlong (Int64.modu counter (Int64.repr 64)); Vint (Int.repr 5)] E0 mb Vundef ->
  Clight2.eval_funcall ge0 mb (Internal f_simplicity_write64)
    [Vptr bf (Ptrofs.repr base); Vlong (Int64.shru counter (Int64.repr 6))] E0 mc Vundef ->
  Clight2.eval_funcall ge0 mc (Internal f_write32s)
    [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr input); Vlong (Int64.repr 8)] E0 mf Vundef ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_write_sha256_context)
    [Vptr bf (Ptrofs.repr base); Vptr bc (Ptrofs.repr cbase)] E0 mf (Vint (bit_int (negb overflow))).
Proof.
  intros HB HM HC0 HC1 HO HF HBuffer HCounter HIV.
  set (le0 := ctx8_write_temps bf base bc cbase).
  set (le1 := PTree.set _t'4 (Vlong counter) le0).
  set (le2 := PTree.set _t'3 (Vlong counter) le1).
  set (le3 := PTree.set _t'2 (Vptr bi (Ptrofs.repr input)) le2).
  set (le4 := PTree.set _t'1 (Vint (bit_int overflow)) le3).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le0) (le2 := le4)
    (m1 := m) (m2 := mf) (out := Out_return (Some (Vint (bit_int (negb overflow)),tint))).
  - constructor.
    + constructor.
    + change (list_norepet [_dst; _ctx]). vm_compute.
      repeat (apply list_norepet_cons; [simpl; intuition discriminate|]). constructor.
    + change (list_disjoint [_dst; _ctx] [_t'4; _t'3; _t'2; _t'1]); vm_compute; intuition congruence.
    + constructor.
    + reflexivity.
  - rewrite ctx8_write_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mb).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
      * apply exec_set. eapply eval_sha256_context_field with (chunk := Mint64);
          [exact HB|exact HM|reflexivity|unfold le0, ctx8_write_temps; umul128_lookup|exact HC0].
      * eapply call_ctx8_buffer; [unfold le1, le0, ctx8_write_temps; umul128_lookup|
          unfold le1, le0, ctx8_write_temps; umul128_lookup|unfold le1; apply PTree.gss|exact HBuffer].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mc).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mb).
        -- apply exec_set. eapply eval_sha256_context_field with (chunk := Mint64);
             [exact HB|exact HM|reflexivity|unfold le1, le0, ctx8_write_temps; umul128_lookup|exact HC1].
        -- eapply call_frame_writer with (f := f_simplicity_write64) (b := jet_symbol_block _simplicity_write64)
             (v := Vlong (Int64.shru counter (Int64.repr 6))) (vret := Vundef).
           ++ reflexivity.
           ++ unfold le2, le1, le0, ctx8_write_temps; umul128_lookup.
           ++ reflexivity.
           ++ exact (wide_writer_symbol W64).
           ++ exact (wide_writer_funct W64).
           ++ eapply eval_Ebinop with (v1 := Vlong counter) (v2 := Vint (Int.repr 6)).
              ** apply eval_Etempvar. unfold le2; apply PTree.gss.
              ** apply eval_Econst_int.
              ** reflexivity.
           ++ reflexivity.
           ++ exact HCounter.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := mf).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := mc).
           ++ apply exec_set. eapply eval_sha256_context_field with (chunk := Mptr);
                [exact HB|exact HM|reflexivity|unfold le2, le1, le0, ctx8_write_temps; umul128_lookup|].
              change (Mem.load Mptr mc bc (cbase + 0) = Some (Vptr bi (Ptrofs.repr input))). rewrite Z.add_0_r; exact HO.
           ++ eapply exec_Scall with (vf := Vptr (jet_symbol_block _write32s) Ptrofs.zero)
                (vargs := [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr input); Vlong (Int64.repr 8)])
                (f := Internal f_write32s) (vres := Vundef).
              ** reflexivity.
              ** eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact write32s_symbol]|apply deref_loc_reference; reflexivity].
              ** eapply eval_Econs; [apply eval_Etempvar; unfold le3, le2, le1, le0, ctx8_write_temps; umul128_lookup|reflexivity|].
                 eapply eval_Econs; [apply eval_Etempvar; unfold le3; apply PTree.gss|reflexivity|].
                 eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
              ** exact write32s_funct.
              ** reflexivity.
              ** exact HIV.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := mf).
           ++ apply exec_set. eapply eval_sha256_context_field with (chunk := Mint8unsigned);
                [exact HB|exact HM|reflexivity|unfold le3, le2, le1, le0, ctx8_write_temps; umul128_lookup|exact HF].
           ++ apply exec_Sreturn_some. eapply eval_Eunop with (v1 := Vint (bit_int overflow));
                [apply eval_Etempvar; unfold le4; apply PTree.gss|destruct overflow; reflexivity].
  - cbn; split; [discriminate|destruct overflow; reflexivity].
  - reflexivity.
Qed.
