(** Actual context writer for a zero counter and non-overflowing context.
    The layout consumer must derive all calls and intermediate field loads. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_sha256_context_fields C.jet_umul128_layout.
Require Import C.jet_arith8_layout_exec C.jet_wide C.jet_sha256_iv_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition ctx8_buffer_call := Scall None
  (Evar _simplicity_write_buffer8 (Tfunction
    (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr tuchar) (Tcons tulong (Tcons tint Tnil)))) tvoid cc_default))
  [Etempvar _dst (tptr (Tstruct _frameItem noattr)); sha256_context_field_expr CtxBlock _ctx;
   Ebinop Omod (Etempvar _t'4 tulong) (Econst_int (Int.repr 64) tint) tulong; Econst_int (Int.repr 5) tint].
Definition ctx8_counter_call := Scall None
  (Evar _simplicity_write64 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
  [Etempvar _dst (tptr (Tstruct _frameItem noattr));
   Ebinop Oshr (Etempvar _t'3 tulong) (Econst_int (Int.repr 6) tint) tulong].
Definition ctx8_iv_call := Scall None
  (Evar _write32s (Tfunction
    (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr tuint) (Tcons tulong Tnil))) tvoid cc_default))
  [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'2 (tptr tuint); Econst_int (Int.repr 8) tint].
Definition ctx8_write_temps bf base bc cbase := PTree.set _ctx (Vptr bc (Ptrofs.repr cbase))
  (PTree.set _dst (Vptr bf (Ptrofs.repr base)) (create_undef_temps f_simplicity_write_sha256_context.(fn_temps))).

Lemma ctx8_write_body : f_simplicity_write_sha256_context.(fn_body) =
  Ssequence (Ssequence (Sset _t'4 (sha256_context_field_expr CtxCounter _ctx)) ctx8_buffer_call)
    (Ssequence (Ssequence (Sset _t'3 (sha256_context_field_expr CtxCounter _ctx)) ctx8_counter_call)
      (Ssequence (Ssequence (Sset _t'2 (sha256_context_field_expr CtxOutput _ctx)) ctx8_iv_call)
        (Ssequence (Sset _t'1 (sha256_context_field_expr CtxOverflow _ctx))
          (Sreturn (Some (Eunop Onotbool (Etempvar _t'1 tbool) tint)))))).
Proof. reflexivity. Qed.
Lemma ctx8_buffer_symbol : Genv.find_symbol (Clight.genv_genv ge0) _simplicity_write_buffer8 =
  Some (jet_symbol_block _simplicity_write_buffer8).
Proof. vm_compute; reflexivity. Qed.
Lemma ctx8_buffer_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _simplicity_write_buffer8) Ptrofs.zero) = Some (Internal f_simplicity_write_buffer8).
Proof. vm_compute; reflexivity. Qed.

Lemma call_ctx8_empty_buffer le m mf bf base bc cbase :
  le!_dst = Some (Vptr bf (Ptrofs.repr base)) -> le!_ctx = Some (Vptr bc (Ptrofs.repr cbase)) ->
  le!_t'4 = Some (Vlong Int64.zero) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_write_buffer8)
    [Vptr bf (Ptrofs.repr base); Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16));
     Vlong Int64.zero; Vint (Int.repr 5)] E0 mf Vundef ->
  Clight2.exec_stmt ge0 empty_env le m ctx8_buffer_call E0 le mf Out_normal.
Proof.
  intros HD HC H4 Hcall. eapply exec_Scall with
    (vf := Vptr (jet_symbol_block _simplicity_write_buffer8) Ptrofs.zero)
    (vargs := [Vptr bf (Ptrofs.repr base); Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16));
      Vlong Int64.zero; Vint (Int.repr 5)]) (f := Internal f_simplicity_write_buffer8) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact ctx8_buffer_symbol]|apply deref_loc_reference; reflexivity].
  - eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs; [apply eval_sha256_context_block; exact HC|reflexivity|].
    eapply eval_Econs.
    + eapply eval_Ebinop with (v1 := Vlong Int64.zero) (v2 := Vint (Int.repr 64));
        [apply eval_Etempvar; exact H4|apply eval_Econst_int|reflexivity].
    + reflexivity.
    + eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
  - exact ctx8_buffer_funct.
  - reflexivity.
  - exact Hcall.
Qed.

Theorem eval_write_sha256_context_empty_composes m mb mc mf bf base bc cbase bi input :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m bc (cbase + 8) = Some (Vlong Int64.zero) ->
  Mem.load Mint64 mb bc (cbase + 8) = Some (Vlong Int64.zero) ->
  Mem.load Mptr mc bc cbase = Some (Vptr bi (Ptrofs.repr input)) ->
  Mem.load Mint8unsigned mf bc (cbase + 80) = Some (Vint Int.zero) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_write_buffer8)
    [Vptr bf (Ptrofs.repr base); Vptr bc (Ptrofs.add (Ptrofs.repr cbase) (Ptrofs.repr 16));
     Vlong Int64.zero; Vint (Int.repr 5)] E0 mb Vundef ->
  Clight2.eval_funcall ge0 mb (Internal f_simplicity_write64)
    [Vptr bf (Ptrofs.repr base); Vlong Int64.zero] E0 mc Vundef ->
  Clight2.eval_funcall ge0 mc (Internal f_write32s)
    [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr input); Vlong (Int64.repr 8)] E0 mf Vundef ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_write_sha256_context)
    [Vptr bf (Ptrofs.repr base); Vptr bc (Ptrofs.repr cbase)] E0 mf (Vint Int.one).
Proof.
  intros HB HM HC0 HC1 HO HF HBuffer HCounter HIV.
  set (le0 := ctx8_write_temps bf base bc cbase).
  set (le1 := PTree.set _t'4 (Vlong Int64.zero) le0).
  set (le2 := PTree.set _t'3 (Vlong Int64.zero) le1).
  set (le3 := PTree.set _t'2 (Vptr bi (Ptrofs.repr input)) le2).
  set (le4 := PTree.set _t'1 (Vint Int.zero) le3).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le0) (le2 := le4)
    (m1 := m) (m2 := mf) (out := Out_return (Some (Vint Int.one,tint))).
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
      * eapply call_ctx8_empty_buffer; [unfold le1, le0, ctx8_write_temps; umul128_lookup|
          unfold le1, le0, ctx8_write_temps; umul128_lookup|unfold le1; apply PTree.gss|exact HBuffer].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mc).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mb).
        -- apply exec_set. eapply eval_sha256_context_field with (chunk := Mint64);
             [exact HB|exact HM|reflexivity|unfold le1, le0, ctx8_write_temps; umul128_lookup|exact HC1].
        -- eapply call_frame_writer with (f := f_simplicity_write64) (b := jet_symbol_block _simplicity_write64)
             (v := Vlong Int64.zero) (vret := Vundef).
           ++ reflexivity.
           ++ unfold le2, le1, le0, ctx8_write_temps; umul128_lookup.
           ++ reflexivity.
           ++ exact (wide_writer_symbol W64).
           ++ exact (wide_writer_funct W64).
           ++ unfold le2. umul128_scalar.
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
           ++ apply exec_Sreturn_some. eapply eval_Eunop with (v1 := Vint Int.zero);
                [apply eval_Etempvar; unfold le4; apply PTree.gss|reflexivity].
  - cbn; split; [discriminate|reflexivity].
  - reflexivity.
Qed.
