(** Actual public ctx_8_init entry, source copy, initializer call, context copy,
    writer, return and cleanup. The layout consumer derives every premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_arith8_layout_exec C.jet_sha256_iv_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition ctx_init_env bl bi bc br := PTree.set __res (br,Tstruct _sha256_context noattr)
  (PTree.set _ctx (bc,Tstruct _sha256_context noattr) (sha256_iv_jet_env bl bi)).
Definition ctx_init_temps env bf base bs sbase :=
  le_arith8_layout env f_simplicity_sha_256_ctx_8_init bf (Ptrofs.repr base) bs (Ptrofs.repr sbase).

Lemma ctx_init_entry env m ma mb mc md bl bi bc br bf base bs sbase :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 32 = (mb,bi) ->
  Mem.alloc mb 0 88 = (mc,bc) -> Mem.alloc mc 0 88 = (md,br) ->
  function_entry2 ge0 f_simplicity_sha_256_ctx_8_init
    [Vptr bf (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); env]
    m (ctx_init_env bl bi bc br) (ctx_init_temps env bf base bs sbase) md.
Proof.
  intros HA HB HC HD. constructor.
  - change (list_norepet [_src; _iv; _ctx; __res]); vm_compute.
    repeat (apply list_norepet_cons; [simpl; intuition discriminate|]); constructor.
  - change (list_norepet [_dst; _src; _env]); vm_compute.
    repeat (apply list_norepet_cons; [simpl; intuition discriminate|]); constructor.
  - change (list_disjoint [_dst; _src; _env] [_t'1]); vm_compute; intuition congruence.
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl); [exact HA|].
    eapply alloc_variables_cons with (m1 := mb) (b1 := bi); [exact HB|].
    eapply alloc_variables_cons with (m1 := mc) (b1 := bc); [exact HC|].
    eapply alloc_variables_cons with (m1 := md) (b1 := br); [exact HD|constructor].
  - reflexivity.
Qed.
Lemma ctx_init_sha_symbol : Genv.find_symbol (Clight.genv_genv ge0) _sha256_init = Some (jet_symbol_block _sha256_init).
Proof. vm_compute; reflexivity. Qed.
Lemma ctx_init_sha_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _sha256_init) Ptrofs.zero) = Some (Internal f_sha256_init).
Proof. vm_compute; reflexivity. Qed.
Lemma ctx_init_write_symbol : Genv.find_symbol (Clight.genv_genv ge0) _simplicity_write_sha256_context =
  Some (jet_symbol_block _simplicity_write_sha256_context).
Proof. vm_compute; reflexivity. Qed.
Lemma ctx_init_write_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _simplicity_write_sha256_context) Ptrofs.zero) = Some (Internal f_simplicity_write_sha256_context).
Proof. vm_compute; reflexivity. Qed.

Theorem eval_sha256_ctx8_init_composes env m ma mb mc md ms mi mx me mf bl bi bc br bf base bs sbase srcbytes ctxbytes :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs -> bc <> br ->
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 32 = (mb,bi) ->
  Mem.alloc mb 0 88 = (mc,bc) -> Mem.alloc mc 0 88 = (md,br) ->
  Mem.loadbytes md bs sbase 16 = Some srcbytes -> Mem.storebytes md bl 0 srcbytes = Some ms ->
  Clight2.eval_funcall ge0 ms (Internal f_sha256_init) [Vptr br Ptrofs.zero; Vptr bi Ptrofs.zero] E0 mi Vundef ->
  Mem.loadbytes mi br 0 88 = Some ctxbytes -> Mem.storebytes mi bc 0 ctxbytes = Some mx ->
  Clight2.eval_funcall ge0 mx (Internal f_simplicity_write_sha256_context)
    [Vptr bf (Ptrofs.repr base); Vptr bc Ptrofs.zero] E0 me (Vint Int.one) ->
  Mem.free_list me (blocks_of_env ge0 (ctx_init_env bl bi bc br)) = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_sha_256_ctx_8_init)
    [Vptr bf (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HS HA Hls Hcr HAllocS HAllocI HAllocC HAllocR HSrc HSrcCopy HInit HCtx HCtxCopy HWrite HFree.
  set (e := ctx_init_env bl bi bc br). set (le := ctx_init_temps env bf base bs sbase).
  set (lef := PTree.set _t'1 (Vint Int.one) le).
  eapply eval_funcall_internal with (e := e) (le1 := le) (le2 := lef)
    (m1 := md) (m2 := me) (out := Out_return (Some (Vint Int.one,tbool))).
  - eapply ctx_init_entry; eauto.
  - cbn [f_simplicity_sha_256_ctx_8_init fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := ms).
    + eapply exec_Sassign_copy.
      * apply eval_Evar_local; reflexivity.
      * apply eval_Etempvar; reflexivity.
      * reflexivity.
      * eapply assign_frameItem_copy; [reflexivity| | |left; exact Hls| |exact HSrcCopy].
        -- intros _. rewrite Ptrofs.unsigned_repr by (unfold frame_base_valid in HS; lia); exact HA.
        -- intros _. exists 0; reflexivity.
        -- rewrite Ptrofs.unsigned_repr by (unfold frame_base_valid in HS; lia); exact HSrc.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mx).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mi).
        -- eapply exec_Scall with (vf := Vptr (jet_symbol_block _sha256_init) Ptrofs.zero)
             (vargs := [Vptr br Ptrofs.zero; Vptr bi Ptrofs.zero]) (f := Internal f_sha256_init) (vres := Vundef).
           ++ reflexivity.
           ++ eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact ctx_init_sha_symbol]|apply deref_loc_reference; reflexivity].
           ++ eapply eval_Econs.
              ** apply eval_Eaddrof. apply eval_Evar_local; reflexivity.
              ** reflexivity.
              ** eapply eval_Econs; [eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity]|
                   reflexivity|apply eval_Enil].
           ++ exact ctx_init_sha_funct.
           ++ reflexivity.
           ++ exact HInit.
        -- eapply exec_Sassign_copy.
           ++ apply eval_Evar_local; reflexivity.
           ++ eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_copy; reflexivity].
           ++ reflexivity.
           ++ eapply assign_loc_copy with (b' := br) (ofs' := Ptrofs.zero) (bytes := ctxbytes).
              ** reflexivity.
              ** intros _. change (8 | 0); exists 0; reflexivity.
              ** intros _. change (8 | 0); exists 0; reflexivity.
              ** left; congruence.
              ** exact HCtx.
              ** exact HCtxCopy.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := lef) (m1 := me).
        -- eapply exec_Scall with (vf := Vptr (jet_symbol_block _simplicity_write_sha256_context) Ptrofs.zero)
             (vargs := [Vptr bf (Ptrofs.repr base); Vptr bc Ptrofs.zero])
             (f := Internal f_simplicity_write_sha256_context) (vres := Vint Int.one).
           ++ reflexivity.
           ++ eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact ctx_init_write_symbol]|apply deref_loc_reference; reflexivity].
           ++ eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
              eapply eval_Econs; [apply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
           ++ exact ctx_init_write_funct.
           ++ reflexivity.
           ++ exact HWrite.
        -- apply exec_Sreturn_some. apply eval_Etempvar; unfold lef; apply PTree.gss.
  - cbn; split; [discriminate|reflexivity].
  - exact HFree.
Qed.
