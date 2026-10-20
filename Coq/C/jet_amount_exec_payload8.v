(** Actual explicit-amount eight-byte read and absorption in the original 32-byte scratch array. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_exec C.jet_memcpy_model C.jet_frame_layout C.jet_input_layout C.jet_encoding.
Require Import C.jet_buffer_input C.jet_readBit_layout C.jet_read8s_layout.
Require Import C.jet_elements_support_sha_ctx_abs C.jet_sha_ctx8_model C.jet_elements_support_sha_uchars_exec C.jet_elements_support_sha_add_n_init.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_transport C.jet_elements_support_sha_block_local C.jet_elements_sha_program.
Require Import C.jets_elements C.jet_elements_linkage.
Require Import C.jet_nonce_context_shape C.jet_nonce_exec_effects C.jet_nonce_exec_calls.
Import Mem Values Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge sha_ge ge0.
Set Default Timeout 10.

Require Import C.jet_nonce_exec_payload C.jet_asset_exec_shape.

Theorem amount_payload8_exec (Hmodel : memcpy_model) le m bl bm bb bx bi edge rc
    (h : Ty.tySem Word64) l regs c ovf :
  bl <> bx -> bl <> bm -> bl <> GC -> bl <> GM ->
  bb <> bx -> bb <> bm -> bb <> GC -> bb <> GM ->
  bl <> bb -> bl <> bi -> bb <> bi ->
  bm <> bx -> GC <> bx -> GC <> bm -> GM <> bx -> GM <> bm ->
  0 <= rc -> rc + 64 <= Int64.max_unsigned ->
  frame_fields_at m bl 0 bi edge rc -> Mem.valid_access m Mint64 bl 8 Writable ->
  Mem.range_perm m bb 0 8 Cur Writable ->
  frame_input_cells_at m bi edge rc (@encode Word64 h) -> ctx_abs m bx bm l regs c ovf ->
  exists mf,
    Clight2.exec_stmt elements_ge (nc_env bl bm bb bx) le m (Ssequence amount_read8 amount_absorb8) E0 le mf Out_normal /\
    frame_fields_at mf bl 0 bi edge (rc + 64) /\
    ctx_abs mf bx bm (fst (absorb l regs (vector_values (Word 3) 3 h)))
      (snd (absorb l regs (vector_values (Word 3) 3 h)))
      (Int64.add c (Int64.repr 8)) (uc_overflow ovf c (Int64.repr 8)) /\
    nonce_effects m mf [bl; bb; bx; bm].
Proof.
  intros Hlx Hlm Hlg Hlc Hbx Hbm Hbg Hbc Hlb Hli Hbi Hmx Hgx Hgm Hcx Hcm H0 HM HF PW PB HI HC.
  set (e := nc_env bl bm bb bx).
  set (vs := vector_values (Word 3) 3 h).
  assert (Lvs : length vs = 8%nat) by apply (vector_values_length (Word 3) 3).
  assert (HIv : forall i x, nth_error vs i = Some x -> frame_input_word_at m bi edge (rc + 8 * Z.of_nat i) x).
  { apply frame_input_byte_list. unfold vs. rewrite <- (encode_vector_values (Word 3) 3 h). exact HI. }
  destruct (eval_read8s_layout m bb 0 bl 0 bi edge rc vs
    ltac:(lia) ltac:(rewrite Lvs; change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(rewrite Lvs; exact PB) Hlb Hli Hbi nonce_local_frame_base H0 ltac:(rewrite Lvs; lia) HF PW HIv)
    as (mr & HRead & HArray & HFields & HLoads & HPerm & HValid).
  rewrite Lvs in HRead, HFields.
  change (rc + 8 * Z.of_nat 8) with (rc + 64) in HFields.
  assert (ER : nonce_effects m mr [bl; bb]).
  { constructor; [|exact HPerm|exact HValid]. intros ch b ofs V N.
    apply HLoads; left; intro E; apply N; first [solve [left; symmetry; exact E] | solve [right; left; symmetry; exact E]]. }
  assert (HCr : ctx_abs mr bx bm l regs c ovf).
  { eapply (nonce_effects_ctx m mr [bl; bb] bx bm l regs c ovf).
    - exact ER.
    - intros [EQ|[EQ|[]]]; [exact (Hlx EQ)|exact (Hbx EQ)].
    - intros [EQ|[EQ|[]]]; [exact (Hlm EQ)|exact (Hbm EQ)].
    - intros [EQ|[EQ|[]]]; [exact (Hlg EQ)|exact (Hbg EQ)].
    - intros [EQ|[EQ|[]]]; [exact (Hlc EQ)|exact (Hbc EQ)].
    - exact HC. }
  destruct (ctx_abs_uchars bx bm Hmx Hgx Hgm Hcx Hcm Hmodel mr bb Ptrofs.zero l regs vs c ovf
    HCr Hbx Hbm ltac:(rewrite Lvs; change (0 + 8 <= Ptrofs.max_unsigned);
      change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(intros i HJ; apply HArray, nth_error_nth'; exact HJ))
    as (mf & HAdd & HCtx & HLoadsA & HPermA & HValidA).
  rewrite Lvs in HAdd, HCtx.
  assert (EA : nonce_effects mr mf [bx; bm]).
  { constructor.
    - intros ch b ofs V N. apply HLoadsA; [exact V| |]; intro E; apply N; first [solve [left; symmetry; exact E] | solve [right; left; symmetry; exact E]].
    - intros b ofs k p HP. apply HPermA; [eapply Mem.perm_valid_block; exact HP|exact HP].
    - exact HValidA. }
  assert (HReadStmt : Clight2.exec_stmt elements_ge e le m amount_read8 E0 le mr Out_normal).
  { destruct nonce_readbytes_link as [HS HFun]. unfold amount_read8.
    change le with (set_opttemp None Vundef le) at 2.
    eapply exec_Scall with (vf := Vptr (elements_symbol_block _read8s) Ptrofs.zero)
      (f := Internal f_read8s) (vargs := [Vptr bb Ptrofs.zero; Vlong (Int64.repr 8); Vptr bl Ptrofs.zero]) (vres := Vundef).
    - reflexivity.
    - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact HS]|apply deref_loc_reference; reflexivity].
    - eapply eval_Econs.
      + eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
      + reflexivity.
      + eapply eval_Econs; [apply eval_Econst_int|reflexivity|].
        eapply eval_Econs; [apply eval_Eaddrof, eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
    - exact HFun.
    - reflexivity.
    - rewrite <- elements_sha_genv. eapply sha_transport_call; [|exact HRead].
      exact C.jet_elements_support_sha_add_n_exec.sg_in_read8s. }
  assert (HAddStmt : Clight2.exec_stmt elements_ge e le mr amount_absorb8 E0 le mf Out_normal).
  { destruct nonce_uchars_link as [HS HFun]. unfold amount_absorb8.
    change le with (set_opttemp None (Vint (bit_int (negb (uc_overflow ovf c (Int64.repr 8))))) le) at 2.
    eapply exec_Scall with (vf := Vptr (elements_symbol_block _sha256_uchars) Ptrofs.zero)
      (f := Internal f_sha256_uchars) (vargs := [Vptr bx Ptrofs.zero; Vptr bb Ptrofs.zero; Vlong (Int64.repr 8)])
      (vres := Vint (bit_int (negb (uc_overflow ovf c (Int64.repr 8))))).
    - reflexivity.
    - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact HS]|apply deref_loc_reference; reflexivity].
    - eapply eval_Econs; [apply eval_Eaddrof, eval_Evar_local; reflexivity|reflexivity|].
      eapply eval_Econs.
      + eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
      + reflexivity.
      + eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
    - exact HFun.
    - reflexivity.
    - rewrite <- elements_sha_genv. exact HAdd. }
  exists mf. split.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le); eassumption.
  - split.
    + eapply nonce_effects_fields; [exact EA|cbn; intuition congruence|exact HFields].
    + split; [exact HCtx|].
      eapply nonce_effects_union with (m1 := mr) (bs := [bl; bb]) (cs := [bx; bm]); eassumption.
Qed.
