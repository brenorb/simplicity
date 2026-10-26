(** Actual finalization of the generator's 48-byte message. Reuse the
    checked padding-array stores, partial absorption and original u64 caller;
    retain allocation, all C calls, return conversion and array deallocation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Memory Values Events.
Require sha.SHA256.
Require Import C.jet_transport C.jet_memcpy_model C.jet_sx_mem C.jet_uint32_array_init
  C.jet_sha_linkage C.jet_sha_ctx8_model C.jet_sha_be64_exec C.jet_sha_compress_call C.jet_sha_finalize_exec
  C.jet_sha_uchars_prep
  C.jet_secp_linkage C.jet_secp_sha_pure_transport C.jet_secp_sha_context C.jet_secp_sha_startup
  C.jet_secp_sha_absorb_short C.jet_secp_sha_u64_full C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Require C.jets_sha C.jets_secp.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition secp_sha_pad48 := firstn 8 pad_source.
Lemma secp_sha_pad48_length : length secp_sha_pad48=8%nat.
Proof. reflexivity. Qed.
Lemma secp_sha_pad48_bytes : pad_bytes (Int64.repr 48)=secp_sha_pad48.
Proof. reflexivity. Qed.
Lemma secp_sha_pad48_checked : stmt_okb sha_ge secp_ge (map fst secp_sha_pure_helpers)
  [jets_sha.___compound] (cf_fill 63)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_pad48_closed : closed_stmtb secp_sha_pure_helpers (cf_fill 63)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_finalize_u64_symbol : Genv.find_symbol secp_ge jets_sha._sha256_u64be=
  Some (secp_symbol_block jets_sha._sha256_u64be).
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_finalize_u64_funct : Genv.find_funct secp_ge
  (Vptr (secp_symbol_block jets_sha._sha256_u64be) Ptrofs.zero)=Some (Internal jets_secp.f_sha256_u64be).
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge sha_ge.

Lemma secp_sha_fin_dom bk : edom (fin_env bk) [(jets_sha.___compound,tarray tuchar 64)].
Proof.
  intros id b ty Lookup;unfold fin_env in Lookup;rewrite PTree.gsspec in Lookup.
  destruct (peq id jets_sha.___compound) as [Same|Other];[subst id;injection Lookup as <- <-;left;reflexivity|].
  rewrite PTree.gempty in Lookup;discriminate.
Qed.
Lemma secp_sha_pad48_transport bk le m mf :
  Clight2.exec_stmt sha_ge (fin_env bk) le m (cf_fill 63) E0 le mf Out_normal ->
  Clight2.exec_stmt secp_ge (fin_env bk) le m (cf_fill 63) E0 le mf Out_normal.
Proof.
  intro Run;exact (proj1 (transport_main sha_ge secp_ge (map fst secp_sha_pure_helpers)
    (transportable_of_entries sha_ge secp_ge secp_sha_pure_helpers
      (secp_sha_helpers_entries sha_ge (or_intror eq_refl)) (secp_sha_helpers_ok sha_ge (or_intror eq_refl))))
    (fin_env bk) le m (cf_fill 63) E0 le mf Out_normal Run
    [(jets_sha.___compound,tarray tuchar 64)] (secp_sha_fin_dom bk) secp_sha_pad48_checked).
Qed.
Lemma secp_sha_finalize48_entry m mi bk bc : Mem.alloc m 0 64=(mi,bk) ->
  function_entry2 secp_ge jets_secp.f_sha256_finalize [Vptr bc Ptrofs.zero] m
    (fin_env bk) (fin_temps bc 0) mi.
Proof.
  intro Alloc;constructor.
  - cbn;repeat constructor;cbn;intuition discriminate.
  - cbn;repeat constructor;cbn;intuition discriminate.
  - intros a b HX HY Hxy;cbn in HX,HY.
    repeat match goal with H:_ \/ _ |- _=>destruct H end;subst;
      first [contradiction|vm_compute in Hxy;discriminate|congruence].
  - eapply alloc_variables_cons with (m1:=mi) (b1:=bk).
    + change (Mem.alloc m 0 64=(mi,bk));exact Alloc.
    + constructor.
  - reflexivity.
Qed.
Lemma secp_sha_finalize48_blocks bk : blocks_of_env secp_ge (fin_env bk)=[(bk,0,64)].
Proof. reflexivity. Qed.

Ltac secp_fin48_expr := first [apply eval_Econst_int|apply eval_Etempvar;reflexivity|
  eapply eval_Ebinop;[secp_fin48_expr|secp_fin48_expr|reflexivity]].

Theorem eval_secp_sha_finalize48 (Hmodel:memcpy_model) l regs m bc bs :
  length l=48%nat ->length regs=8%nat ->bc<>bs ->secp_sha_startup m ->
  Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->
  Mem.load Mptr m bc 0=Some (Vptr bs Ptrofs.zero) ->uint32_array_at m bs 0 regs ->
  Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr 48)) ->
  Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->
  (forall i,(i<48)%nat ->Mem.load Mint8unsigned m bc (16+Z.of_nat i)=Some (Vint (nth i l Int.zero))) ->
  exists mf,Clight2.eval_funcall secp_ge m (Internal jets_secp.f_sha256_finalize)
    [Vptr bc Ptrofs.zero] E0 mf (Vint Int.one) /\
  uint32_array_at mf bs 0 (SHA256.hash_block regs (be_words (l++sha_pad (Int64.repr 48)))) /\
  Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
  Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 64)) /\
  Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
  Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
  lframe (fun b _=>b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\secp_sha_startup mf.
Proof.
  intros LL LR CS Startup FC FS Pointer State Counter Overflow Buffer.
  assert (VC:Mem.valid_block m bc) by (eapply Mem.perm_valid_block;apply (FC 0);lia).
  assert (VS:Mem.valid_block m bs) by (eapply Mem.perm_valid_block;apply (FS 0);lia).
  destruct (Mem.alloc m 0 64) as (m1,bk) eqn:Alloc.
  pose proof (mext_alloc _ _ _ _ _ Alloc) as (VA & LA & PA & AA).
  assert (Fresh:forall b,Mem.valid_block m b ->b<>bk).
  { intros b Old Same;subst b;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Old). }
  assert (PadOther:bk<>bc /\bk<>bs) by (split;[exact (not_eq_sym (Fresh bc VC))|exact (not_eq_sym (Fresh bs VS))]).
  assert (FB:Mem.range_perm m1 bk 0 64 Cur Freeable) by (intros pos Range;eapply Mem.perm_alloc_2;eauto).
  set (le0:=fin_temps bc 0).
  set (le1:=PTree.set jets_sha._result (Vint Int.one) (PTree.set jets_sha._t'3 (Vint Int.zero) le0)).
  set (le2:=PTree.set jets_sha._length (Vlong (Int64.repr 384))
    (PTree.set jets_sha._t'2 (Vlong (Int64.repr 48)) le1)).
  set (le3:=PTree.set jets_sha._t'1 (Vlong (Int64.repr 48)) le2).
  destruct (cf_fill_exec bk (fin_env bk) eq_refl 63 ltac:(lia) le2 m1
    ltac:(intros pos Range;eapply Mem.perm_implies;[apply FB;exact Range|constructor])) as
    (m2 & Fill & PadBytes & LoadsP & PermP & ValidP).
  pose proof (secp_sha_pad48_transport bk le2 m1 m2 Fill) as FillCall.
  assert (FillReadonly:readonly_preserved m1 m2).
  { eapply (proj1 (internal_exec_preserved _ _ secp_sha_pure_table_ok));[exact FillCall| |exact secp_sha_pad48_closed].
    apply plain_set;[apply plain_empty|reflexivity]. }
  assert (R2:readonly_preserved m m2) by (eapply preserved_trans;[eapply alloc_preserved;exact Alloc|exact FillReadonly]).
  assert (K2:forall ch b ofs,Mem.valid_block m b ->Mem.load ch m2 b ofs=Mem.load ch m b ofs).
  { intros ch b ofs Old;rewrite LoadsP by (apply Fresh;exact Old);apply LA;exact Old. }
  assert (V2:forall b,Mem.valid_block m b ->Mem.valid_block m2 b) by (intros;apply ValidP,VA;assumption).
  assert (Frame2:lframe (fun _ _=>True) m m2).
  { split;[intros;apply K2;assumption|];split;[intros;apply PermP,PA;assumption|exact V2]. }
  assert (Ready2:secp_sha_startup m2).
  { eapply secp_sha_startup_preserved;[exact Startup|exact R2|exact Frame2|intros;exact I]. }
  destruct (eval_secp_sha_absorb_short Hmodel l secp_sha_pad48 m2 bc bk Ptrofs.zero (Vptr bs Ptrofs.zero)
    ltac:(rewrite LL,secp_sha_pad48_length;lia) (Fresh bc VC) Ready2
    ltac:(intros pos Range;apply PermP,PA,FC;exact Range)
    ltac:(rewrite secp_sha_pad48_length;change (8<=18446744073709551615);lia)) as
    (m3 & Pad & Pointer3 & Counter3 & Overflow3 & Buffer3 & FC3 & Frame3 & R3 & Ready3).
  { rewrite K2 by exact VC;exact Pointer. }
  { rewrite K2 by exact VC;rewrite LL;exact Counter. }
  { rewrite K2 by exact VC;exact Overflow. }
  { intros i Index;rewrite K2 by exact VC;apply Buffer;rewrite LL in Index;exact Index. }
  { intros i Index;rewrite secp_sha_pad48_length in Index;unfold secp_sha_pad48.
    rewrite nth_firstn_lt by exact Index;apply PadBytes;lia. }
  destruct (eval_secp_sha_u64_full Hmodel (l++secp_sha_pad48) regs (Int64.repr 384) m3 bc bs
    ltac:(rewrite app_length,LL,secp_sha_pad48_length;reflexivity) LR CS Ready3 FC3) as
    (m4 & LengthCall & Output & Pointer4 & Counter4 & Overflow4 & FC4 & FS4 & Frame4 & R4 & Ready4).
  { intros pos Range;apply (proj1 (proj2 Frame3));[apply V2;exact VS|congruence|apply PermP,PA,FS;exact Range]. }
  { exact Pointer3. }
  { intros i v Nth;rewrite (proj1 Frame3) by (first [apply V2;exact VS|intros;congruence]);
      rewrite K2 by exact VS;apply State;exact Nth. }
  { rewrite app_length,LL,secp_sha_pad48_length in Counter3;exact Counter3. }
  { exact Overflow3. }
  { intros i Index;apply Buffer3;rewrite app_length,LL,secp_sha_pad48_length;exact Index. }
  assert (VB2:Mem.valid_block m2 bk) by (apply ValidP;eapply Mem.valid_new_block;exact Alloc).
  assert (FB4:Mem.range_perm m4 bk 0 64 Cur Freeable).
  { intros pos Range;apply (proj1 (proj2 Frame4));[apply (proj2 (proj2 Frame3));exact VB2|exact PadOther|].
    apply (proj1 (proj2 Frame3));[exact VB2|exact (proj1 PadOther)|apply PermP,FB;exact Range]. }
  destruct (Mem.range_perm_free m4 bk 0 64 FB4) as (mf & Free).
  assert (FreeFrame:lframe (fun b _=>b<>bk) m4 mf).
  { apply lframe_unchanged;eapply Mem.free_unchanged_on;[exact Free|intros pos Range Other;apply Other;reflexivity]. }
  assert (RF:readonly_preserved m4 mf) by (eapply free_preserved;exact Free).
  assert (FinalFrame:lframe (fun b _=>b<>bc /\b<>bs) m mf).
  { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\b<>bc /\b<>bs).
    - eapply lframe_trans.
      + eapply lframe_implies;[exact Frame2|intros;exact I].
      + eapply lframe_trans.
        * eapply lframe_implies;[exact Frame3|intros b pos [Old [NC NS]] Valid;exact NC].
        * eapply lframe_trans.
          -- eapply lframe_implies;[exact Frame4|intros b pos [Old Outside] Valid;exact Outside].
          -- eapply lframe_implies;[exact FreeFrame|intros b pos [Old Outside] Valid;apply Fresh;exact Old].
    - intros b pos Outside Old;split;assumption. }
  exists mf;split.
  - eapply eval_funcall_internal with (e:=fin_env bk) (le1:=le0) (m1:=m1) (le2:=le3) (m2:=m4)
      (out:=Out_return (Some (Vint Int.one,tbool))).
    + apply secp_sha_finalize48_entry;exact Alloc.
    + change (fn_body jets_secp.f_sha256_finalize) with
        (Ssequence fin_result (Ssequence fin_length (Ssequence fin_pad (Ssequence fin_len_call (Sreturn (Some (Etempvar jets_sha._result tbool))))))).
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le1) (m1:=m1).
      { unfold fin_result;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
        - apply exec_Sset;eapply (eval_secp_ctx_field SOverflow) with (chunk:=Mint8unsigned) (base:=0);
            [lia|change (88<=18446744073709551615);lia|reflexivity|reflexivity|rewrite LA by exact VC;exact Overflow].
        - apply exec_Sset;eapply eval_Ecast with (v1:=Val.of_bool true);
            [eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|reflexivity]|reflexivity]. }
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le2) (m1:=m1).
      { unfold fin_length;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
        - apply exec_Sset;eapply (eval_secp_ctx_field SCounter) with (chunk:=Mint64) (base:=0);
            [lia|change (88<=18446744073709551615);lia|reflexivity|reflexivity|rewrite LA by exact VC;exact Counter].
        - apply exec_Sset;eapply eval_Ebinop;[apply eval_Etempvar;apply PTree.gss|constructor|reflexivity]. }
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le3) (m1:=m3).
      { unfold fin_pad;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact FillCall|].
        eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le3) (m1:=m2).
        - apply exec_Sset;eapply (eval_secp_ctx_field SCounter) with (chunk:=Mint64) (base:=0);
            [lia|change (88<=18446744073709551615);lia|reflexivity|reflexivity|rewrite K2 by exact VC;exact Counter].
        - change le3 with (set_opttemp None (Vint Int.one) le3) at 2.
          eapply exec_Scall with (vf:=Vptr (secp_symbol_block jets_sha._sha256_uchars) Ptrofs.zero)
            (vargs:=[Vptr bc Ptrofs.zero;Vptr bk Ptrofs.zero;Vlong (Int64.repr 8)])
            (f:=Internal jets_secp.f_sha256_uchars) (vres:=Vint Int.one).
          + reflexivity.
          + eapply eval_Elvalue;[apply eval_Evar_global;[reflexivity|exact secp_sha_u64_uchars_symbol]|apply deref_loc_reference;reflexivity].
          + eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|].
            eapply eval_Econs.
            * eapply eval_Elvalue;[apply eval_Evar_local;reflexivity|apply deref_loc_reference;reflexivity].
            * reflexivity.
            * eapply eval_Econs with (v1:=Vlong (Int64.repr 8));[unfold fin_pad_len;secp_fin48_expr|reflexivity|constructor].
          + exact secp_sha_u64_uchars_funct.
          + reflexivity.
          + exact Pad. }
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le3) (m1:=m4).
      { unfold fin_len_call;change le3 with (set_opttemp None (Vint Int.one) le3) at 2.
        eapply exec_Scall with (vf:=Vptr (secp_symbol_block jets_sha._sha256_u64be) Ptrofs.zero)
          (vargs:=[Vptr bc Ptrofs.zero;Vlong (Int64.repr 384)]) (f:=Internal jets_secp.f_sha256_u64be) (vres:=Vint Int.one).
        - reflexivity.
        - eapply eval_Elvalue;[apply eval_Evar_global;[reflexivity|exact secp_sha_finalize_u64_symbol]|apply deref_loc_reference;reflexivity].
        - eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|].
          eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|constructor].
        - exact secp_sha_finalize_u64_funct.
        - reflexivity.
        - exact LengthCall. }
      apply exec_Sreturn_some;apply eval_Etempvar;reflexivity.
    + cbn;split;[discriminate|reflexivity].
    + rewrite secp_sha_finalize48_blocks;cbn [Mem.free_list];rewrite Free;reflexivity.
  - split.
    + replace (l++sha_pad (Int64.repr 48)) with ((l++secp_sha_pad48)++c_be64_bytes (Int64.repr 384))
        by (unfold sha_pad;rewrite secp_sha_pad48_bytes,app_assoc;reflexivity).
      intros i v Nth;erewrite Mem.load_free;[apply Output;exact Nth|exact Free|left;apply Fresh;exact VS].
    + split.
      * erewrite Mem.load_free;[exact Pointer4|exact Free|left;apply Fresh;exact VC].
      * split.
        -- erewrite Mem.load_free;[exact Counter4|exact Free|left;apply Fresh;exact VC].
        -- split.
           ++ erewrite Mem.load_free;[exact Overflow4|exact Free|left;apply Fresh;exact VC].
           ++ split.
              ** intros pos Range;eapply Mem.perm_free_1;[exact Free|left;apply Fresh;exact VC|apply FC4;exact Range].
              ** split.
                 --- intros pos Range;eapply Mem.perm_free_1;[exact Free|left;apply Fresh;exact VS|apply FS4;exact Range].
                 --- split;[exact FinalFrame|];split.
                     +++ eapply preserved_trans;[exact R2|];eapply preserved_trans;[exact R3|];eapply preserved_trans;[exact R4|exact RF].
                     +++ eapply secp_sha_startup_preserved;[exact Ready4|exact RF|exact FreeFrame|].
                         intros pos;destruct (secp_sha_startup_separate m4 bk 64 Ready4 ltac:(lia) FB4) as [Other _];congruence.
Qed.
