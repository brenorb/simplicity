(** Original Schnorr challenge-tag initialization. Constant-array and SHA
    compound initialization are reused; the public signature callers follow. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jets C.jets_secp C.jet_exec C.jet_secp_linkage C.jet_sx_exec C.jet_sx_mem
 C.jet_transport C.jet_uint32_array_init C.jet_uint32_array_prefix C.jet_struct_copy_loads
 C.jet_sha256_init_exec C.jet_sha256_init_fields_layout C.jet_sha256_tagged_fields
 C.jet_secp_statement_prefix C.jet_secp_local_regions C.jet_secp_closed_helpers
 C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Values Mem Ctypes Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition schnorr_tagged_constants : list Z :=
 [2632759825;596792193;292000018;3512892943;2546496848;3983205;2432045412;870954602].
Definition schnorr_tagged_words := map uint32_init_value schnorr_tagged_constants.
Definition schnorr_tagged_copy := Sassign
 (Ederef (Etempvar __res (tptr (Tstruct _sha256_context noattr))) (Tstruct _sha256_context noattr))
 (Evar ___compound (Tstruct _sha256_context noattr)).
Definition schnorr_tagged_tail := Ssequence (Ssequence sha_ctx_tagged_fields_stmt schnorr_tagged_copy) (Sreturn None).
Lemma schnorr_tagged_body_shape : fn_body f_secp256k1_schnorrsig_sha256_tagged=
 statement_sequence (uint32_init_statements_at _output 0 schnorr_tagged_constants) schnorr_tagged_tail.
Proof. reflexivity. Qed.

Lemma schnorr_tagged_fields_checked :
 stmt_okb ge0 secp_ge [] [___compound] sha_ctx_tagged_fields_stmt=true.
Proof. vm_compute;reflexivity. Qed.
Lemma schnorr_tagged_fields_transport e le m mf bc :
 e=sha_init_env bc ->
 Clight2.exec_stmt ge0 e le m sha_ctx_tagged_fields_stmt E0 le mf Out_normal ->
 Clight2.exec_stmt secp_ge e le m sha_ctx_tagged_fields_stmt E0 le mf Out_normal.
Proof.
 intros Env Run;subst e.
 assert (Calls:transportable ge0 secp_ge []) by (intros id Member;contradiction).
 eapply (proj1 (transport_main ge0 secp_ge [] Calls)) with
  (vars:=[(___compound,Tstruct _sha256_context noattr)]);[exact Run| |exact schnorr_tagged_fields_checked].
 unfold edom,sha_init_env;intros id b ty Lookup.
 rewrite PTree.gsspec in Lookup;destruct (peq id jets.___compound).
 - subst id;inversion Lookup;subst;left;reflexivity.
 - discriminate.
Qed.
Local Opaque secp_ge ge0.

Lemma schnorr_tagged_entry m ma bc br bs : Mem.alloc m 0 88=(ma,bc) ->
 function_entry2 secp_ge f_secp256k1_schnorrsig_sha256_tagged
  [Vptr br Ptrofs.zero;Vptr bs Ptrofs.zero] m (sha_init_env bc) (sha_init_temps br bs 0) ma.
Proof.
 intro Alloc;assert (Ok:fn_okb f_secp256k1_schnorrsig_sha256_tagged=true) by reflexivity.
 destruct (fn_okb_true _ Ok) as (Vars & Params & Disjoint);constructor;
 [exact Vars|exact Params|exact Disjoint| |reflexivity].
 eapply alloc_variables_cons with (m1:=ma) (b1:=bc);[exact Alloc|constructor].
Qed.

Theorem eval_schnorr_tagged_composes m ma mi mz me mf bc br bs bytes :
 bc<>br -> Mem.alloc m 0 88=(ma,bc) ->
 Clight2.exec_stmt secp_ge (sha_init_env bc) (sha_init_temps br bs 0) ma
  (uint32_init_prefix_at _output 0 schnorr_tagged_constants) E0 (sha_init_temps br bs 0) mi Out_normal ->
 Clight2.exec_stmt secp_ge (sha_init_env bc) (sha_init_temps br bs 0) mi
  sha_ctx_tagged_fields_stmt E0 (sha_init_temps br bs 0) mz Out_normal ->
 Mem.loadbytes mz bc 0 88=Some bytes -> Mem.storebytes mz br 0 bytes=Some me ->
 Mem.free me bc 0 88=Some mf ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_schnorrsig_sha256_tagged)
  [Vptr br Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef.
Proof.
 intros Separate Alloc Init Fields Load Copy Free;pose (le:=sha_init_temps br bs 0).
 eapply eval_funcall_internal with (e:=sha_init_env bc) (le1:=le) (le2:=le)
  (m1:=ma) (m2:=me) (out:=Out_return None).
 - eapply schnorr_tagged_entry;exact Alloc.
 - rewrite schnorr_tagged_body_shape;eapply exec_statement_prefix_then_last;[exact Init|].
   unfold schnorr_tagged_tail;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=me).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mz);[exact Fields|].
     unfold schnorr_tagged_copy;eapply exec_Sassign_copy.
     * apply eval_Ederef;apply eval_Etempvar;unfold le,sha_init_temps;rewrite PTree.gso by discriminate;apply PTree.gss.
     * eapply eval_Elvalue;[apply eval_Evar_local;unfold sha_init_env;apply PTree.gss|apply deref_loc_copy;reflexivity].
     * reflexivity.
     * eapply assign_loc_copy with (b':=bc) (ofs':=Ptrofs.zero) (bytes:=bytes).
       -- reflexivity.
       -- intros _;change (8|0);exists 0;reflexivity.
       -- intros _;change (8|0);exists 0;reflexivity.
       -- left;exact Separate.
       -- exact Load.
       -- exact Copy.
   + apply exec_Sreturn_none.
 - reflexivity.
 - change (Mem.free_list me [(bc,0,88)]=Some mf);cbn;rewrite Free;reflexivity.
Qed.

Theorem eval_schnorr_tagged_init_layout m br bs :
  br <> bs ->
  Mem.range_perm m br 0 88 Cur Writable -> Mem.range_perm m bs 0 (0 + 32) Cur Writable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_schnorrsig_sha256_tagged) [Vptr br Ptrofs.zero; Vptr bs (Ptrofs.repr 0)] E0 mf Vundef /\
    Mem.load Mptr mf br 0 = Some (Vptr bs (Ptrofs.repr 0)) /\
    Mem.load Mint64 mf br 8 = Some (Vlong (Int64.repr 64)) /\
    Mem.load Mint8unsigned mf br 80 = Some (Vint Int.zero) /\
    uint32_array_at mf bs 0 schnorr_tagged_words /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> br \/ ofs + size_chunk chunk <= 0 \/ 88 <= ofs) ->
      (b <> bs \/ ofs + size_chunk chunk <= 0 \/ 0 + 32 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros Hri PR PI.
  assert (VR : Mem.valid_block m br) by (eapply Mem.perm_valid_block; apply (PR 0); lia).
  assert (VI : Mem.valid_block m bs) by (eapply Mem.perm_valid_block; apply (PI 0); lia).
  destruct (Mem.alloc m 0 88) as (ma & bc) eqn:HC.
  assert (HFresh : forall b, Mem.valid_block m b -> bc <> b).
  { intros b HV HE; subst b; exact (Mem.fresh_block_alloc _ _ _ _ _ HC HV). }
  assert (Hcr : bc <> br) by auto. assert (Hci : bc <> bs) by auto.
  assert (PIA : Mem.range_perm ma bs 0 (0 + 32) Cur Writable).
  { intros ofs H; eapply Mem.perm_alloc_1; [exact HC|apply PI; exact H]. }
  destruct (exec_uint32_init_prefix_at secp_ge (sha_init_env bc) _output ma
    (sha_init_temps br bs 0) bs 0 0 schnorr_tagged_constants
    ltac:(unfold sha_init_temps;apply PTree.gss) ltac:(lia)
    ltac:(change (32<=18446744073709551615);lia)
    ltac:(change (8<=2147483647);lia) ltac:(exists 0;reflexivity) PIA)
    as (mi & HInit & HArray & HInitLoads & HInitPerm & HInitValid).
  assert (PC : Mem.range_perm mi bc 0 88 Cur Writable).
  { intros ofs H; apply HInitPerm. eapply Mem.perm_implies;
      [eapply Mem.perm_alloc_2; eauto|constructor]. }
  destruct (exec_sha_ctx_tagged_fields_layout (sha_init_env bc) (sha_init_temps br bs 0) mi bc bs (Ptrofs.repr 0)
    ltac:(unfold sha_init_env; apply Maps.PTree.gss)
    ltac:(unfold sha_init_temps; apply Maps.PTree.gss) PC)
    as (mz & HFieldsGeo & HO & HCounter & HOverflow & HFieldLoads & HFieldPerm & HFieldValid).
  assert (HFields:Clight2.exec_stmt secp_ge (sha_init_env bc) (sha_init_temps br bs 0) mi
    sha_ctx_tagged_fields_stmt E0 (sha_init_temps br bs 0) mz Out_normal).
  { eapply schnorr_tagged_fields_transport;[reflexivity|exact HFieldsGeo]. }
  assert (PCRead : Mem.range_perm mz bc 0 88 Cur Readable).
  { intros ofs H; apply HFieldPerm. eapply Mem.perm_implies; [apply PC; exact H|constructor]. }
  destruct (Mem.range_perm_loadbytes mz bc 0 88 PCRead) as (bytes & HBytes).
  pose proof (Mem.loadbytes_length _ _ _ _ _ HBytes) as HLen.
  assert (PRZ : Mem.range_perm mz br 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite HLen. change (Mem.range_perm mz br 0 88 Cur Writable).
    intros ofs H; apply HFieldPerm, HInitPerm. eapply Mem.perm_alloc_1; [exact HC|apply PR; exact H]. }
  destruct (Mem.range_perm_storebytes mz br 0 bytes PRZ) as (me & HCopy).
  assert (HNewBytes : Mem.loadbytes me br 0 88 = Some bytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HCopy) as H; rewrite HLen in H; exact H. }
  assert (HOutCopy : Mem.load Mptr me br 0 = Some (Vptr bs (Ptrofs.repr 0))).
  { eapply equal_loadbytes_field with (m1 := mz) (b1 := bc) (base1 := 0) (base2 := 0)
      (n := 88) (delta := 0) (bytes := bytes); [lia|change (8 <= 88); lia|exact HBytes|exact HNewBytes|
      change (8 | 0); exists 0; reflexivity|exact HO]. }
  assert (HCounterCopy : Mem.load Mint64 me br 8 = Some (Vlong (Int64.repr 64))).
  { eapply equal_loadbytes_field with (m1 := mz) (b1 := bc) (base1 := 0) (base2 := 0)
      (n := 88) (delta := 8) (bytes := bytes); [lia|change (16 <= 88); lia|exact HBytes|exact HNewBytes|
      change (8 | 8); exists 1; reflexivity|exact HCounter]. }
  assert (HOverflowCopy : Mem.load Mint8unsigned me br 80 = Some (Vint Int.zero)).
  { eapply equal_loadbytes_field with (m1 := mz) (b1 := bc) (base1 := 0) (base2 := 0)
      (n := 88) (delta := 80) (bytes := bytes); [lia|change (81 <= 88); lia|exact HBytes|exact HNewBytes|
      change (1 | 80); exists 80; reflexivity|exact HOverflow]. }
  assert (PCFree : Mem.range_perm me bc 0 88 Cur Freeable).
  { intros ofs H; eapply Mem.perm_storebytes_1; [exact HCopy|apply HFieldPerm, HInitPerm].
    eapply Mem.perm_alloc_2; eauto. }
  destruct (Mem.range_perm_free me bc 0 88 PCFree) as (mf & HFree).
  exists mf. split; [eapply eval_schnorr_tagged_composes; eauto|]. split.
  - erewrite Mem.load_free; [exact HOutCopy|exact HFree|auto].
  - split.
    + erewrite Mem.load_free; [exact HCounterCopy|exact HFree|auto].
    + split.
      * erewrite Mem.load_free; [exact HOverflowCopy|exact HFree|auto].
      * split.
        -- intros i v Hv. erewrite Mem.load_free; [|exact HFree|auto].
           erewrite Mem.load_storebytes_other; [|exact HCopy|left; congruence].
           rewrite HFieldLoads by (left; congruence). exact (HArray i v Hv).
        -- split.
           ++ intros chunk b ofs HV HR HI'. assert (Hbc : b <> bc) by (intro H; apply (HFresh b HV); congruence).
              erewrite Mem.load_free; [|exact HFree|left; exact Hbc].
              erewrite Mem.load_storebytes_other; [|exact HCopy|rewrite HLen; exact HR].
              rewrite HFieldLoads by (left; exact Hbc). rewrite HInitLoads by exact HI'.
              eapply Mem.load_alloc_unchanged; eauto.
           ++ split.
              ** intros b ofs kind p H. assert (Hbc : b <> bc).
                 { intro E. apply (HFresh b); [eapply Mem.perm_valid_block; exact H|congruence]. }
                 eapply Mem.perm_free_1; [exact HFree|left; exact Hbc|].
                 eapply Mem.perm_storebytes_1; [exact HCopy|apply HFieldPerm, HInitPerm].
                 eapply Mem.perm_alloc_1; eauto.
              ** intros b H. eapply Mem.valid_block_free_1; [exact HFree|].
                 eapply Mem.storebytes_valid_block_1; [exact HCopy|apply HFieldValid, HInitValid].
                 eapply Mem.valid_block_alloc; eauto.
Qed.

Lemma schnorr_tagged_closed : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_schnorrsig_sha256_tagged)=true.
Proof. vm_compute;reflexivity. Qed.

Theorem eval_schnorr_tagged_init_owned m bc bs : bc<>bs ->
  Mem.range_perm m bc 0 88 Cur Freeable -> Mem.range_perm m bs 0 32 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_schnorrsig_sha256_tagged)
    [Vptr bc Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef /\
  Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
  Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr 64)) /\
  Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
  uint32_array_at mf bs 0 schnorr_tagged_words /\
  Mem.range_perm mf bc 0 88 Cur Freeable /\ Mem.range_perm mf bs 0 32 Cur Freeable /\
  lframe (fun b _=>b<>bc /\ b<>bs) m mf /\ readonly_preserved m mf.
Proof.
  intros Separate FC FS.
  destruct (eval_schnorr_tagged_init_layout m bc bs Separate
    (freeable_range_writable _ _ _ _ FC) (freeable_range_writable _ _ _ _ FS))
    as (mf & Call & Pointer & Counter & Overflow & State & Loads & Perm & Valid).
  exists mf;split;[exact Call|];split;[exact Pointer|];split;[exact Counter|];split;[exact Overflow|];
    split;[exact State|];split;[intros pos Range;apply Perm,FC;exact Range|];
    split;[intros pos Range;apply Perm,FS;exact Range|];split.
  - split.
    + intros chunk b ofs Old Outside;apply Loads;[exact Old| |];
        [left;pose proof (Outside ofs ltac:(pose proof (size_chunk_pos chunk);lia)) as [NC NS];exact NC|
         left;pose proof (Outside ofs ltac:(pose proof (size_chunk_pos chunk);lia)) as [NC NS];exact NS].
    + split;[intros;apply Perm;assumption|exact Valid].
  - eapply secp_closed_function_preserved;[exact schnorr_tagged_closed|reflexivity|exact Call].
Qed.

