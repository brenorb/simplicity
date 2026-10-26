(** Both complete SHA blocks in the original generator body, with the actual
    initialization/copy, prefix and key calls, finalization and serialization.
    The byte-string bridge identifies the computed registers; the generator's
    SWU/addition/public lifecycle are outside this internal statement span. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Globalenvs Memory Values Events.
Require sha.SHA256 sha.common_lemmas.
Require Import C.jet_memcpy_model C.jet_sx_mem C.jet_uint32_array_init C.jet_sha256_iv_init
  C.jet_sha_ctx8_model C.jet_sha_be32_exec C.jet_sha_finalize_exec C.jet_sha_linkage
  C.jet_secp_linkage C.jet_secp_sha_owned C.jet_secp_sha_pure_transport C.jet_secp_sha_startup
  C.jet_secp_generator_sha_start C.jet_secp_generator_sha_absorb C.jet_secp_sha_finalize48
  C.jet_secp_statement_prefix C.jet_clight_internal_preserve C.jet_secp_sha_bytestring48.
Require Import C.jet_entropy_streaming_byte_blocks Simplicity.Digest.
Require C.jets_sha.
Require Import C.jets_secp.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generator_sha_block (second:bool) := nth (if second then 11%nat else 7%nat)
  (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))) Sskip.
Definition generator_sha_regs second key := SHA256.hash_block sha256_iv_words
  (be_words (generator_sha_prefix_bytes second++key++sha_pad (Int64.repr 48))).
Definition generator_sha_prefix_octets second :=
  map (fun x=>Byte.repr (Int.unsigned x)) (generator_sha_prefix_bytes second).
Lemma generator_sha_prefix_octets_int second : map byte_int (generator_sha_prefix_octets second)=
  generator_sha_prefix_bytes second.
Proof. destruct second;reflexivity. Qed.
Lemma generator_sha_regs_length second key : length key=32%nat ->length (generator_sha_regs second key)=8%nat.
Proof.
  intro Len;apply sha.common_lemmas.length_hash_block;[reflexivity|].
  apply be_words_length;rewrite !app_length,generator_sha_prefix_length,Len;reflexivity.
Qed.
Theorem generator_sha_regs_bytestring second (key:list byte) : length key=32%nat ->
  generator_sha_regs second (map byte_int key)=
    hash256_reg (byteStringHash (generator_sha_prefix_octets second++key)).
Proof.
  intro Len;unfold generator_sha_regs;rewrite app_assoc.
  rewrite <-(generator_sha_prefix_octets_int second),<-map_app;apply secp_sha48_bytestring.
  unfold generator_sha_prefix_octets;rewrite app_length,map_length,generator_sha_prefix_length,Len;reflexivity.
Qed.

Definition generator_sha_finalize_call second := Scall None
  (Evar _sha256_finalize (type_of_function f_sha256_finalize))
  [Eaddrof (Evar (generator_sha_context_id second) generator_sha_ctx_type) (tptr generator_sha_ctx_type)].
Definition generator_sha_digest_call := Scall None
  (Evar _sha256_fromMidstate (type_of_function f_sha256_fromMidstate))
  [Evar _b32 (tarray tuchar 32);Efield (Evar _sha256_buf generator_sha_state_type) _s (tarray tuint 8)].
Lemma generator_sha_final_calls_source second : generator_sha_final_calls second=
  Ssequence (generator_sha_finalize_call second) generator_sha_digest_call.
Proof. destruct second;reflexivity. Qed.
Lemma generator_sha_finalize_symbol : Genv.find_symbol secp_ge _sha256_finalize=
  Some (secp_symbol_block _sha256_finalize).
Proof. vm_compute;reflexivity. Qed.
Lemma generator_sha_finalize_funct : Genv.find_funct secp_ge
  (Vptr (secp_symbol_block _sha256_finalize) Ptrofs.zero)=Some (Internal f_sha256_finalize).
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge sha_ge.

Lemma exec_generator_sha_finalize_call second e le m mf bc :
  e!_sha256_finalize=None ->e!(generator_sha_context_id second)=Some (bc,generator_sha_ctx_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_sha256_finalize) [Vptr bc Ptrofs.zero] E0 mf (Vint Int.one) ->
  Clight2.exec_stmt secp_ge e le m (generator_sha_finalize_call second) E0 le mf Out_normal.
Proof.
  intros Fun Context Call;change le with (set_opttemp None (Vint Int.one) le) at 2.
  unfold generator_sha_finalize_call;eapply exec_Scall with
    (vf:=Vptr (secp_symbol_block _sha256_finalize) Ptrofs.zero) (vargs:=[Vptr bc Ptrofs.zero])
    (f:=Internal f_sha256_finalize) (vres:=Vint Int.one).
  - reflexivity.
  - eapply eval_Elvalue;[apply eval_Evar_global;[exact Fun|exact generator_sha_finalize_symbol]|apply deref_loc_reference;reflexivity].
  - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Context|reflexivity|constructor].
  - exact generator_sha_finalize_funct.
  - reflexivity.
  - exact Call.
Qed.
Lemma exec_generator_sha_digest_call e le m mf bb bs :
  e!_sha256_fromMidstate=None ->e!_b32=Some (bb,tarray tuchar 32) ->
  e!_sha256_buf=Some (bs,generator_sha_state_type) ->
  Clight2.eval_funcall secp_ge m (Internal f_sha256_fromMidstate)
    [Vptr bb Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m generator_sha_digest_call E0 le mf Out_normal.
Proof.
  intros Fun Bytes State Call;change le with (set_opttemp None Vundef le) at 2.
  unfold generator_sha_digest_call.
  destruct (secp_sha_helpers_entries sha_ge (or_intror eq_refl) jets_sha._sha256_fromMidstate
    jets_sha.f_sha256_fromMidstate ltac:(do 5 right;left;reflexivity)) as (b1 & b2 & S1 & F1 & S2 & F2).
  eapply exec_Scall with (vf:=Vptr b2 Ptrofs.zero) (vargs:=[Vptr bb Ptrofs.zero;Vptr bs Ptrofs.zero])
    (f:=Internal f_sha256_fromMidstate) (vres:=Vundef).
  - reflexivity.
  - eapply eval_Elvalue;[apply eval_Evar_global;[exact Fun|exact S2]|apply deref_loc_reference;reflexivity].
  - eapply eval_Econs.
    + eapply eval_Elvalue;[apply eval_Evar_local;exact Bytes|apply deref_loc_reference;reflexivity].
    + reflexivity.
    + eapply eval_Econs;[apply eval_generator_sha_state;exact State|reflexivity|constructor].
  - exact F2.
  - reflexivity.
  - exact Call.
Qed.

Theorem exec_generator_sha_block_owned (Hmodel:memcpy_model) second key e le m br bc bs bb ba oa :
  e!_sha256_init=None ->e!_sha256_uchars=None ->e!_sha256_finalize=None ->e!_sha256_fromMidstate=None ->
  e!(generator_sha_result_id second)=Some (br,generator_sha_ctx_type) ->
  e!(generator_sha_context_id second)=Some (bc,generator_sha_ctx_type) ->
  e!_sha256_buf=Some (bs,generator_sha_state_type) ->e!_b32=Some (bb,tarray tuchar 32) ->
  e!(generator_sha_prefix_id second)=None ->le!_key32=Some (Vptr ba oa) ->
  br<>bc ->br<>bs ->br<>bb ->bc<>bs ->bc<>bb ->bs<>bb ->ba<>br ->ba<>bc ->ba<>bs ->
  length key=32%nat ->Ptrofs.unsigned oa+32<=Ptrofs.max_unsigned ->
  secp_sha_startup m ->generator_sha_prefix_state second m ->
  Mem.range_perm m br 0 88 Cur Freeable ->Mem.range_perm m bc 0 88 Cur Freeable ->
  Mem.range_perm m bs 0 32 Cur Freeable ->Mem.range_perm m bb 0 32 Cur Freeable ->
  (forall i,(i<32)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=Some (Vint (nth i key Int.zero))) ->
  exists mf,Clight2.exec_stmt secp_ge e le m (generator_sha_block second) E0 le mf Out_normal /\
  (forall i,(i<32)%nat ->Mem.load Mint8unsigned mf bb (Z.of_nat i)=
    Some (Vint (Int.repr (nth i (secp_sha_digest_bytes (generator_sha_regs second key)) 0)))) /\
  uint32_array_at mf bs 0 (generator_sha_regs second key) /\
  Mem.range_perm mf br 0 88 Cur Freeable /\Mem.range_perm mf bc 0 88 Cur Freeable /\
  Mem.range_perm mf bs 0 32 Cur Freeable /\Mem.range_perm mf bb 0 32 Cur Freeable /\
  lframe (fun b _=>b<>br /\b<>bc /\b<>bs /\b<>bb) m mf /\readonly_preserved m mf /\
  secp_sha_startup mf /\generator_sha_prefix_state second mf.
Proof.
  intros FI FU FF FD Result Context State Bytes Prefix Key RC RS RB CS CB SB AR AC AS Len Hi Ready PrefixReady FR FC FS FB Input.
  assert (VR:Mem.valid_block m br) by (eapply Mem.perm_valid_block;apply (FR 0);lia).
  assert (VC:Mem.valid_block m bc) by (eapply Mem.perm_valid_block;apply (FC 0);lia).
  assert (VS:Mem.valid_block m bs) by (eapply Mem.perm_valid_block;apply (FS 0);lia).
  assert (VB:Mem.valid_block m bb) by (eapply Mem.perm_valid_block;apply (FB 0);lia).
  assert (VA:Mem.valid_block m ba).
  { pose proof (Input 0%nat ltac:(lia)) as Load;apply Mem.load_valid_access in Load.
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Load|constructor]. }
  destruct (exec_generator_sha_start_owned second e le m br bc bs FI Result Context State RS CS RC FR FC FS) as
    (m1 & Init & Pointer1 & Counter1 & Overflow1 & IV & FR1 & FC1 & FS1 & Frame1 & R1).
  assert (Ready1:secp_sha_startup m1).
  { eapply secp_sha_startup_preserved;[exact Ready|exact R1|exact Frame1|].
    pose proof (proj1 (secp_sha_startup_separate m br 88 Ready ltac:(lia) FR)) as DR.
    pose proof (proj1 (secp_sha_startup_separate m bc 88 Ready ltac:(lia) FC)) as DC.
    pose proof (proj1 (secp_sha_startup_separate m bs 32 Ready ltac:(lia) FS)) as DS.
    intros pos;repeat split;congruence. }
  assert (FB1:Mem.range_perm m1 bb 0 32 Cur Freeable).
  { intros pos Range;apply (proj1 (proj2 Frame1));[exact VB|repeat split;congruence|apply FB;exact Range]. }
  destruct (exec_generator_sha_absorb_owned Hmodel second key e le m1 bc ba oa (Vptr bs Ptrofs.zero)
    FU Context Prefix Key ltac:(congruence) Len Hi
    (generator_sha_prefix_preserved second m m1 PrefixReady R1) Ready1 FC1 Pointer1 Counter1 Overflow1)
    as (m2 & Absorb & Pointer2 & Counter2 & Overflow2 & Buffer2 & FC2 & Frame2 & R2 & Ready2 & Prefix2).
  { intros i Index;rewrite (proj1 Frame1) by (first [exact VA|intros;repeat split;assumption]);apply Input;exact Index. }
  assert (State2:uint32_array_at m2 bs 0 sha256_iv_words).
  { intros i v Nth;rewrite (proj1 Frame2) by (first [apply (proj2 (proj2 Frame1));exact VS|intros;congruence]);apply IV;exact Nth. }
  assert (FS2:Mem.range_perm m2 bs 0 32 Cur Freeable).
  { intros pos Range;apply (proj1 (proj2 Frame2));[apply (proj2 (proj2 Frame1));exact VS|congruence|apply FS1;exact Range]. }
  destruct (eval_secp_sha_finalize48 Hmodel (generator_sha_prefix_bytes second++key) sha256_iv_words m2 bc bs
    ltac:(rewrite app_length,generator_sha_prefix_length,Len;reflexivity) eq_refl CS Ready2 FC2 FS2
    Pointer2 State2 Counter2 Overflow2 Buffer2) as
    (m3 & Finalize & Output & Pointer3 & Counter3 & Overflow3 & FC3 & FS3 & Frame3 & R3 & Ready3).
  rewrite <-app_assoc in Output.
  change (uint32_array_at m3 bs 0 (generator_sha_regs second key)) in Output.
  assert (FB3:Mem.range_perm m3 bb 0 32 Cur Freeable).
  { intros pos Range;apply (proj1 (proj2 Frame3));[apply (proj2 (proj2 Frame2)),(proj2 (proj2 Frame1));exact VB|split;congruence|].
    apply (proj1 (proj2 Frame2));[apply (proj2 (proj2 Frame1));exact VB|congruence|apply FB1;exact Range]. }
  destruct (eval_secp_sha_digest_owned (generator_sha_regs second key) m3 bb bs
    (generator_sha_regs_length second key Len) ltac:(congruence) Output FB3 FS3) as
    (mf & Digest & DigestBytes & StateF & FBF & FSF & Frame4 & R4).
  assert (Readonly:readonly_preserved m mf) by
    (eapply preserved_trans;[exact R1|];eapply preserved_trans;[exact R2|];eapply preserved_trans;[exact R3|exact R4]).
  exists mf;split.
  - unfold generator_sha_block;rewrite generator_sha_absorb_source.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Init|].
    eapply exec_statement_prefix_then_last;[exact Absorb|].
    rewrite generator_sha_final_calls_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    + eapply exec_generator_sha_finalize_call;[exact FF|exact Context|exact Finalize].
    + eapply exec_generator_sha_digest_call;[exact FD|exact Bytes|exact State|exact Digest].
  - split;[exact DigestBytes|];split;[exact StateF|];split.
    + intros pos Range;apply (proj1 (proj2 Frame4));[apply (proj2 (proj2 Frame3)),(proj2 (proj2 Frame2)),(proj2 (proj2 Frame1));exact VR|exact RB|].
      apply (proj1 (proj2 Frame3));[apply (proj2 (proj2 Frame2)),(proj2 (proj2 Frame1));exact VR|split;assumption|].
      apply (proj1 (proj2 Frame2));[apply (proj2 (proj2 Frame1));exact VR|exact RC|apply FR1;exact Range].
    + split.
      * intros pos Range;apply (proj1 (proj2 Frame4));[apply (proj2 (proj2 Frame3)),(proj2 (proj2 Frame2)),(proj2 (proj2 Frame1));exact VC|exact CB|apply FC3;exact Range].
      * split;[exact FSF|];split;[exact FBF|];split.
        -- eapply lframe_trans.
           ++ eapply lframe_implies;[exact Frame1|intros b pos [NR [NC [NS NB]]] Old;repeat split;assumption].
           ++ eapply lframe_trans.
              ** eapply lframe_implies;[exact Frame2|intros b pos [NR [NC [NS NB]]] Old;exact NC].
              ** eapply lframe_trans.
                 --- eapply lframe_implies;[exact Frame3|intros b pos [NR [NC [NS NB]]] Old;split;assumption].
                 --- eapply lframe_implies;[exact Frame4|intros b pos [NR [NC [NS NB]]] Old;exact NB].
        -- split;[exact Readonly|];split.
           ++ eapply secp_sha_startup_preserved;[exact Ready3|exact R4|exact Frame4|].
              intros pos;pose proof (proj1 (secp_sha_startup_separate m3 bb 32 Ready3 ltac:(lia) FB3));congruence.
           ++ eapply generator_sha_prefix_preserved;[|exact R4].
              eapply generator_sha_prefix_preserved;[exact Prefix2|exact R3].
Qed.

Corollary exec_generator_sha_block_bytestring (Hmodel:memcpy_model) second (key:list byte) e le m br bc bs bb ba oa :
  e!_sha256_init=None ->e!_sha256_uchars=None ->e!_sha256_finalize=None ->e!_sha256_fromMidstate=None ->
  e!(generator_sha_result_id second)=Some (br,generator_sha_ctx_type) ->
  e!(generator_sha_context_id second)=Some (bc,generator_sha_ctx_type) ->
  e!_sha256_buf=Some (bs,generator_sha_state_type) ->e!_b32=Some (bb,tarray tuchar 32) ->
  e!(generator_sha_prefix_id second)=None ->le!_key32=Some (Vptr ba oa) ->
  br<>bc ->br<>bs ->br<>bb ->bc<>bs ->bc<>bb ->bs<>bb ->ba<>br ->ba<>bc ->ba<>bs ->
  length key=32%nat ->Ptrofs.unsigned oa+32<=Ptrofs.max_unsigned ->
  secp_sha_startup m ->generator_sha_prefix_state second m ->
  Mem.range_perm m br 0 88 Cur Freeable ->Mem.range_perm m bc 0 88 Cur Freeable ->
  Mem.range_perm m bs 0 32 Cur Freeable ->Mem.range_perm m bb 0 32 Cur Freeable ->
  (forall i,(i<32)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=
    Some (Vint (nth i (map byte_int key) Int.zero))) ->
  let hash:=hash256_reg (byteStringHash (generator_sha_prefix_octets second++key)) in
  exists mf,Clight2.exec_stmt secp_ge e le m (generator_sha_block second) E0 le mf Out_normal /\
  (forall i,(i<32)%nat ->Mem.load Mint8unsigned mf bb (Z.of_nat i)=
    Some (Vint (Int.repr (nth i (secp_sha_digest_bytes hash) 0)))) /\
  uint32_array_at mf bs 0 hash /\
  Mem.range_perm mf br 0 88 Cur Freeable /\Mem.range_perm mf bc 0 88 Cur Freeable /\
  Mem.range_perm mf bs 0 32 Cur Freeable /\Mem.range_perm mf bb 0 32 Cur Freeable /\
  lframe (fun b _=>b<>br /\b<>bc /\b<>bs /\b<>bb) m mf /\readonly_preserved m mf /\
  secp_sha_startup mf /\generator_sha_prefix_state second mf.
Proof.
  intros FI FU FF FD Result Context State Bytes Prefix Key RC RS RB CS CB SB AR AC AS Len Hi Ready PrefixReady FR FC FS FB Input.
  pose proof (exec_generator_sha_block_owned Hmodel second (map byte_int key) e le m br bc bs bb ba oa
    FI FU FF FD Result Context State Bytes Prefix Key RC RS RB CS CB SB AR AC AS
    ltac:(rewrite map_length;exact Len) Hi Ready PrefixReady FR FC FS FB Input) as Run.
  rewrite generator_sha_regs_bytestring in Run by exact Len;exact Run.
Qed.
