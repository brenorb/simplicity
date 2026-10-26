(** Both actual generator SHA-start stages, including the normalized C
    struct-return destination and its By_copy assignment into the context.
    Reuse the checked initialization/copy memory proof; no libc model. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events Errors Globalenvs.
Require Import C.jet_exec C.jet_sx_mem C.jet_sha_linkage C.jet_secp_linkage
  C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_sha_tapdata_prep
  C.jet_secp_sha_pure_transport C.jet_secp_local_regions C.jet_secp_statement_prefix
  C.jet_clight_internal_preserve.
Require C.jets_sha.
Require Import C.jets_secp.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generator_sha_ctx_type := Tstruct _sha256_context noattr.
Definition generator_sha_state_type := Tstruct _sha256_midstate noattr.
Definition generator_sha_result_id (second:bool) := if second then __res else __res__1.
Definition generator_sha_context_id (second:bool) := if second then _sha256_ctx__1 else _sha256_ctx.
Definition generator_sha_start_call second := Scall None (Evar _sha256_init (type_of_function f_sha256_init))
  [Eaddrof (Evar (generator_sha_result_id second) generator_sha_ctx_type) (tptr generator_sha_ctx_type);
   Efield (Evar _sha256_buf generator_sha_state_type) _s (tarray tuint 8)].
Definition generator_sha_copy second := Sassign (Evar (generator_sha_context_id second) generator_sha_ctx_type)
  (Evar (generator_sha_result_id second) generator_sha_ctx_type).
Definition generator_sha_start (second:bool) := match nth (if second then 11%nat else 7%nat)
  (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))) Sskip with
  | Ssequence start _=>start | _=>Sskip end.
Lemma generator_sha_start_source second : generator_sha_start second=
  Ssequence (generator_sha_start_call second) (generator_sha_copy second).
Proof. destruct second;reflexivity. Qed.

Lemma generator_sha_state_members : option_map co_members ((genv_cenv secp_ge)!_sha256_midstate)=
  Some [Member_plain _s (tarray tuint 8)].
Proof. vm_compute;reflexivity. Qed.
Lemma generator_sha_state_layout : exists co,(genv_cenv secp_ge)!_sha256_midstate=Some co /\
  field_offset secp_ge _s (co_members co)=OK (0,Full).
Proof.
  pose proof generator_sha_state_members as Members.
  destruct ((genv_cenv secp_ge)!_sha256_midstate) as [co|] eqn:Cenv;[|discriminate].
  exists co;split;[reflexivity|].
  inversion Members as [Fields];rewrite Fields;reflexivity.
Qed.
Local Opaque secp_ge sha_ge.
Lemma eval_generator_sha_state e le m bs : e!_sha256_buf=Some (bs,generator_sha_state_type) ->
  eval_expr secp_ge e le m (Efield (Evar _sha256_buf generator_sha_state_type) _s (tarray tuint 8))
    (Vptr bs Ptrofs.zero).
Proof.
  intro State;destruct generator_sha_state_layout as (co & Cenv & Offset).
  eapply eval_Elvalue with (loc:=bs) (ofs:=Ptrofs.zero) (bf:=Full).
  - rewrite <-(Ptrofs.add_zero_l Ptrofs.zero);eapply eval_Efield_struct with (co:=co) (delta:=0).
    + eapply eval_Elvalue;[apply eval_Evar_local;exact State|apply deref_loc_copy;reflexivity].
    + reflexivity.
    + exact Cenv.
    + exact Offset.
  - apply deref_loc_reference;reflexivity.
Qed.

Theorem exec_generator_sha_start_owned second e le m br bc bs :
  e!_sha256_init=None -> e!(generator_sha_result_id second)=Some (br,generator_sha_ctx_type) ->
  e!(generator_sha_context_id second)=Some (bc,generator_sha_ctx_type) ->
  e!_sha256_buf=Some (bs,generator_sha_state_type) ->
  br<>bs -> bc<>bs -> br<>bc ->
  Mem.range_perm m br 0 88 Cur Freeable -> Mem.range_perm m bc 0 88 Cur Freeable ->
  Mem.range_perm m bs 0 32 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge e le m (generator_sha_start second) E0 le mf Out_normal /\
  Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
  Mem.load Mint64 mf bc 8=Some (Vlong Int64.zero) /\
  Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
  uint32_array_at mf bs 0 sha256_iv_words /\
  Mem.range_perm mf br 0 88 Cur Freeable /\ Mem.range_perm mf bc 0 88 Cur Freeable /\
  Mem.range_perm mf bs 0 32 Cur Freeable /\
  lframe (fun b _=>b<>br /\ b<>bc /\ b<>bs) m mf /\ readonly_preserved m mf.
Proof.
  intros Fun Result Context State RS CS RC FR FC FS.
  destruct (sha_init_copy m br bc bs 0 RS CS RC ltac:(lia)
    ltac:(change (32<=18446744073709551615);lia) ltac:(exists 0;reflexivity)
    (freeable_range_writable _ _ _ _ FR) (freeable_range_writable _ _ _ _ FC)
    (freeable_range_writable _ _ _ _ FS))
    as (mi & mf & bytes & Init & Load & Store & Pointer & Counter & Overflow & IV & Loads & Perm & Valid).
  pose proof (secp_sha_transport_call sha_ge jets_sha._sha256_init jets_sha.f_sha256_init m
    [Vptr br Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mi Vundef
    (or_intror eq_refl) ltac:(right;left;reflexivity) Init) as Call.
  assert (Body:Clight2.exec_stmt secp_ge e le m (generator_sha_start second) E0 le mf Out_normal).
  { rewrite generator_sha_start_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=le).
    - unfold generator_sha_start_call.
      destruct (secp_sha_helpers_entries sha_ge (or_intror eq_refl) jets_sha._sha256_init jets_sha.f_sha256_init
        ltac:(right;left;reflexivity)) as (b1 & b2 & S1 & F1 & S2 & F2).
      eapply exec_Scall with (vf:=Vptr b2 Ptrofs.zero) (f:=Internal jets_sha.f_sha256_init)
        (vargs:=[Vptr br Ptrofs.zero;Vptr bs Ptrofs.zero]) (vres:=Vundef).
      + reflexivity.
      + eapply eval_Elvalue;[eapply eval_Evar_global;[exact Fun|exact S2]|apply deref_loc_reference;reflexivity].
      + eapply eval_Econs.
        * apply eval_Eaddrof;apply eval_Evar_local;exact Result.
        * reflexivity.
        * eapply eval_Econs;[apply eval_generator_sha_state;exact State|reflexivity|constructor].
      + exact F2.
      + reflexivity.
      + exact Call.
    - unfold generator_sha_copy;eapply exec_Sassign_copy with (b:=bc) (b':=br)
        (ofs:=Ptrofs.zero) (ofs':=Ptrofs.zero) (v:=Vptr br Ptrofs.zero).
      + apply eval_Evar_local;exact Context.
      + eapply eval_Elvalue;[apply eval_Evar_local;exact Result|apply deref_loc_copy;reflexivity].
      + reflexivity.
      + eapply assign_loc_copy with (b':=br) (ofs':=Ptrofs.zero) (bytes:=bytes).
        * reflexivity.
        * intros _;exists 0;reflexivity.
        * intros _;exists 0;reflexivity.
        * left;congruence.
        * exact Load.
        * exact Store. }
  exists mf;split;[exact Body|];split;[exact Pointer|];split;[exact Counter|];split;[exact Overflow|];
    split;[exact IV|];split;[intros pos Range;apply Perm,FR;exact Range|];
    split;[intros pos Range;apply Perm,FC;exact Range|];
    split;[intros pos Range;apply Perm,FS;exact Range|];split.
  - split.
    + intros chunk b ofs Old Outside.
      pose proof (Outside ofs ltac:(pose proof (size_chunk_pos chunk);lia)) as (NR & NC & NS).
      apply Loads;[exact Old|exact NR|exact NC|left;exact NS].
    + split;[intros;apply Perm;assumption|exact Valid].
  - eapply preserved_trans.
    + eapply secp_sha_pure_preserved;[right;left;reflexivity|exact Call].
    + eapply storebytes_preserved;exact Store.
Qed.
