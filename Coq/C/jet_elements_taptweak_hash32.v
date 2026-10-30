(** Original sha256_hash wrapper for TapTweak's empty/half-full context states. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require sha.SHA256.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_sx_exec C.jet_sx_mem C.jet_memcpy_model C.jet_uint32_array_init C.jet_sha_ctx8_model
 C.jet_sha_hash_exec C.jet_sha_be32_write C.jet_secp_generator_sha_start C.jet_secp_schnorr_challenge_body C.jet_secp_sha_owned C.jet_secp_sha_append32 C.jet_secp_sha_startup
 C.jet_secp_curve_frame C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_sha_hash32 C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_globals C.jet_elements_taptweak_parse_start C.jet_xonly_parse_control_at
 C.jet_transport.
Require Import C.jet_elements_taptweak_append32.
From compcert Require Import Globalenvs.
Definition elements_taptweak_hash32_helpers:=
 [(_sha256_fromMidstate,f_sha256_fromMidstate);(_sha256_uchars,f_sha256_uchars)].
Lemma elements_taptweak_hash32_lookup:
 map(secp_helper_lookup elements_taptweak_ge)elements_taptweak_hash32_helpers=
 map(fun it=>Some(Internal(snd it)))elements_taptweak_hash32_helpers.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_hash_midstate_checked:
 expr_okb secp_ge elements_taptweak_ge
 (Efield (Ederef (Etempvar _h (tptr (Tstruct _sha256_midstate noattr)))
 (Tstruct _sha256_midstate noattr)) _s (tarray tuint 8))=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge.
Lemma eval_elements_taptweak_hash_midstate e le m bt:le!_h=Some (Vptr bt Ptrofs.zero) ->
 eval_expr elements_taptweak_ge e le m
 (Efield (Ederef (Etempvar _h (tptr (Tstruct _sha256_midstate noattr)))
 (Tstruct _sha256_midstate noattr)) _s (tarray tuint 8)) (Vptr bt Ptrofs.zero).
Proof.
 intro H;apply(proj1(eval_expr_transport secp_ge elements_taptweak_ge e le m));
 [apply eval_secp_hash_midstate;exact H|exact elements_taptweak_hash_midstate_checked].
Qed.
Lemma exec_elements_taptweak_hash32_call id fd args vargs v e le m mf:
 In(id,fd)elements_taptweak_hash32_helpers ->e!id=None ->
 eval_exprlist elements_taptweak_ge e le m args (type_of_params(fn_params fd)) vargs ->
 Clight2.eval_funcall elements_taptweak_ge m(Internal fd)vargs E0 mf v ->
 Clight2.exec_stmt elements_taptweak_ge e le m(curve_call id fd None args)E0 le mf Out_normal.
Proof.
 intros Member Global Args Call.
 destruct(secp_helper_lookup_exists elements_taptweak_ge id fd
 (secp_map_eq_in _ _ _ elements_taptweak_hash32_lookup (id,fd) Member))as(bf & Sym & Funct).
 eapply exec_elements_taptweak_curve_call with(result:=None)(bf:=bf)(v:=v);[exact Sym| |exact Global|exact Args|exact Call].
 unfold Genv.find_funct;rewrite pred_dec_true by reflexivity;exact Funct.
Qed.
Theorem eval_elements_taptweak_sha_hash32 (Copy:memcpy_model) l regs regsH total m bc bs bt:
 (length l=0%nat \/length l=32%nat) ->length regs=8%nat ->length regsH=8%nat ->
 0<=total ->total+32<2305843009213693952 ->total mod 64=Z.of_nat (length l) ->
 NoDup [bc;bs;bt] ->elements_taptweak_sha_startup m ->
 Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->Mem.range_perm m bt 0 32 Cur Freeable ->
 uint32_array_at m bt 0 regsH ->Mem.load Mptr m bc 0=Some (Vptr bs Ptrofs.zero) ->
 uint32_array_at m bs 0 regs ->Mem.load Mint64 m bc 8=Some (Vlong (Int64.repr total)) ->Mem.load Mint8unsigned m bc 80=Some (Vint Int.zero) ->
 (forall i,(i<length l)%nat ->Mem.load Mint8unsigned m bc (16+Z.of_nat i)=Some (Vint (nth i l Int.zero))) ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_sha256_hash) [Vptr bc Ptrofs.zero;Vptr bt Ptrofs.zero] E0 mf Vundef /\
 uint32_array_at mf bs 0 (sha_append32_regs l regs (secp_hash_bytes regsH)) /\
 Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc 8=Some (Vlong (Int64.repr (total+32))) /\Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
 (forall i,(i<length (sha_append32_buffer l (secp_hash_bytes regsH)))%nat ->Mem.load Mint8unsigned mf bc (16+Z.of_nat i)=
  Some (Vint (nth i (sha_append32_buffer l (secp_hash_bytes regsH)) Int.zero))) /\
 Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\Mem.range_perm mf bt 0 32 Cur Freeable /\
 uint32_array_at mf bt 0 regsH /\lframe (fun b _=>b<>bc /\b<>bs) m mf /\readonly_preserved m mf /\elements_taptweak_sha_startup mf.
Proof.
 intros Used LR LH Nonnegative Bound Remainder Sep Startup FC FS FT InputH Pointer State Counter Overflow Buffer.
 assert (CS:bc<>bs) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence).
 assert (CT:bc<>bt) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence).
 assert (ST:bs<>bt) by (clear -Sep;repeat rewrite NoDup_cons_iff in Sep;cbn [In] in *;intuition congruence).
 assert (VC:Mem.valid_block m bc) by (eapply Mem.perm_valid_block;apply (FC 0);clear;lia).
 assert (VS:Mem.valid_block m bs) by (eapply Mem.perm_valid_block;apply (FS 0);clear;lia).
 assert (VT:Mem.valid_block m bt) by (eapply Mem.perm_valid_block;apply (FT 0);clear;lia).
 destruct (Mem.alloc m 0 32) as (mi,bb) eqn:Alloc.
 pose (e:=hash_env bb);pose (le:=hash_temps bc 0 bt Ptrofs.zero).
 assert (Entry:function_entry2 elements_taptweak_ge f_sha256_hash [Vptr bc Ptrofs.zero;Vptr bt Ptrofs.zero] m e le mi).
 { assert (OK:fn_okb f_sha256_hash=true) by reflexivity.
   destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
   eapply alloc_variables_cons;[exact Alloc|constructor]. }
 assert (Fresh:forall b,Mem.valid_block m b ->b<>bb).
 { intros b Valid Same;subst b;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid). }
 assert (CB:bc<>bb) by (apply Fresh;exact VC).
 assert (SB:bs<>bb) by (apply Fresh;exact VS).
 assert (TB:bt<>bb) by (apply Fresh;exact VT).
 assert (FB:Mem.range_perm mi bb 0 32 Cur Freeable) by (intros pos Range;eapply Mem.perm_alloc_2;[exact Alloc|exact Range]).
 assert (KeepI:keeps_permissions m mi) by (eapply entry_keeps_permissions;exact Entry).
 assert (FrameI:lframe (fun _ _=>True) m mi) by (apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc).
 assert (ReadI:readonly_preserved m mi) by (eapply entry_preserved;exact Entry).
 assert (FTI:Mem.range_perm mi bt 0 32 Cur Freeable) by (intros pos Range;apply KeepI,FT;exact Range).
 assert (InputI:uint32_array_at mi bt 0 regsH).
 { intros i v Nth;rewrite (proj1 FrameI Mint32 bt (0+4*Z.of_nat i) VT);[apply InputH;exact Nth|intros;exact I]. }
 destruct (eval_elements_taptweak_sha_digest_owned regsH mi bb bt LH ltac:(clear -TB;congruence) InputI FB FTI)
 as (md & Digest & Bytes & SourceD & FBD & FTD & FrameD & ReadD).
 assert (ReadID:readonly_preserved m md) by (eapply preserved_trans;[exact ReadI|exact ReadD]).
 assert (FrameID:lframe (fun _ _=>True) m md).
 { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b).
   - eapply lframe_trans;[eapply lframe_implies;[exact FrameI|intros;exact I]|].
     eapply lframe_implies;[exact FrameD|intros b pos Old Valid;apply Fresh;exact Old].
   - intros b pos _ Old;exact Old. }
 assert (FCD:Mem.range_perm md bc 0 88 Cur Freeable) by (eapply curve_keep_free;[clear;lia|exact FC|exact FrameID|intros;exact I]).
 assert (FSD:Mem.range_perm md bs 0 32 Cur Freeable) by (eapply curve_keep_free;[clear;lia|exact FS|exact FrameID|intros;exact I]).
 assert (StateD:uint32_array_at md bs 0 regs).
 { intros i v Nth;rewrite (proj1 FrameID Mint32 bs (0+4*Z.of_nat i) VS);[apply State;exact Nth|intros;exact I]. }
 assert (PointerD:Mem.load Mptr md bc 0=Some (Vptr bs Ptrofs.zero)).
 { rewrite (proj1 FrameID Mptr bc 0 VC);[exact Pointer|intros;exact I]. }
 assert (CounterD:Mem.load Mint64 md bc 8=Some (Vlong (Int64.repr total))).
 { rewrite (proj1 FrameID Mint64 bc 8 VC);[exact Counter|intros;exact I]. }
 assert (OverflowD:Mem.load Mint8unsigned md bc 80=Some (Vint Int.zero)).
 { rewrite (proj1 FrameID Mint8unsigned bc 80 VC);[exact Overflow|intros;exact I]. }
 assert (BufferD:forall i,(i<length l)%nat ->Mem.load Mint8unsigned md bc (16+Z.of_nat i)=Some (Vint (nth i l Int.zero))).
 { intros i Index;rewrite (proj1 FrameID Mint8unsigned bc (16+Z.of_nat i) VC);[apply Buffer;exact Index|intros;exact I]. }
 assert (SourceBytes:forall i,(i<length (secp_hash_bytes regsH))%nat ->Mem.load Mint8unsigned md bb (Z.of_nat i)=
  Some (Vint (nth i (secp_hash_bytes regsH) Int.zero))).
 { intros i Index;unfold secp_hash_bytes;change Int.zero with (Int.repr 0);rewrite map_nth;apply Bytes.
   rewrite (secp_hash_bytes_length regsH LH) in Index;exact Index. }
 assert (StartD:elements_taptweak_sha_startup md).
 { eapply elements_taptweak_sha_startup_preserved;[exact Startup|exact ReadID|exact FrameID|intros;exact I]. }
 destruct (eval_elements_taptweak_sha_append32 Copy l (secp_hash_bytes regsH) regs total md bc bs bb Used
  (secp_hash_bytes_length regsH LH) LR Nonnegative Bound Remainder CS CB StartD FCD FSD PointerD StateD CounterD OverflowD BufferD SourceBytes)
 as (ma & Absorb & StateA & PointerA & CounterA & OverflowA & BufferA & FCA & FSA & FrameA & ReadA & StartA).
 assert (DigestStmt:Clight2.exec_stmt elements_taptweak_ge e le mi secp_hash_from E0 le md Out_normal).
 { unfold secp_hash_from;eapply exec_elements_taptweak_hash32_call with (vargs:=[Vptr bb Ptrofs.zero;Vptr bt Ptrofs.zero]) (v:=Vundef).
   - unfold elements_taptweak_hash32_helpers;repeat first [left;reflexivity|right].
   - reflexivity.
   - eapply eval_Econs;[eapply eval_Elvalue;[apply eval_Evar_local;reflexivity|apply deref_loc_reference;reflexivity]|reflexivity|].
     eapply eval_Econs;[apply eval_elements_taptweak_hash_midstate;reflexivity|reflexivity|constructor].
   - exact Digest. }
 assert (AbsorbStmt:Clight2.exec_stmt elements_taptweak_ge e le md secp_hash_absorb E0 le ma Out_normal).
 { unfold secp_hash_absorb;eapply exec_elements_taptweak_hash32_call with
   (vargs:=[Vptr bc Ptrofs.zero;Vptr bb Ptrofs.zero;Vlong (Int64.repr 32)]) (v:=Vint Int.one).
   - unfold elements_taptweak_hash32_helpers;repeat first [left;reflexivity|right].
   - reflexivity.
   - eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|].
     eapply eval_Econs;[eapply eval_Elvalue;[apply eval_Evar_local;reflexivity|apply deref_loc_reference;reflexivity]|reflexivity|].
     eapply eval_Econs;[apply eval_Esizeof|reflexivity|constructor].
   - exact Absorb. }
 assert (FBA:Mem.range_perm ma bb 0 32 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FBD|exact FrameA|intros;split;[clear -CB;congruence|clear -SB;congruence]]. }
 destruct (Mem.range_perm_free ma bb 0 32 FBA) as (mf & Frees).
 assert (FrameF:lframe (fun b _=>b<>bb) ma mf) by (apply lframe_unchanged;eapply Mem.free_unchanged_on;[exact Frees|intros;congruence]).
 assert (ReadF:readonly_preserved ma mf) by (eapply free_preserved;exact Frees).
 assert (Frame:lframe (fun b _=>b<>bc /\b<>bs) m mf).
 { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\b<>bc /\b<>bs).
   - eapply lframe_trans;[eapply lframe_implies;[exact FrameID|intros;exact I]|].
     eapply lframe_trans;
      [eapply lframe_implies;[exact FrameA|intros b pos [Old Outside] Valid;exact Outside]|
       eapply lframe_implies;[exact FrameF|intros b pos [Old Outside] Valid;apply Fresh;exact Old]].
   - intros b pos Outside Old;split;assumption. }
 assert (Read:readonly_preserved m mf).
 { eapply preserved_trans;[exact ReadID|];eapply preserved_trans;[exact ReadA|exact ReadF]. }
 assert (VA:Mem.valid_block ma bc) by (eapply Mem.perm_valid_block;apply (FCA 0);clear;lia).
 assert (VSA:Mem.valid_block ma bs) by (eapply Mem.perm_valid_block;apply (FSA 0);clear;lia).
 exists mf;split.
 - eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=le) (m1:=mi) (m2:=ma) (out:=Out_normal).
   + exact Entry.
   + rewrite secp_hash_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact DigestStmt|exact AbsorbStmt].
   + reflexivity.
   + change (Mem.free_list ma [(bb,0,32)]=Some mf);cbn [Mem.free_list];rewrite Frees;reflexivity.
 - split.
   + intros i v Nth;rewrite (proj1 FrameF Mint32 bs (0+4*Z.of_nat i) VSA);[apply StateA;exact Nth|intros;exact SB].
   + split.
     * rewrite (proj1 FrameF Mptr bc 0 VA);[exact PointerA|intros;exact CB].
     * split.
       -- rewrite (proj1 FrameF Mint64 bc 8 VA);[exact CounterA|intros;exact CB].
       -- split.
          ++ rewrite (proj1 FrameF Mint8unsigned bc 80 VA);[exact OverflowA|intros;exact CB].
          ++ split.
             ** intros i Index;rewrite (proj1 FrameF Mint8unsigned bc (16+Z.of_nat i) VA);[apply BufferA;exact Index|intros;exact CB].
             ** split.
                --- eapply curve_keep_free;[clear;lia|exact FCA|exact FrameF|intros;exact CB].
                --- split.
                    +++ eapply curve_keep_free;[clear;lia|exact FSA|exact FrameF|intros;exact SB].
                    +++ split.
                        *** eapply curve_keep_free;[clear;lia|exact FT|exact Frame|intros;split;[clear -CT;congruence|clear -ST;congruence]].
                        *** split.
                            ---- intros i v Nth;rewrite (proj1 Frame Mint32 bt (0+4*Z.of_nat i) VT);
                                 [apply InputH;exact Nth|intros;split;[clear -CT;congruence|clear -ST;congruence]].
                            ---- split;[exact Frame|];split;[exact Read|].
                                 eapply elements_taptweak_sha_startup_preserved;[exact Startup|exact Read|exact Frame|].
                                 pose proof (proj1 (elements_taptweak_sha_startup_separate m bc 88 Startup ltac:(clear;lia) FC)) as DC.
                                 pose proof (proj1 (elements_taptweak_sha_startup_separate m bs 32 Startup ltac:(clear;lia) FS)) as DS.
                                 intros;split;[clear -DC;congruence|clear -DS;congruence].
Qed.
