(** Both original public normalization branches after the actual reader/tag. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.extraMath C.jet_exec C.jet_readBit_layout C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_frame_inv
 C.jet_output_layout C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_curve_frame C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge C.jet_secp_square_spec_bridge
 C.jet_secp_canonical_zero C.jet_secp_gej_norm_branch C.jet_secp_gej_norm_literal
 C.jet_secp_gej_predicate_body C.jet_secp_affine_skip C.jet_secp_affine_inverse_literal
 C.jet_secp_modinfo_fe_caller C.jet_secp_fe_inverse_state C.jet_secp_gej_norm_preserve
 C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma gej_norm_right_encoding (p:Ty.tySem(Ty.Prod Word256 Word256)) :
 @Simplicity.Translate.encode(Ty.Sum Ty.Unit(Ty.Prod Word256 Word256))(inr p)=
 [Some true]++Simplicity.Translate.encode p.
Proof. reflexivity. Qed.
Lemma gej_norm_payload_link : Genv.find_symbol secp_ge _write_ge=Some(secp_symbol_block _write_ge) /\
 Genv.find_funct secp_ge(Vptr(secp_symbol_block _write_ge)Ptrofs.zero)=Some(Internal f_write_ge).
Proof. split;reflexivity. Qed.
Local Opaque secp_ge canonical_fe_is_zero literal_gej_norm literal_gej_normalize Simplicity.Translate.encode.

Lemma exec_gej_norm_payload_calls le m mr mf bl bp br bd base :
 le!_dst=Some(Vptr bd(Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge m(Internal f_secp256k1_ge_set_gej_var)
  [Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero]E0 mr Vundef ->
 Clight2.eval_funcall secp_ge mr(Internal f_write_ge)
  [Vptr bd(Ptrofs.repr base);Vptr br Ptrofs.zero]E0 mf Vundef ->
 Clight2.exec_stmt secp_ge(gej_norm_env bl bp br)le m
  (Ssequence gej_norm_affine_stmt gej_norm_payload_stmt)E0 le mf Out_normal.
Proof.
 intros Dst Affine Write;eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mr)(le1:=le).
 - change(Clight2.exec_stmt secp_ge(gej_norm_env bl bp br)le m
    (curve_call _secp256k1_ge_set_gej_var f_secp256k1_ge_set_gej_var None
     [Eaddrof(Evar _r(Tstruct __6121 noattr))(tptr(Tstruct __6121 noattr));
      Eaddrof(Evar _a(Tstruct __6123 noattr))(tptr(Tstruct __6123 noattr))])E0 le mr Out_normal).
   eapply exec_curve_call with(vargs:=[Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero])(v:=Vundef).
   + unfold secp_pure;repeat(first[left;reflexivity|right]).
   + reflexivity.
   + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
   + exact Affine.
 - unfold gej_norm_payload_stmt.
   eapply exec_Scall with(vf:=Vptr(secp_symbol_block _write_ge)Ptrofs.zero)
    (f:=Internal f_write_ge)(vargs:=[Vptr bd(Ptrofs.repr base);Vptr br Ptrofs.zero])(vres:=Vundef).
   + reflexivity.
   + eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact(proj1 gej_norm_payload_link)]|apply deref_loc_reference;reflexivity].
   + eapply eval_Econs;[apply eval_Etempvar;exact Dst|reflexivity|].
     eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
   + exact(proj2 gej_norm_payload_link).
   + reflexivity.
   + exact Write.
Qed.

Lemma exec_gej_norm_skip_call le m mf bl bp br bd base :
 le!_dst=Some(Vptr bd(Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge m(Internal f_skip_ge)[Vptr bd(Ptrofs.repr base)]E0 mf Vundef ->
 Clight2.exec_stmt secp_ge(gej_norm_env bl bp br)le m gej_norm_skip_stmt E0 le mf Out_normal.
Proof.
 intros Dst Skip;unfold gej_norm_skip_stmt.
 eapply exec_Scall with(vf:=Vptr(secp_symbol_block _skip_ge)Ptrofs.zero)
  (f:=Internal f_skip_ge)(vargs:=[Vptr bd(Ptrofs.repr base)])(vres:=Vundef).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact(proj1 gej_norm_skip_link)]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs;[apply eval_Etempvar;exact Dst|reflexivity|constructor].
 - exact(proj2 gej_norm_skip_link).
 - reflexivity.
 - exact Skip.
Qed.

Theorem exec_gej_norm_branch_initialized le m0 bd base bw edge cursor N bi m bl bp br
 (x y z:Ty.tySem Word256) :
 (forall mc w,Int64.unsigned w<>0 ->
   Clight2.eval_funcall secp_ge mc(Internal f_secp256k1_ctz64_var)[Vlong w]
    E0 mc(Vint(Int.repr(Z_ctz(Int64.unsigned w))))) ->
 le!_dst=Some(Vptr bd(Ptrofs.repr base)) -> write_frame_at m0 bd base bw edge cursor N -> 513<=N ->
 finv m0 bd base bw edge cursor N bi m true [Some(negb(Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)))] ->
 fe_at m bp 0(words5(square_reader_rho x)) -> fe_at m bp 40(words5(square_reader_rho y)) ->
 fe_at m bp 80(words5(square_reader_rho z)) ->
 Mem.load Mint32 m bp 120=Some(Vint(bit_int(Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)))) ->
 modinfo_fe_state m -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bl 0 16 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable ->
 bp<>bl -> br<>bp -> br<>bl -> xsep(extA m0 bd bw bi)[(bp,0);(br,0);(bl,0)] ->
 exists mf,
 Clight2.exec_stmt secp_ge(gej_norm_env bl bp br)
  (gej_norm_tagged le(Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)))m gej_norm_branch E0
  (gej_norm_tagged le(Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)))mf Out_normal /\
 finv m0 bd base bw edge cursor N bi mf true
  (Simplicity.Translate.encode(@literal_gej_normalize Alg.CoreFunSem ((x,y),z))) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bl 0 16 Cur Freeable /\
 Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe(fun b _=>b<>bp /\ b<>br /\ b<>bl /\ ~extA m0 bd bw bi b)m mf /\
 modinfo_fe_state mf /\ readonly_preserved m mf.
Proof.
 intros CountCall Dst Output Cap Prefix X Y Z Flag Ready FP FL FR PL RP RL Sep.
 assert(TaggedDst:forall flag,(gej_norm_tagged le flag)!_dst=Some(Vptr bd(Ptrofs.repr base))).
 { intro flag;unfold gej_norm_tagged;rewrite !PTree.gso by discriminate;exact Dst. }
 rewrite literal_gej_normalize_value.
 destruct(Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)) eqn:Zero;cbn [negb bit_int] in Prefix,Flag |- *.
 - destruct(eval_secp_skip_ge_from_prefix m0 bd base bw edge cursor N bi true [Some false]m
    Output ltac:(cbn;lia) Prefix) as(mf & Skip & Final & SkipFrame).
   pose proof(secp_skip_ge_preserved _ _ _ _ _ Skip) as Preserved.
   assert(NotD:bp<>bd /\ br<>bd /\ bl<>bd).
   { pose proof(fext_bd m0 bd base bw edge cursor N bi Output) as D;
     repeat split;intro Same;subst;[exact(Sep 0%nat ltac:(cbn;lia)D)|
      exact(Sep 1%nat ltac:(cbn;lia)D)|exact(Sep 2%nat ltac:(cbn;lia)D)]. }
   destruct NotD as(PD & RD & LD).
   exists mf;split.
   + unfold gej_norm_branch;eapply exec_Sifthenelse with(v1:=Vint Int.zero)(b:=false).
     * apply eval_Etempvar;unfold gej_norm_tagged;apply PTree.gss.
     * reflexivity.
     * apply(exec_gej_norm_skip_call(gej_norm_tagged le true)m mf bl bp br bd base);[apply TaggedDst|exact Skip].
   + split;[exact Final|];split.
     * eapply curve_keep_free;[lia|exact FP|exact SkipFrame|intros;exact PD].
     * split;[eapply curve_keep_free;[lia|exact FL|exact SkipFrame|intros;exact LD]|];split.
       -- eapply curve_keep_free;[lia|exact FR|exact SkipFrame|intros;exact RD].
       -- split.
          ++ eapply lframe_implies;[exact SkipFrame|];intros b pos(NP & NR & NL & Ext)V.
             intro Same;subst b;apply Ext;apply(fext_bd m0 bd base bw edge cursor N bi Output).
          ++ split;[exact(proj1(modinfo_fe_state_preserved m mf Ready Preserved))|exact Preserved].
 - assert(Sep2:xsep(extA m0 bd bw bi)[(bp,0);(br,0)]).
   { intros [|[|r]] Bound;[exact(Sep 0%nat ltac:(cbn;lia))|exact(Sep 1%nat ltac:(cbn;lia))|cbn in Bound;lia]. }
   destruct(eval_affine_finite_write_literal m0 bd base bw edge cursor N bi 0 m bp br x y z
    CountCall Output Cap Prefix Sep2 ltac:(congruence) X Y Z Flag Ready FP FR)
    as(mr & mf & Affine & Write & Final & FPF & FRF & Frame & ReadyF & Preserved).
   assert(FLF:Mem.range_perm mf bl 0 16 Cur Freeable).
   { eapply curve_keep_free;[lia|exact FL|exact Frame|];intros;split;[congruence|];split;[congruence|exact(Sep 2%nat ltac:(cbn;lia))]. }
   exists mf;split.
   + unfold gej_norm_branch;eapply exec_Sifthenelse with(v1:=Vint Int.one)(b:=true).
     * apply eval_Etempvar;unfold gej_norm_tagged;apply PTree.gss.
     * reflexivity.
     * apply(exec_gej_norm_payload_calls(gej_norm_tagged le false)m mr mf bl bp br bd base);
       [apply TaggedDst|exact Affine|exact Write].
   + rewrite gej_norm_right_encoding;split;[exact Final|];split;[exact FPF|];split;[exact FLF|];split;[exact FRF|];split.
     * eapply lframe_implies;[exact Frame|];intros b pos(NP & NR & NL & NE) Valid;split;[exact NP|];split;assumption.
     * split;assumption.
Qed.

Lemma exec_gej_norm_after_copy le m mt mf bl bp br infinity :
 Clight2.exec_stmt secp_ge(gej_norm_env bl bp br)le m
  (Ssequence gej_predicate_read_stmt gej_norm_header)E0(gej_norm_tagged le infinity)mt Out_normal ->
 Clight2.exec_stmt secp_ge(gej_norm_env bl bp br)(gej_norm_tagged le infinity)mt gej_norm_branch
  E0(gej_norm_tagged le infinity)mf Out_normal ->
 Clight2.exec_stmt secp_ge(gej_norm_env bl bp br)le m
  (Ssequence gej_predicate_read_stmt gej_norm_after_read)E0(gej_norm_tagged le infinity)mf
  (Out_return(Some(Vint Int.one,tint))).
Proof.
 intros Prefix Branch;inversion Prefix;subst;[|contradiction].
 match goal with
 | H:E0=?t1 ** ?t2 |- _=>destruct(Eapp_E0_inv t1 t2(eq_sym H)) as[-> ->]
 | H:?t1 ** ?t2=E0 |- _=>destruct(Eapp_E0_inv t1 t2 H) as[-> ->]
 end.
 eapply exec_Sseq_1 with(t1:=E0)(t2:=E0);[eassumption|].
 unfold gej_norm_after_read;eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mf)(le1:=gej_norm_tagged le infinity).
 - eapply exec_Sseq_1 with(t1:=E0)(t2:=E0);eassumption.
 - apply exec_Sreturn_some;constructor.
Qed.
