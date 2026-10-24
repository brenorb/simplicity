(** Both original parity branches, from actual represented reader fields. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.extraMath C.jet_readBit_layout C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame C.jet_frame_inv
 C.jet_output_layout C.jet_secp_linkage C.jets_secp C.jet_secp_curve_frame C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_square_spec_bridge C.jet_secp_canonical_zero
 C.jet_secp_gej_odd_entry C.jet_secp_gej_odd_body C.jet_secp_gej_odd_literal C.jet_secp_gej_odd_finite_calls
 C.jet_secp_bit_writer C.jet_secp_frame_preserve C.jet_secp_modinfo_fe_caller
 C.jet_secp_fe_inverse_state C.jet_clight_internal_preserve.
Require C.jets.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_is_zero literal_gej_y_is_odd Simplicity.Translate.encode.

Theorem exec_gej_odd_rest_initialized le m0 bd base bw edge cursor N bi m bl bp br
 (x y z:Ty.tySem Word256) :
 (forall mc w,Int64.unsigned w<>0 ->
   Clight2.eval_funcall secp_ge mc(Internal f_secp256k1_ctz64_var)[Vlong w]
    E0 mc(Vint(Int.repr(Z_ctz(Int64.unsigned w))))) ->
 le!_dst=Some(Vptr bd(Ptrofs.repr base)) -> write_frame_at m0 bd base bw edge cursor N -> 1<=N ->
 finv m0 bd base bw edge cursor N bi m false [] ->
 fe_at m bp 0(words5(square_reader_rho x)) -> fe_at m bp 40(words5(square_reader_rho y)) ->
 fe_at m bp 80(words5(square_reader_rho z)) ->
 Mem.load Mint32 m bp 120=Some(Vint(bit_int(Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)))) ->
 modinfo_fe_state m -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bl 0 16 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable ->
 bp<>bl -> br<>bp -> br<>bl -> xsep(extA m0 bd bw bi)[(bp,0);(br,0);(bl,0)] ->
 exists lef mf,
 Clight2.exec_stmt secp_ge(gej_odd_env bl bp br)le m gej_odd_after_read E0 lef mf
  (Out_return(Some(Vint Int.one,tint))) /\
 finv m0 bd base bw edge cursor N bi mf true
  (Simplicity.Translate.encode(@literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z))) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bl 0 16 Cur Freeable /\
 Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe(fun b _=>b<>bp /\ b<>br /\ b<>bl /\ ~extA m0 bd bw bi b)m mf /\
 modinfo_fe_state mf /\ readonly_preserved m mf.
Proof.
 intros CountCall Dst Output Cap Prefix X Y Z Flag Ready FP FL FR PL RP RL Sep.
 pose proof(exec_gej_odd_flag le m bl bp br(Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z))Flag) as FlagRun.
 assert(FlaggedDst:forall bit,(gej_odd_flagged le bit)!_dst=Some(Vptr bd(Ptrofs.repr base))).
 { intro bit;unfold gej_odd_flagged;rewrite PTree.gso by discriminate;exact Dst. }
 destruct(Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)) eqn:Zero;cbn [bit_int] in Flag |- *.
 - destruct(eval_secp_writeBit_from_invariant m0 bd base bw edge cursor N bi m false Output Cap Prefix)
    as(mf & Write & Final & WriteFrame & Perms).
   pose proof(secp_writeBit_preserved _ _ _ _ _ Write) as Preserved.
   exists(gej_odd_flagged le true),mf;split.
   + unfold gej_odd_after_read;eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mf)(le1:=gej_odd_flagged le true).
     * eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=m)(le1:=gej_odd_flagged le true);[exact FlagRun|].
       unfold gej_odd_branch;eapply exec_Sifthenelse with(v1:=Vint Int.one)(b:=true).
       -- apply eval_Etempvar;unfold gej_odd_flagged;apply PTree.gss.
       -- reflexivity.
       -- apply(exec_gej_odd_write(gej_odd_flagged le true)m mf bl bp br bd base(Econst_int Int.zero tint)false);
          [apply FlaggedDst|reflexivity|constructor|exact Write].
     * apply exec_Sreturn_some;constructor.
   + split.
     * rewrite literal_gej_y_is_odd_encoded,literal_gej_y_is_odd_infinity by exact Zero;exact Final.
     * split;[intros pos Range;apply Perms,FP;exact Range|];split;
        [intros pos Range;apply Perms,FL;exact Range|];split;
        [intros pos Range;apply Perms,FR;exact Range|];split.
       -- eapply lframe_implies;[exact WriteFrame|];intros b pos(NP & NR & NL & NE)Valid;
          split;intro Same;subst b;apply NE.
          ++ apply(fext_bd m0 bd base bw edge cursor N bi Output).
          ++ split;[right;left;reflexivity|];eapply bw_valid;[exact Output|lia].
       -- split;[exact(proj1(modinfo_fe_state_preserved m mf Ready Preserved))|exact Preserved].
 - assert(Sep2:xsep(extA m0 bd bw bi)[(bp,0);(br,0)]).
   { intros [|[|r]] Bound;[exact(Sep 0%nat ltac:(cbn;lia))|exact(Sep 1%nat ltac:(cbn;lia))|cbn in Bound;lia]. }
   destruct(eval_gej_odd_finite_calls m0 bd base bw edge cursor N bi m bp br x y z
    CountCall Output Cap Prefix Sep2 ltac:(congruence) X Y Z Flag Ready FP FR)
    as(ma & mn & mo & mf & Affine & Normalize & Odd & Write & Final & FPF & FRF & Frame & ReadyF & Preserved).
   set(bit:=Bit.toBool(@literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z))).
   assert(FLF:Mem.range_perm mf bl 0 16 Cur Freeable).
   { eapply curve_keep_free;[lia|exact FL|exact Frame|];intros;split;[congruence|];split;[congruence|exact(Sep 2%nat ltac:(cbn;lia))]. }
   exists(gej_odd_parity_temps(gej_odd_flagged le false)bit),mf;split.
   + unfold gej_odd_after_read;eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mf)
      (le1:=gej_odd_parity_temps(gej_odd_flagged le false)bit).
     * eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=m)(le1:=gej_odd_flagged le false);[exact FlagRun|].
       unfold gej_odd_branch;eapply exec_Sifthenelse with(v1:=Vint Int.zero)(b:=false).
       -- apply eval_Etempvar;unfold gej_odd_flagged;apply PTree.gss.
       -- reflexivity.
       -- apply(exec_gej_odd_finite_from_calls(gej_odd_flagged le false)m ma mn mo mf bl bp br bd base bit);
          [apply FlaggedDst|exact Affine|exact Normalize|exact Odd|exact Write].
     * apply exec_Sreturn_some;constructor.
   + split;[exact Final|];split;[exact FPF|];split;[exact FLF|];split;[exact FRF|];split.
     * eapply lframe_implies;[exact Frame|];intros b pos(NP & NR & NL & NE)Valid;split;[exact NP|];split;assumption.
     * split;assumption.
Qed.
