(** Actual finite affine/normalize/odd/write calls, with all intermediate
    output premises discharged from reader storage. CTZ remains explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.extraMath C.jet_toZ C.jet_word_repr C.jet_readBit_layout C.jet_sx_mem C.jet_sx_exec
 C.jet_secp_linkage C.jets_secp C.jet_frame_inv C.jet_output_layout C.jet_secp_frame
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_multiply_checkpoint_columns C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_square_spec_bridge
 C.jet_secp_point_mul_storage C.jet_secp_rescale_literal C.jet_secp_affine_inverse_complete
 C.jet_secp_affine_inverse_literal C.jet_secp_gej_norm_output C.jet_secp_gej_norm_reads
 C.jet_secp_affine_y_parity C.jet_secp_gej_odd_literal C.jet_secp_gej_norm_literal C.jet_secp_canonical_odd
 C.jet_secp_invert_literal C.jet_secp_fe_inv_prefix C.jet_secp_bit_writer C.jet_secp_frame_preserve
 C.jet_secp_modinfo_fe_caller C.jet_secp_fe_inverse_state C.jet_clight_internal_preserve C.jet_secp_curve_frame.
Require C.jets.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words literal_gej_norm literal_gej_y_is_odd Simplicity.Translate.encode.

Theorem eval_gej_odd_finite_calls m0 bd base bw edge cursor N bi m bp br (x y z:Ty.tySem Word256) :
 (forall mc w,Int64.unsigned w<>0 ->
   Clight2.eval_funcall secp_ge mc(Internal f_secp256k1_ctz64_var)[Vlong w]
    E0 mc(Vint(Int.repr(Z_ctz(Int64.unsigned w))))) ->
 write_frame_at m0 bd base bw edge cursor N -> 1<=N ->
 finv m0 bd base bw edge cursor N bi m false [] ->
 xsep(extA m0 bd bw bi)[(bp,0);(br,0)] -> bp<>br ->
 fe_at m bp 0(words5(square_reader_rho x)) -> fe_at m bp 40(words5(square_reader_rho y)) ->
 fe_at m bp 80(words5(square_reader_rho z)) -> Mem.load Mint32 m bp 120=Some(Vint Int.zero) ->
 modinfo_fe_state m -> Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable ->
 exists ma mn mo mf,
 Clight2.eval_funcall secp_ge m(Internal f_secp256k1_ge_set_gej_var)
  [Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero]E0 ma Vundef /\
 Clight2.eval_funcall secp_ge ma(Internal f_secp256k1_fe_normalize_var)
  [Vptr br(Ptrofs.repr 40)]E0 mn Vundef /\
 Clight2.eval_funcall secp_ge mn(Internal f_secp256k1_fe_is_odd)
  [Vptr br(Ptrofs.repr 40)]E0 mo
  (Vint(bit_int(Bit.toBool(@literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z))))) /\
 Clight2.eval_funcall secp_ge mo(Internal C.jets.f_writeBit)
  [Vptr bd(Ptrofs.repr base);Vint(bit_int(Bit.toBool(@literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z))))]
  E0 mf(Vint(bit_int(Bit.toBool(@literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z))))) /\
 finv m0 bd base bw edge cursor N bi mf true
  (Simplicity.Translate.encode(@literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z))) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe(fun b _=>b<>bp /\ b<>br /\ ~extA m0 bd bw bi b)m mf /\
 modinfo_fe_state mf /\ readonly_preserved m mf.
Proof.
 intros CountCall Output Cap Prefix Sep Separate X Y Z Flag Ready FP FR.
 destruct(eval_affine_finite_initialized(square_reader_rho x)(square_reader_rho y)(square_reader_rho z)m bp br
  CountCall Separate(square_reader_bounds x)(square_reader_bounds y)(square_reader_bounds z)X Y Z Flag Ready FP FR)
  as(zi & ma & Affine & XA & YA & FlagA & FPA & FRA & BXO & BYO & Numeric & VX & VY & ReadyA & AffineFrame & AffineReadonly).
 assert(Inverse:radix_value zi mod feP=literal_invert_numeric(@toZ(WordToZ 8)z) mod feP).
 { rewrite Numeric,affine_inverse_reader_value,literal_invert_numeric_mod_field by apply word_toZ_range;reflexivity. }
 assert(Literal:(rescale_field_output(point_mul_words(square_reader_rho x)(square_words zi)),
  rescale_field_output(point_mul_words(square_reader_rho y)(point_mul_words zi(square_words zi))))=
  @literal_gej_norm Alg.CoreFunSem ((x,y),z)).
 { eapply affine_normalized_words_literal;[| |exact Inverse|exact VX|exact VY];
   rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue. }
 destruct(eval_affine_normalized_y_odd(point_mul_words(square_reader_rho y)(point_mul_words zi(square_words zi)))
  ma br BYO YA FRA) as(mn & mo & Normalize & Odd & FRO & ParityFrame & ParityReadonly).
 assert(Parity:Bit.toBool(@canonical_fe_is_odd Alg.CoreFunSem
  (rescale_field_output(point_mul_words(square_reader_rho y)(point_mul_words zi(square_words zi)))))=
  Bit.toBool(@literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z))).
 { rewrite literal_gej_y_is_odd_value;pose proof(f_equal snd Literal) as YValue;cbn [snd] in YValue;rewrite YValue;reflexivity. }
 rewrite Parity in Odd.
 assert(NotP:~extA m0 bd bw bi bp) by(exact(Sep 0%nat ltac:(cbn;lia))).
 assert(NotR:~extA m0 bd bw bi br) by(exact(Sep 1%nat ltac:(cbn;lia))).
 assert(BeforeFrame:lframe(fun b _=>b<>bp /\ b<>br)m mo).
 { eapply lframe_trans;[exact AffineFrame|];eapply lframe_implies;[exact ParityFrame|].
   intros b pos(NP & NR)Valid;left;exact NR. }
 assert(External:eqext m0 bd bw bi m mo).
 { eapply lframe_implies;[exact BeforeFrame|];intros b pos Ext Valid;split;intro Same;subst b;contradiction. }
 assert(PrefixO:finv m0 bd base bw edge cursor N bi mo false []).
 { eapply finv_stable;[exact Output|exact Prefix|exact External]. }
 assert(FPO:Mem.range_perm mo bp 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FPA|exact ParityFrame|];intros;left;exact Separate. }
 destruct(eval_secp_writeBit_from_invariant m0 bd base bw edge cursor N bi mo
  (Bit.toBool(@literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z)))Output Cap PrefixO)
  as(mf & Write & Final & WriteFrame & Perms).
 pose proof(secp_writeBit_preserved _ _ _ _ _ Write) as WriteReadonly.
 assert(WholeReadonly:readonly_preserved m mf).
 { eapply preserved_trans;[exact AffineReadonly|];eapply preserved_trans;[exact ParityReadonly|exact WriteReadonly]. }
 exists ma,mn,mo,mf;split;[exact Affine|];split;[exact Normalize|];split;[exact Odd|];split;[exact Write|];split.
 - rewrite literal_gej_y_is_odd_encoded;exact Final.
 - split;[intros pos Range;apply Perms,FPO;exact Range|];split;
    [intros pos Range;apply Perms,FRO;exact Range|];split.
   + eapply lframe_trans.
     * eapply lframe_implies;[exact BeforeFrame|];intros b pos(NP & NR & NE)Valid;split;assumption.
     * eapply lframe_implies;[exact WriteFrame|];intros b pos(NP & NR & NE)Valid;split;intro Same;subst b;apply NE.
       -- apply(fext_bd m0 bd base bw edge cursor N bi Output).
       -- split;[right;left;reflexivity|];eapply bw_valid;[exact Output|lia].
   + split;[exact(proj1(modinfo_fe_state_preserved m mf Ready WholeReadonly))|exact WholeReadonly].
Qed.
