(** The complete original finite affine call and original writer produce the
    literal normalization payload. No inverse execution/output is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.extraMath C.modinv C.jet_toZ C.jet_word_repr C.jet_sx_mem C.jet_sx_exec
 C.jet_secp_linkage C.jets_secp C.jet_secp_frame C.jet_frame_inv C.jet_output_layout
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_fe_inv_prefix
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_square_spec_bridge
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_invert_literal C.jet_secp_invert_modinv C.jet_secp_fe_invert_writer
 C.jet_secp_affine_inverse_complete C.jet_secp_modinfo_fe_caller C.jet_secp_fe_inverse_state
 C.jet_secp_gej_norm_reads C.jet_secp_gej_norm_output C.jet_secp_gej_norm_literal
 C.jet_secp_rescale_literal C.jet_secp_rescale_writer C.jet_secp_point_write_field
 C.jet_secp_affine_write_prefix C.jet_secp_point_mul_storage C.jet_secp_gej_negate_literal
 C.jet_secp_curve_frame C.jet_secp_field_io_preserve C.jet_clight_internal_frame
 C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words literal_gej_norm Simplicity.Translate.encode.

Lemma literal_invert_numeric_mod_field z : 0<=z<2^256 ->
 literal_invert_numeric(z mod feP)=literal_invert_numeric z.
Proof.
 intro Range;rewrite !literal_invert_numeric_modInv.
 - apply modInv_eqm;unfold eqm;rewrite Z.mod_mod by(unfold feP,feR;lia);reflexivity.
 - exact Range.
 - pose proof(Z.mod_pos_bound z feP ltac:(unfold feP,feR;lia));unfold feP,feR in *;lia.
Qed.

Lemma affine_writer_closed : closed_stmtb field_io_helpers(fn_body f_write_ge)=true.
Proof. vm_compute;reflexivity. Qed.

Theorem eval_affine_finite_write_literal m0 bd base bw edge cursor N bi (rc:Z) m bp br
 (a b c:Ty.tySem Word256) :
 (forall mc w,Int64.unsigned w<>0 ->
   Clight2.eval_funcall secp_ge mc(Internal f_secp256k1_ctz64_var)[Vlong w]
    E0 mc(Vint(Int.repr(Z_ctz(Int64.unsigned w))))) ->
 write_frame_at m0 bd base bw edge cursor N -> 513<=N ->
 finv m0 bd base bw edge cursor N bi m true [Some true] ->
 xsep(extA m0 bd bw bi)[(bp,0);(br,0)] -> bp<>br ->
 fe_at m bp 0(words5(square_reader_rho a)) ->
 fe_at m bp 40(words5(square_reader_rho b)) ->
 fe_at m bp 80(words5(square_reader_rho c)) ->
 Mem.load Mint32 m bp 120=Some(Vint Int.zero) -> modinfo_fe_state m ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable ->
 exists mr mf,
 Clight2.eval_funcall secp_ge m(Internal f_secp256k1_ge_set_gej_var)
  [Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero] E0 mr Vundef /\
 Clight2.eval_funcall secp_ge mr(Internal f_write_ge)
  [Vptr bd(Ptrofs.repr base);Vptr br Ptrofs.zero] E0 mf Vundef /\
 finv m0 bd base bw edge cursor N bi mf true
  ([Some true]++Simplicity.Translate.encode(@literal_gej_norm Alg.CoreFunSem ((a,b),c))) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe(fun bx _=>bx<>bp /\ bx<>br /\ ~extA m0 bd bw bi bx)m mf /\
 modinfo_fe_state mf /\ readonly_preserved m mf.
Proof.
 intros CountCall Output Cap Prefix Sep Separate X Y Z Flag Ready FP FR.
 destruct(eval_affine_finite_initialized(square_reader_rho a)(square_reader_rho b)(square_reader_rho c)
  m bp br CountCall Separate(square_reader_bounds a)(square_reader_bounds b)(square_reader_bounds c)
  X Y Z Flag Ready FP FR)
  as(zi & mr & Affine & XR & YR & FlagR & FPR & FRR & BXO & BYO & Numeric & VX & VY & ReadyR & AffineFrame & AffineReadonly).
 assert(NotP:~extA m0 bd bw bi bp) by(exact(Sep 0%nat ltac:(cbn;lia))).
 assert(NotR:~extA m0 bd bw bi br) by(exact(Sep 1%nat ltac:(cbn;lia))).
 assert(External:eqext m0 bd bw bi m mr).
 { eapply lframe_implies;[exact AffineFrame|];intros bx pos Ext Valid;split;intro Same;subst bx;contradiction. }
 assert(PrefixR:finv m0 bd base bw edge cursor N bi mr true [Some true]).
 { eapply finv_stable;[exact Output|exact Prefix|exact External]. }
 assert(Inverse:radix_value zi mod feP=literal_invert_numeric(@toZ(WordToZ 8)c) mod feP).
 { rewrite Numeric,affine_inverse_reader_value,literal_invert_numeric_mod_field by apply word_toZ_range;reflexivity. }
 assert(Literal:(rescale_field_output(point_mul_words(square_reader_rho a)(square_words zi)),
  rescale_field_output(point_mul_words(square_reader_rho b)(point_mul_words zi(square_words zi))))=
  @literal_gej_norm Alg.CoreFunSem ((a,b),c)).
 { eapply affine_normalized_words_literal;[| |exact Inverse|exact VX|exact VY];
   rewrite <-field_prime_matches_normalizer;apply rescale_reader_residue. }
 rewrite <-rescale_point_limbs in XR,YR.
 destruct(eval_write_ge_from_prefix m0 bd base bw edge cursor N bi rc true [Some true] mr br
  (rescale_point_field(point_mul_words(square_reader_rho a)(square_words zi)))
  (rescale_point_field(point_mul_words(square_reader_rho b)(point_mul_words zi(square_words zi))))
  Output ltac:(cbn;lia) PrefixR(rescale_point_bounds _ BXO)(rescale_point_bounds _ BYO) XR YR FRR)
  as(mf & Write & Final & FRF & WriteFrame).
 { intros [|r] Bound;[exact NotR|cbn in Bound;lia]. }
 rewrite !rescale_point_output in Final.
 pose proof(f_equal(@Simplicity.Translate.encode(Ty.Prod Word256 Word256))Literal) as Encoding.
 rewrite point_encode_pair in Encoding;rewrite Encoding in Final.
 assert(FPF:Mem.range_perm mf bp 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FPR|exact WriteFrame|];intros;split;assumption. }
 assert(WriteReadonly:readonly_preserved mr mf).
 { pose proof Write as Run;inversion Run;subst.
   eapply preserved_trans;[eapply entry_preserved;eassumption|].
   eapply preserved_trans;[|eapply freelist_preserved;eassumption].
   eapply(proj1(internal_exec_preserved _ _ field_io_helpers_ok));
    [eassumption|eapply entry_plain;[eassumption|reflexivity]|exact affine_writer_closed]. }
 exists mr,mf;split;[exact Affine|];split;[exact Write|];split;[exact Final|];
 split;[exact FPF|];split;[exact FRF|];split.
 - eapply lframe_trans; eapply lframe_implies;[exact AffineFrame| |exact WriteFrame|];
   intros bx pos(NP & NR & NE) Valid;split;assumption.
 - split;[exact(proj1(modinfo_fe_state_preserved mr mf ReadyR WriteReadonly))|].
   eapply preserved_trans;[exact AffineReadonly|exact WriteReadonly].
Qed.
