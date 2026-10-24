(** Canonical finite normalization output from the original post-inversion
    affine suffix and write_ge. The inverse residue is an explicit internal
    boundary obligation, not an assumption added to a public jet theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.BitMachine.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_toZ C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_frame_inv C.jet_output_layout C.jet_secp_frame C.jet_secp_fe_nv.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math C.jet_secp_curve_frame.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_mul_storage.
Require Import C.jet_secp_point_write_field C.jet_secp_rescale_writer C.jet_secp_rescale_literal.
Require Import C.jet_secp_gej_norm_literal C.jet_secp_gej_negate_literal C.jet_secp_eea_numeric.
Require Import C.jet_secp_invert_literal C.jet_secp_multiply_checkpoint_columns.
Require Import C.jet_secp_gej_affine_arithmetic C.jet_secp_gej_affine_finish C.jet_secp_affine_write_prefix.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words rescale_field_output literal_gej_norm Simplicity.Translate.encode.

Lemma affine_normalized_words_literal ox oy x y zi (a b c:Ty.tySem Word256) :
  radix_value x mod feP=@toZ (WordToZ 8) a mod feP ->
  radix_value y mod feP=@toZ (WordToZ 8) b mod feP ->
  radix_value zi mod feP=literal_invert_numeric(@toZ (WordToZ 8) c) mod feP ->
  radix_value ox mod field_prime=(radix_value x*(radix_value zi*radix_value zi)) mod field_prime ->
  radix_value oy mod field_prime=(radix_value y*(radix_value zi*(radix_value zi*radix_value zi))) mod field_prime ->
  (rescale_field_output ox,rescale_field_output oy)=@literal_gej_norm Alg.CoreFunSem ((a,b),c).
Proof.
  intros X Y Inv VX VY.
  assert (PN:feP<>0) by (unfold feP,feR;lia).
  set (iz:=literal_invert_numeric(@toZ (WordToZ 8) c)) in *.
  assert (Square:(radix_value zi*radix_value zi) mod feP=(iz*iz) mod feP).
  { rewrite (Z.mul_mod (radix_value zi) (radix_value zi) feP),
      (Z.mul_mod iz iz feP) by exact PN;rewrite Inv;reflexivity. }
  assert (Cube:(radix_value zi*(radix_value zi*radix_value zi)) mod feP=(iz*(iz*iz)) mod feP).
  { rewrite (Z.mul_mod (radix_value zi) (radix_value zi*radix_value zi) feP),
      (Z.mul_mod iz (iz*iz) feP) by exact PN;rewrite Inv,Square;reflexivity. }
  assert (NX:radix_value ox mod field_prime=(@toZ (WordToZ 8) a*iz*iz) mod feP).
  { rewrite VX,field_prime_matches_normalizer.
    replace (@toZ (WordToZ 8) a*iz*iz) with (@toZ (WordToZ 8) a*(iz*iz)) by ring.
    rewrite (Z.mul_mod (radix_value x) (radix_value zi*radix_value zi) feP),
      (Z.mul_mod (@toZ (WordToZ 8) a) (iz*iz) feP) by exact PN.
    rewrite X,Square;reflexivity. }
  assert (NY:radix_value oy mod field_prime=(@toZ (WordToZ 8) b*iz*iz*iz) mod feP).
  { rewrite VY,field_prime_matches_normalizer.
    replace (@toZ (WordToZ 8) b*iz*iz*iz) with (@toZ (WordToZ 8) b*(iz*(iz*iz))) by ring.
    rewrite (Z.mul_mod (radix_value y) (radix_value zi*(radix_value zi*radix_value zi)) feP),
      (Z.mul_mod (@toZ (WordToZ 8) b) (iz*(iz*iz)) feP) by exact PN.
    rewrite Y,Cube;reflexivity. }
  pose proof (literal_gej_norm_numeric a b c) as Numeric.
  destruct (@literal_gej_norm Alg.CoreFunSem ((a,b),c)) as [rx ry].
  change ((@toZ (WordToZ 8) rx,@toZ (WordToZ 8) ry)=
    ((@toZ (WordToZ 8) a*iz*iz) mod feP,(@toZ (WordToZ 8) b*iz*iz*iz) mod feP)) in Numeric.
  injection Numeric as EX EY;f_equal;apply (toZ_injective(WordToZ 8));
    rewrite rescale_field_output_value;[rewrite EX;exact NX|rewrite EY;exact NY].
Qed.

Theorem exec_affine_normalized_output m0 bd base bw edge cursor N bi (rc:Z) le m bp ba b2 b3 x y zi
    (a b c:Ty.tySem Word256) :
  write_frame_at m0 bd base bw edge cursor N -> 513<=N ->
  finv m0 bd base bw edge cursor N bi m true [Some true] ->
  xsep (extA m0 bd bw bi) [(bp,0);(ba,0);(b2,0);(b3,0)] ->
  le!_a=Some(Vptr bp Ptrofs.zero) -> le!_r=Some(Vptr ba Ptrofs.zero) ->
  bp<>b2 -> bp<>b3 -> b2<>b3 -> ba<>bp -> ba<>b2 -> ba<>b3 ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds zi ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 zi) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable ->
  radix_value x mod feP=@toZ (WordToZ 8) a mod feP ->
  radix_value y mod feP=@toZ (WordToZ 8) b mod feP ->
  radix_value zi mod feP=literal_invert_numeric(@toZ (WordToZ 8) c) mod feP -> exists mx mr mf,
  Clight2.exec_stmt secp_ge (affine_local_env b2 b3) le m
    (affine_arithmetic_context affine_finish_statement) E0 le mx Out_normal /\
  Mem.free_list mx (blocks_of_env secp_ge (affine_local_env b2 b3))=Some mr /\
  Clight2.eval_funcall secp_ge mr (Internal f_write_ge)
    [Vptr bd (Ptrofs.repr base);Vptr ba Ptrofs.zero] E0 mf Vundef /\
  finv m0 bd base bw edge cursor N bi mf true
    ([Some true]++Simplicity.Translate.encode(@literal_gej_norm Alg.CoreFunSem ((a,b),c))) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  lframe (fun bx _=>bx<>bp /\ bx<>ba /\ bx<>b2 /\ bx<>b3 /\ ~extA m0 bd bw bi bx) m mf.
Proof.
  intros Output Cap Prefix Sep HA HR P2 P3 N23 AP A2 A3 BX BY BZ X Y Z FP FA F2 F3 RX RY RI.
  assert (NotP:~extA m0 bd bw bi bp) by (exact(Sep 0%nat ltac:(cbn;lia))).
  assert (NotA:~extA m0 bd bw bi ba) by (exact(Sep 1%nat ltac:(cbn;lia))).
  assert (Not2:~extA m0 bd bw bi b2) by (exact(Sep 2%nat ltac:(cbn;lia))).
  assert (Not3:~extA m0 bd bw bi b3) by (exact(Sep 3%nat ltac:(cbn;lia))).
  destruct (exec_affine_after_inverse_and_free le m bp ba b2 b3 x y zi
    HA HR P2 P3 N23 AP A2 A3 BX BY BZ X Y Z FP FA F2 F3)
    as (mx & mr & Body & Free & XR & YR & Flag & FPR & FAR & BXO & BYO & VX & VY & Frame).
  assert (External:lframe (fun bx _=>extA m0 bd bw bi bx) m mr).
  { eapply lframe_implies;[exact Frame|].
    intros bx pos Ext Valid;split;[split|split];try (intro Eq;subst bx;contradiction).
    unfold affine_arithmetic_frame;intros [[Eq _]|[[Eq _]|[Eq _]]];subst bx;contradiction. }
  assert (PrefixR:finv m0 bd base bw edge cursor N bi mr true [Some true]).
  { eapply finv_stable;[exact Output|exact Prefix|exact External]. }
  rewrite <-rescale_point_limbs in XR,YR.
  destruct (eval_write_ge_from_prefix m0 bd base bw edge cursor N bi rc true [Some true] mr ba
    (rescale_point_field(point_mul_words x(square_words zi)))
    (rescale_point_field(point_mul_words y(point_mul_words zi(square_words zi))))
    Output ltac:(cbn;lia) PrefixR (rescale_point_bounds _ BXO) (rescale_point_bounds _ BYO) XR YR FAR)
    as (mf & Write & Final & FAF & WriteFrame).
  { intros r Bound;destruct r;[exact NotA|cbn in Bound;lia]. }
  assert (Literal:(rescale_field_output(point_mul_words x(square_words zi)),
    rescale_field_output(point_mul_words y(point_mul_words zi(square_words zi))))=
    @literal_gej_norm Alg.CoreFunSem ((a,b),c)).
  { eapply affine_normalized_words_literal;[exact RX|exact RY|exact RI|exact VX|exact VY]. }
  rewrite !rescale_point_output in Final.
  pose proof (f_equal (@Simplicity.Translate.encode (Ty.Prod Word256 Word256)) Literal) as Encoding.
  rewrite point_encode_pair in Encoding;rewrite Encoding in Final.
  assert (FPF:Mem.range_perm mf bp 0 128 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FPR|exact WriteFrame|].
    intros pos;split;[congruence|exact NotP]. }
  exists mx,mr,mf;split;[exact Body|];split;[exact Free|];split;[exact Write|];
    split;[exact Final|];split;[exact FPF|];split;[exact FAF|].
  eapply lframe_trans; eapply lframe_implies;[exact Frame| |exact WriteFrame|].
  - intros bx pos (NP & NA & N2 & N3 & NE) Valid.
    split;[split|split];try assumption.
    unfold affine_arithmetic_frame;intros [[Eq _]|[[Eq _]|[Eq _]]];congruence.
  - intros bx pos (NP & NA & N2 & N3 & NE) Valid;split;assumption.
Qed.
