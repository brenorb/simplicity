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
Require Import C.jet_secp_fe_inv_finish C.jet_secp_fe_inv_statements C.jet_secp_signed62_numeric C.jet_secp_signed62_repack.
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

(** Actual inverse unpack/free through affine arithmetic/free and output.
    The preceding inverse loop must still supply the canonical signed62
    result and its inverse-value equality; neither is claimed here. *)
Theorem exec_inverse_return_normalized_output m0 bd base bw edge cursor N bi (rc:Z)
    le ile m bp ba b2 b3 bt bs x y w (a b c:Ty.tySem Word256) :
  write_frame_at m0 bd base bw edge cursor N -> 513<=N ->
  finv m0 bd base bw edge cursor N bi m true [Some true] ->
  xsep (extA m0 bd bw bi) [(bp,0);(ba,0);(b2,0);(b3,0);(bt,0);(bs,0)] ->
  NoDup [bp;ba;b2;b3;bt;bs] ->
  le!_a=Some(Vptr bp Ptrofs.zero) -> le!_r=Some(Vptr ba Ptrofs.zero) ->
  ile!_r=Some(Vptr bp(Ptrofs.repr 80)) ->
  square_input_bounds x -> square_input_bounds y -> signed62_normalized w ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bs 0 (words5 w) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bs 0 40 Cur Freeable ->
  radix_value x mod feP=@toZ (WordToZ 8) a mod feP ->
  radix_value y mod feP=@toZ (WordToZ 8) b mod feP ->
  signed62_unsigned_value w=literal_invert_numeric(@toZ (WordToZ 8) c) ->
  exists mu mr mx ma mf,
  Clight2.exec_stmt secp_ge (fe_inv_env bt bs) ile m fe_inv_unpack E0 ile mu Out_normal /\
  Mem.free_list mu (blocks_of_env secp_ge (fe_inv_env bt bs))=Some mr /\
  Clight2.exec_stmt secp_ge (affine_local_env b2 b3) le mr
    (affine_arithmetic_context affine_finish_statement) E0 le mx Out_normal /\
  Mem.free_list mx (blocks_of_env secp_ge (affine_local_env b2 b3))=Some ma /\
  Clight2.eval_funcall secp_ge ma (Internal f_write_ge)
    [Vptr bd(Ptrofs.repr base);Vptr ba Ptrofs.zero] E0 mf Vundef /\
  finv m0 bd base bw edge cursor N bi mf true
    ([Some true]++Simplicity.Translate.encode(@literal_gej_norm Alg.CoreFunSem ((a,b),c))) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  lframe (fun bx _=>bx<>bp /\ bx<>ba /\ bx<>b2 /\ bx<>b3 /\ bx<>bt /\ bx<>bs /\ ~extA m0 bd bw bi bx) m mf.
Proof.
  intros Output Cap Prefix Sep Distinct HA HR IR BX BY Normal X Y Packed FP FA F2 F3 FT FS RX RY RI.
  assert(Pairs:bp<>b2 /\ bp<>b3 /\ b2<>b3 /\ ba<>bp /\ ba<>b2 /\ ba<>b3 /\
    bt<>bs /\ bp<>bt /\ bp<>bs /\ ba<>bt /\ ba<>bs /\ b2<>bt /\ b2<>bs /\ b3<>bt /\ b3<>bs).
  { repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct;intuition congruence. }
  destruct Pairs as (P2 & P3 & N23 & AP & A2 & A3 & TS & PT & PS & AT & AS & T2 & S2 & T3 & S3).
  destruct(exec_fe_inv_unpack_point_and_free ile m bt bs bp w x y IR TS PT PS Normal Packed X Y FS FT FP)
    as (mu & mr & Unpack & FreeInv & XR & YR & ZR & FPR & BZ & Value & UnpackFrame).
  assert(NotP:~extA m0 bd bw bi bp) by (exact(Sep 0%nat ltac:(cbn;lia))).
  assert(NotT:~extA m0 bd bw bi bt) by (exact(Sep 4%nat ltac:(cbn;lia))).
  assert(NotS:~extA m0 bd bw bi bs) by (exact(Sep 5%nat ltac:(cbn;lia))).
  assert(External:eqext m0 bd bw bi m mr).
  { eapply lframe_implies;[exact UnpackFrame|];intros bx pos Ext Valid.
    split;[left|split];intro Same;subst bx;contradiction. }
  assert(PrefixR:finv m0 bd base bw edge cursor N bi mr true [Some true]).
  { eapply finv_stable;[exact Output|exact Prefix|exact External]. }
  assert(FAR:Mem.range_perm mr ba 0 88 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FA|exact UnpackFrame|];intros;split;[left;exact AP|];split;assumption. }
  assert(F2R:Mem.range_perm mr b2 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F2|exact UnpackFrame|];intros;split;[left;congruence|];split;assumption. }
  assert(F3R:Mem.range_perm mr b3 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F3|exact UnpackFrame|];intros;split;[left;congruence|];split;assumption. }
  assert(SepAffine:xsep (extA m0 bd bw bi) [(bp,0);(ba,0);(b2,0);(b3,0)]).
  { intros [|[|[|[|i]]]] Bound;
      [exact(Sep 0%nat ltac:(cbn;lia))|exact(Sep 1%nat ltac:(cbn;lia))|
       exact(Sep 2%nat ltac:(cbn;lia))|exact(Sep 3%nat ltac:(cbn;lia))|cbn in Bound;lia]. }
  assert(Inverse:radix_value(fe_repack_words false w) mod feP=
    literal_invert_numeric(@toZ (WordToZ 8) c) mod feP) by (rewrite Value,RI;reflexivity).
  destruct(exec_affine_normalized_output m0 bd base bw edge cursor N bi rc le mr bp ba b2 b3
    x y (fe_repack_words false w) a b c Output Cap PrefixR SepAffine HA HR P2 P3 N23 AP A2 A3
    BX BY BZ XR YR ZR FPR FAR F2R F3R RX RY Inverse)
    as (mx & ma & mf & Affine & FreeAffine & Write & Final & FPF & FAF & AffineFrame).
  assert(Whole:lframe (fun bx _=>bx<>bp /\ bx<>ba /\ bx<>b2 /\ bx<>b3 /\ bx<>bt /\ bx<>bs /\ ~extA m0 bd bw bi bx) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact UnpackFrame|];intros bx pos (NP & NA & N2 & N3 & NT & NS & NE) Valid.
      split;[left;exact NP|];split;assumption.
    - eapply lframe_implies;[exact AffineFrame|];intros bx pos (NP & NA & N2 & N3 & NT & NS & NE) Valid.
      repeat split;assumption. }
  exists mu,mr,mx,ma,mf;repeat first[assumption|split].
Qed.
