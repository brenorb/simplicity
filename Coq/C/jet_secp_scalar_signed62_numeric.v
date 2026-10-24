(** Numeric interpretation of the words returned by the original C scalar
    conversions, reusing the field repacking bit-window lemmas. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require Import C.jet_secp_scalar_signed62 C.jet_secp_signed62_numeric.
Require Import C.jet_secp_scalar_overflow_numeric C.jet_secp_u128_word_shift.
Require Import C.jet_secp_linkage C.jets_secp C.jet_sx_mem C.jet_secp_fe_nv.
Require Import C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_add_initial C.jet_secp_multiply_normalize_bridge.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_to62_value (w:nat->int64) i := match i with
  | O=>Int64.unsigned(w 0%nat) mod 2^62
  | S O=>(Int64.unsigned(w 0%nat)/2^62+Int64.unsigned(w 1%nat)*2^2) mod 2^62
  | S(S O)=>(Int64.unsigned(w 1%nat)/2^60+Int64.unsigned(w 2%nat)*2^4) mod 2^62
  | S(S(S O))=>(Int64.unsigned(w 2%nat)/2^58+Int64.unsigned(w 3%nat)*2^6) mod 2^62
  | _=>Int64.unsigned(w 3%nat)/2^56 end.

Lemma scalar_to62_words_numeric w i : (i<5)%nat ->
  Int64.unsigned(scalar62_words true w i)=scalar_to62_value w i.
Proof.
  intro Index.
  pose proof(Int64.unsigned_range_2(w 0%nat)) as B0.
  pose proof(Int64.unsigned_range_2(w 1%nat)) as B1.
  pose proof(Int64.unsigned_range_2(w 2%nat)) as B2.
  change Int64.max_unsigned with (2^64-1) in *.
  destruct i as [|[|[|[|[|i]]]]];try lia;cbn [scalar62_words scalar_to62_value List.nth].
  - apply repack_mask_unsigned;lia.
  - apply repack_shifted_join_unsigned;lia.
  - apply repack_shifted_join_unsigned;lia.
  - apply repack_shifted_join_unsigned;lia.
  - apply uns_shru;lia.
Qed.

Lemma scalar_to62_normalized w : signed62_normalized(scalar62_words true w).
Proof.
  intros i Index;rewrite scalar_to62_words_numeric by exact Index.
  destruct i as [|[|[|[|[|i]]]]];try lia;cbn [scalar_to62_value Nat.eqb].
  all:try solve[apply Z.mod_pos_bound;lia].
  pose proof(Int64.unsigned_range_2(w 3%nat)) as Bound.
  change Int64.max_unsigned with (2^64-1) in Bound.
  split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia].
Qed.

Theorem scalar_to62_preserves_value w :
  signed62_unsigned_value(scalar62_words true w)=scalar_limb_value w.
Proof.
  unfold signed62_unsigned_value;rewrite !scalar_to62_words_numeric by lia.
  unfold scalar_to62_value,scalar_limb_value.
  set(a0:=Int64.unsigned(w 0%nat));set(a1:=Int64.unsigned(w 1%nat));
    set(a2:=Int64.unsigned(w 2%nat));set(a3:=Int64.unsigned(w 3%nat)).
  assert(B0:0<=a0<2^64) by (unfold a0;exact(Int64.unsigned_range(w 0%nat))).
  assert(B1:0<=a1<2^64) by (unfold a1;exact(Int64.unsigned_range(w 1%nat))).
  assert(B2:0<=a2<2^64) by (unfold a2;exact(Int64.unsigned_range(w 2%nat))).
  rewrite(repack_join_mod (a0/2^62) a1 2 62 ltac:(lia)
    ltac:(split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia])).
  rewrite(repack_join_mod (a1/2^60) a2 4 62 ltac:(lia)
    ltac:(split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia])).
  rewrite(repack_join_mod (a2/2^58) a3 6 62 ltac:(lia)
    ltac:(split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia])).
  change(62-2) with 60;change(62-4) with 58;change(62-6) with 56.
  pose proof(Z.div_mod a0 (2^62) ltac:(lia)) as E0.
  pose proof(Z.div_mod a1 (2^60) ltac:(lia)) as E1.
  pose proof(Z.div_mod a2 (2^58) ltac:(lia)) as E2.
  pose proof(Z.div_mod a3 (2^56) ltac:(lia)) as E3.
  lia.
Qed.

Lemma scalar62_join_mod64 lo hi shift : 0<=shift<64 -> Int64.unsigned lo<2^shift ->
  Int64.unsigned(Int64.or lo (Int64.shl hi (Int64.repr shift)))=
    (Int64.unsigned lo+Int64.unsigned hi*2^shift) mod 2^64.
Proof.
  intros Shift Low;rewrite Int64.or_commut,Int64.shifted_or_is_add by
    (try exact Shift;rewrite two_p_equiv;exact Low).
  rewrite two_p_equiv,Int64.unsigned_repr_eq;change Int64.modulus with (2^64);f_equal;ring.
Qed.

Definition scalar_from62_value (w:nat->int64) i := match i with
  | O=>Int64.unsigned(w 0%nat)+(Int64.unsigned(w 1%nat) mod 2^2)*2^62
  | S O=>Int64.unsigned(w 1%nat)/2^2+(Int64.unsigned(w 2%nat) mod 2^4)*2^60
  | S(S O)=>Int64.unsigned(w 2%nat)/2^4+(Int64.unsigned(w 3%nat) mod 2^6)*2^58
  | _=>Int64.unsigned(w 3%nat)/2^6+Int64.unsigned(w 4%nat)*2^56 end.

Lemma scalar_from62_words_numeric w : signed62_normalized w -> forall i,(i<4)%nat ->
  Int64.unsigned(scalar62_words false w i)=scalar_from62_value w i.
Proof.
  intros Normal i Index.
  pose proof(Normal 0%nat ltac:(lia)) as B0.
  pose proof(Normal 1%nat ltac:(lia)) as B1.
  pose proof(Normal 2%nat ltac:(lia)) as B2.
  pose proof(Normal 3%nat ltac:(lia)) as B3.
  pose proof(Normal 4%nat ltac:(lia)) as B4.
  cbn [Nat.eqb] in B0,B1,B2,B3,B4.
  destruct i as [|[|[|[|i]]]];try lia;cbn [scalar62_words scalar_from62_value List.nth].
  - rewrite scalar62_join_mod64 by lia;apply repack_join_mod;lia.
  - rewrite scalar62_join_mod64.
    + rewrite uns_shru by lia;apply repack_join_mod;[lia|].
      split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia].
    + lia.
    + rewrite uns_shru by lia;apply Z.div_lt_upper_bound;lia.
  - rewrite scalar62_join_mod64.
    + rewrite uns_shru by lia;apply repack_join_mod;[lia|].
      split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia].
    + lia.
    + rewrite uns_shru by lia;apply Z.div_lt_upper_bound;lia.
  - rewrite scalar62_join_mod64.
    + rewrite uns_shru by lia.
      rewrite(repack_join_mod (Int64.unsigned(w 3%nat)/2^6) (Int64.unsigned(w 4%nat)) 56 64 ltac:(lia)
        ltac:(split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia])).
      rewrite Z.mod_small by exact B4;reflexivity.
    + lia.
    + rewrite uns_shru by lia;apply Z.div_lt_upper_bound;lia.
Qed.

Theorem scalar_from62_preserves_value w : signed62_normalized w ->
  scalar_limb_value(scalar62_words false w)=signed62_unsigned_value w.
Proof.
  intro Normal;unfold scalar_limb_value;rewrite !scalar_from62_words_numeric by (exact Normal||lia).
  unfold scalar_from62_value,signed62_unsigned_value.
  pose proof(Z.div_mod (Int64.unsigned(w 1%nat)) (2^2) ltac:(lia)) as E1.
  pose proof(Z.div_mod (Int64.unsigned(w 2%nat)) (2^4) ltac:(lia)) as E2.
  pose proof(Z.div_mod (Int64.unsigned(w 3%nat)) (2^6) ltac:(lia)) as E3.
  lia.
Qed.

Theorem eval_scalar_to62_value w m bout bin : bout<>bin ->
  Mem.range_perm m bout 0 40 Cur Freeable ->
  scalar_at m bin 0 (scalar_add_values w 0) -> Mem.range_perm m bin 0 32 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_to_signed62)
    [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bout 0 (words5(scalar62_words true w)) /\ signed62_normalized(scalar62_words true w) /\
  signed62_unsigned_value(scalar62_words true w)=scalar_limb_value w /\
  scalar_at mf bin 0 (scalar_add_values w 0) /\
  Mem.range_perm mf bout 0 40 Cur Freeable /\ Mem.range_perm mf bin 0 32 Cur Freeable /\
  lframe (fun b _=>b<>bout /\ b<>bin) m mf.
Proof.
  intros Separate Out Input InFree.
  destruct(eval_scalar62_from_storage true w m bout bin Separate Out Input InFree)
    as (mf & Call & Output & Source & FO & FI & Frame).
  pose proof(scalar_to62_normalized w) as Normal.
  pose proof(scalar_to62_preserves_value w) as Value.
  exists mf;repeat first[assumption|split].
Qed.

Theorem eval_scalar_from62_value w m bout bin : signed62_normalized w -> bout<>bin ->
  Mem.range_perm m bout 0 32 Cur Freeable ->
  fe_at m bin 0 (words5 w) -> Mem.range_perm m bin 0 40 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_from_signed62)
    [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
  scalar_at mf bout 0 (scalar_add_values(scalar62_words false w)0) /\
  scalar_limb_value(scalar62_words false w)=signed62_unsigned_value w /\
  fe_at mf bin 0 (words5 w) /\
  Mem.range_perm mf bout 0 32 Cur Freeable /\ Mem.range_perm mf bin 0 40 Cur Freeable /\
  lframe (fun b _=>b<>bout /\ b<>bin) m mf.
Proof.
  intros Normal Separate Out Input InFree.
  destruct(eval_scalar62_from_storage false w m bout bin Separate Out Input InFree)
    as (mf & Call & Output & Source & FO & FI & Frame).
  pose proof(scalar_from62_preserves_value w Normal) as Value.
  exists mf;repeat first[assumption|split].
Qed.
