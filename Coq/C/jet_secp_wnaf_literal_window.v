(** Original C wNAF reader/digit/store against complete literal windows.
    Covers all window lengths reached by a positive split128 scalar, including
    the final carry. This is not a whole-loop or public jet theorem. *)
From Coq Require Import ZArith Lia List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
From compcert Require Import Integers AST Maps Memory Values Events Clight ClightBigstep.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_zeros C.jet_secp_wnaf_literal_tail
  C.jet_secp_wnaf_literal_mask C.jet_secp_wnaf_digit C.jet_secp_wnaf_control
  C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric C.jet_secp_linkage C.jets_secp.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma literal_wnaf_split_window n bit carry (word : Ty.tySem (Word 7)) :
  0<=n<2^128 -> 0<=bit<129 -> (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
  @toZ (WordToZ 7) word=n/2^bit+carry ->
  let width:=Z.min 15 (129-bit) in
  exists (final : Ty.tySem (Word 7)) (digit : Ty.tySem (Word 4)),
    literal_wnaf_run (Z.to_nat width) (Bit.zero,word)=
      ((Bit.zero,final),repeat (inl tt) (Z.to_nat (width-1))++[inr digit]) /\
    literal_wnaf_signed16 digit=wnaf_digit (wnaf_word n bit width carry) 15 /\
    @toZ (WordToZ 7) final=n/2^(bit+width)+wnaf_carry (wnaf_word n bit width carry) 15.
Proof.
  intros N HBit Carry Different Value;cbv zeta.
  destruct (Z_le_dec 15 (129-bit)) as [Full|Tail].
  - rewrite Z.min_l by lia.
    exact (literal_wnaf_window15 n bit carry word ltac:(lia) Carry Different Value).
  - rewrite Z.min_r by lia.
    pose proof (wnaf_top_quotient_bound n bit 129 HBit N) as Top.
    replace (129-bit-1) with ((129-bit)-1) in Top by lia.
    destruct (literal_wnaf_last_window n bit (129-bit) carry word ltac:(lia) ltac:(lia)
      Top Carry Different Value) as (final & digit & Run & Digit & Last & CarryZero).
    exists final,digit;split;[exact Run|];split;[exact Digit|].
    rewrite Last,CarryZero;replace (bit+(129-bit)) with 129 by lia.
    rewrite Z.div_small by lia;reflexivity.
Qed.

Theorem exec_wnaf_literal_split_window le m n bit carry b base bs (word : Ty.tySem (Word 7)) :
  0<=n<2^128 -> 0<=bit<129 -> (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
  @toZ (WordToZ 7) word=n/2^bit+carry ->
  le!_now=Some (Vint (Int.repr (Z.min 15 (129-bit)))) ->
  le!_carry=Some (Vint (Int.repr carry)) -> le!_w=Some (Vint (Int.repr 15)) ->
  le!_wnaf=Some (Vptr b (Ptrofs.repr base)) -> le!_bit=Some (Vint (Int.repr bit)) ->
  le!_sign=Some (Vint Int.one) ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) ->
  0<=base -> base+4*bit<=Ptrofs.max_unsigned -> Mem.valid_access m Mint32 b (base+4*bit) Writable ->
  let width:=Z.min 15 (129-bit) in
  exists mf (final : Ty.tySem (Word 7)) (digit : Ty.tySem (Word 4)),
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_window_digit E0
      (wnaf_digit_final (PTree.set _t'3 (Vint (Int.repr ((n/2^bit) mod 2^width))) le)
        (wnaf_word n bit width carry) 15) mf Out_normal /\
    literal_wnaf_run (Z.to_nat width) (Bit.zero,word)=
      ((Bit.zero,final),repeat (inl tt) (Z.to_nat (width-1))++[inr digit]) /\
    Mem.store Mint32 m b (base+4*bit) (Vint (Int.repr (literal_wnaf_signed16 digit)))=Some mf /\
    Mem.load Mint32 mf b (base+4*bit)=Some (Vint (Int.repr (literal_wnaf_signed16 digit))) /\
    @toZ (WordToZ 7) final=n/2^(bit+width)+wnaf_carry (wnaf_word n bit width carry) 15.
Proof.
  intros N HBit Carry Different Value HNow HC HW HP HB HS Storage Base Max Writable;cbv zeta.
  destruct (wnaf_window_bounds bit 129 15 HBit ltac:(lia) ltac:(lia)) as (Width & End & Advance).
  destruct (literal_wnaf_split_window n bit carry word N HBit Carry Different Value)
    as (final & digit & Run & Digit & Last).
  destruct (exec_wnaf_window_digit le m n bit (Z.min 15 (129-bit)) 15 carry b base 1 bs
    ltac:(split;[lia|change (2^256) with (2^128*2^128);nia]) ltac:(lia) Width ltac:(lia) ltac:(lia)
    Carry Different ltac:(left;reflexivity) HNow HC HW HP HB HS Storage Base Max Writable)
    as (mf & Exec & Store & Load & Rest).
  exists mf,final,digit;split;[exact Exec|];split;[exact Run|].
  rewrite Z.mul_1_l in Store,Load.
  split;[rewrite Digit;exact Store|];split;[rewrite Digit;exact Load|exact Last].
Qed.
