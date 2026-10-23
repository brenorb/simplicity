(** One original C body step preserving the exact literal array relation. *)
From Coq Require Import ZArith Lia List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
From compcert Require Import Integers AST Maps Memory Values Events Clight ClightBigstep.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_body C.jet_secp_wnaf_literal_array
  C.jet_secp_wnaf_literal_mask C.jet_secp_wnaf_digit C.jet_secp_wnaf_control C.jet_secp_wnaf_loop
  C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric C.jet_secp_linkage C.jets_secp.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem exec_wnaf_literal_array_step le m n bit carry b base bs last digits (word : Ty.tySem (Word 7)) :
  0<=n<2^128 -> 0<=bit<129 -> (carry=0 \/ carry=1) ->
  @toZ (WordToZ 7) word=n/2^bit+carry ->
  wnaf_loop_fields le bit 129 15 carry 1 b base last ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) -> b<>bs ->
  0<=base -> base+4*129<=Ptrofs.max_unsigned ->
  wnaf_array_state m b base 129 15 1 bit last digits ->
  exists lei mi biti carryi lasti digitsi out (next : Ty.tySem (Word 7)) segment,
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop_body E0 lei mi out /\
    wnaf_loop_fields lei biti 129 15 carryi 1 b base lasti /\
    bit<biti<=129 /\ (carryi=0 \/ carryi=1) /\
    scalar_at mi bs 0 (map Int64.repr (scalar_limbs_of n)) /\
    wnaf_array_state mi b base 129 15 1 biti lasti digitsi /\
    wnaf_memory_effect b m mi /\ (out=Out_normal \/ out=Out_continue) /\
    literal_wnaf_run (Z.to_nat (biti-bit)) (Bit.zero,word)=((Bit.zero,next),segment) /\
    @toZ (WordToZ 7) next=n/2^biti+carryi /\
    map wnaf_literal_value segment=rev (wnaf_slice (Z.to_nat (biti-bit)) digitsi bit) /\
    (forall i, 0<=i<bit -> digitsi i=digits i) /\ (biti=129 -> carryi=0).
Proof.
  intros N HBit Carry Value Fields Storage Separate Base Max Array.
  destruct (Coqlib.zeq ((n/2^bit) mod 2) carry) as [Same|Different].
  - destruct (exec_wnaf_literal_zero_body le m n bit carry b base bs last word
      N HBit Carry Same Value Fields Storage) as (lei & next & Exec & Final & Run & Next).
    exists lei,m,(bit+1),carry,last,digits,Out_continue,next,([inl tt] : list (Ty.tySem literal_wnaf_digit)).
    split;[exact Exec|];split;[exact Final|];split;[lia|];split;[exact Carry|];
      split;[exact Storage|];split.
    + apply wnaf_array_skip with (bit:=bit);[lia|lia|exact Array].
    + split;[apply wnaf_memory_refl|];split;[right;reflexivity|];split.
      * replace (bit+1-bit) with 1 by lia;exact Run.
      * split;[exact Next|];split.
        -- replace (bit+1-bit) with 1 by lia;change ([0]=[digits bit]).
           rewrite (wnaf_array_suffix _ _ _ _ _ _ _ _ _ Array bit ltac:(lia));reflexivity.
        -- split;[intros;reflexivity|intro End].
           assert (bit=128) by lia;subst bit;rewrite Z.div_small in Same by lia.
           change (0=carry) in Same;lia.
  - pose (width:=Z.min 15 (129-bit)).
    destruct (wnaf_window_bounds bit 129 15 HBit ltac:(lia) ltac:(lia)) as (Width & End & Advance).
    fold width in Width,End,Advance.
    destruct (exec_wnaf_literal_nonzero_body le m n bit carry b base bs last word N HBit Carry Different
      Value Fields Storage Separate Base ltac:(lia) (wnaf_array_access _ _ _ _ _ _ _ _ _ Array bit HBit))
      as (lei & mi & next & digit & Exec & Final & Store & StorageI & Effect & Run & Digit & Next & CarryI).
    fold width in Final,Store,Run,Digit,Next,CarryI.
    destruct (wnaf_word_bounds n bit width carry ltac:(lia) ltac:(lia) Carry Different) as (Window & WordOdd).
    assert (Window15 : 0<wnaf_word n bit width carry<2^15).
    { assert (2^width<=2^15) by (apply Z.pow_le_mono_r;lia);lia. }
    destruct (wnaf_digit_bounds (wnaf_word n bit width carry) 15 ltac:(lia) Window15 WordOdd)
      as (_ & Bounds & Odd).
    rewrite <-Digit in Bounds,Odd.
    pose (newdigits:=wnaf_update digits bit (literal_wnaf_signed16 digit)).
    exists lei,mi,(bit+width),(wnaf_carry (wnaf_word n bit width carry) 15),bit,newdigits,
      Out_normal,next,(repeat (inl tt) (Z.to_nat (width-1))++[inr digit]).
    split;[exact Exec|];split;[exact Final|];split;[exact Advance|];split;[exact CarryI|];
      split;[exact StorageI|];split.
    + apply wnaf_array_store with (m:=m) (last:=last);try assumption;try lia.
      rewrite Z.mul_1_l;exact Store.
    + split;[exact Effect|];split;[left;reflexivity|];split.
      * replace (bit+width-bit) with width by lia;exact Run.
      * split;[exact Next|];split.
        -- replace (bit+width-bit) with width by lia.
           rewrite wnaf_literal_segment.
           assert (Count : Z.to_nat width=S (Z.to_nat (width-1))).
           { rewrite <-Z2Nat.inj_succ by lia;f_equal;lia. }
           rewrite Count;unfold newdigits.
           rewrite wnaf_slice_update.
           ++ cbn [rev];rewrite rev_repeat;reflexivity.
           ++ intros i Range;apply (wnaf_array_suffix _ _ _ _ _ _ _ _ _ Array i).
              rewrite <-Count,Z2Nat.id in Range by lia;lia.
        -- split.
           ++ intros i Range;unfold newdigits,wnaf_update;destruct Coqlib.zeq;[lia|reflexivity].
           ++ intro Finish;apply wnaf_finishing_carry_zero with (len:=129);
                try assumption;lia.
Qed.
