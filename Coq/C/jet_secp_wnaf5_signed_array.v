(** One original C window-5 iteration, preserving its digit array and exact
    signed literal segment. The array retains C's positive-magnitude digit
    convention; its stores and the literal values include the same sign. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
From compcert Require Import Integers AST Maps Memory Values Events Clight ClightBigstep.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_signed C.jet_secp_wnaf_literal_array
 C.jet_sx_mem C.jet_secp_wnaf_slice_frame
 C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_literal_next C.jet_secp_wnaf5_signed_body
 C.jet_secp_wnaf5_signed_nonzero C.jet_secp_wnaf_digit C.jet_secp_wnaf_control C.jet_secp_wnaf_loop
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric C.jet_secp_linkage C.jets_secp.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wnaf5_literal_value (digit:Ty.tySem literal_wnaf5_digit) : Z :=
 match digit with inl _=>0 | inr nib=>literal_wnaf5_value nib end.
Lemma wnaf5_literal_segment count nib :
 map wnaf5_literal_value (repeat (inl tt) count++[inr nib])=
 repeat 0 count++[literal_wnaf5_value nib].
Proof. rewrite map_app,map_repeat;reflexivity. Qed.
Lemma wnaf5_literal_run_join left right state next segment :
 literal_wnaf5_run left state=(next,segment) ->
 map wnaf5_literal_value (snd (literal_wnaf5_run (left+right)%nat state))=
 map wnaf5_literal_value (snd (literal_wnaf5_run right next))++map wnaf5_literal_value segment.
Proof.
 intro First;rewrite literal_wnaf5_run_add,First.
 destruct (literal_wnaf5_run right next);cbn [snd];apply map_app.
Qed.

Theorem exec_wnaf5_signed_array_step le m n bit carry sign b base bs last digits sb word :
 0<=n<2^129 -> 0<=bit<129 -> (carry=0 \/ carry=1) -> (sign=1 \/ sign= -1) ->
 literal_wnaf_signed_value sb word=sign*(n/2^bit+carry) ->
 wnaf_loop_fields le bit 129 5 carry sign b base last ->
 scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) -> b<>bs ->
 0<=base -> base+4*129<=Ptrofs.max_unsigned ->
 wnaf_array_state m b base 129 5 sign bit last digits ->
 exists lei mi biti carryi lasti digitsi out sb' next segment,
 Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop_body E0 lei mi out /\
 wnaf_loop_fields lei biti 129 5 carryi sign b base lasti /\
 bit<biti<=129 /\ (carryi=0 \/ carryi=1) /\
 scalar_at mi bs 0 (map Int64.repr (scalar_limbs_of n)) /\
 wnaf_array_state mi b base 129 5 sign biti lasti digitsi /\
 wnaf_memory_effect b m mi /\ (out=Out_normal \/ out=Out_continue) /\
 literal_wnaf5_run (Z.to_nat (biti-bit)) (sb,word)=((sb',next),segment) /\
 literal_wnaf_signed_value sb' next=sign*(n/2^biti+carryi) /\
 map wnaf5_literal_value segment=rev (map (fun d=>sign*d) (wnaf_slice (Z.to_nat (biti-bit)) digitsi bit)) /\
 (forall i,0<=i<bit -> digitsi i=digits i) /\
 lframe (wnaf_slice_outside b base 129) m mi.
Proof.
 intros N HBit Carry Sign Value Fields Storage Separate Base Max Array.
 destruct (Coqlib.zeq ((n/2^bit) mod 2) carry) as [Same|Different].
 - assert (N256:0<=n<2^256).
   { assert (2^129<2^256) by (apply Z.pow_lt_mono_r;lia);lia. }
   destruct (exec_wnaf5_signed_zero_body le m n bit carry sign b base bs last sb word
    N256 HBit Carry Same Sign Value Fields Storage) as (lei & next & Exec & Final & Run & Last).
   exists lei,m,(bit+1),carry,last,digits,Out_continue,sb,next,
    ([inl tt]:list (Ty.tySem literal_wnaf5_digit)).
   split;[exact Exec|];split;[exact Final|];split;[lia|];split;[exact Carry|];
    split;[exact Storage|];split.
   + apply wnaf_array_skip with (bit:=bit);[lia|lia|exact Array].
   + split;[apply wnaf_memory_refl|];split;[right;reflexivity|];split.
     * replace (bit+1-bit) with 1 by lia;exact Run.
     * split;[exact Last|];split.
       -- replace (bit+1-bit) with 1 by lia;change ([0]=[sign*digits bit]).
          rewrite (wnaf_array_suffix _ _ _ _ _ _ _ _ _ Array bit ltac:(lia)),Z.mul_0_r;reflexivity.
       -- split;[intros;reflexivity|apply lframe_refl].
 - set (width:=Z.min 5 (129-bit)).
   destruct (wnaf_window_bounds bit 129 5 HBit ltac:(lia) ltac:(lia)) as (Width & End & Advance).
   fold width in Width,End,Advance.
   destruct (exec_wnaf5_signed_nonzero_body le m n bit carry sign b base bs last sb word
    N HBit Carry Different Sign Value Fields Storage Separate Base ltac:(lia)
    (wnaf_array_access _ _ _ _ _ _ _ _ _ Array bit HBit))
    as (lei & mi & sb' & next & nib & Exec & Final & Store & StorageI & Effect & Run & Digit & Next
      & CarryI & Bounds & Odd).
   fold width in Final,Store,Run,Digit,Next,CarryI,Bounds,Odd.
   set (newdigits:=wnaf_update digits bit (wnaf_digit (wnaf_word n bit width carry) 5)).
   exists lei,mi,(bit+width),(wnaf_carry (wnaf_word n bit width carry) 5),bit,newdigits,
    Out_normal,sb',next,(repeat (inl tt) (Z.to_nat (width-1))++[inr nib]).
   split;[exact Exec|];split;[exact Final|];split;[exact Advance|];split;[exact CarryI|];
    split;[exact StorageI|];split.
   + apply wnaf_array_store with (m:=m) (last:=last);try assumption;try lia.
     rewrite <-Digit;exact Store.
   + split;[exact Effect|];split;[left;reflexivity|];split.
     * replace (bit+width-bit) with width by lia;exact Run.
     * split;[exact Next|];split.
       -- replace (bit+width-bit) with width by lia;rewrite wnaf5_literal_segment.
          assert (Count:Z.to_nat width=S (Z.to_nat (width-1))).
          { rewrite <-Z2Nat.inj_succ by lia;f_equal;lia. }
          rewrite Count;unfold newdigits;rewrite wnaf_slice_update.
          ++ rewrite map_cons,map_repeat,Z.mul_0_r;cbn [rev];rewrite rev_repeat,Digit;reflexivity.
          ++ intros i Range;apply (wnaf_array_suffix _ _ _ _ _ _ _ _ _ Array i).
             rewrite <-Count,Z2Nat.id in Range by lia;lia.
       -- split.
          ++ intros i Range;unfold newdigits,wnaf_update;destruct Coqlib.zeq;[lia|reflexivity].
          ++ eapply wnaf_slice_store_frame;[exact HBit|exact Store].
Qed.
