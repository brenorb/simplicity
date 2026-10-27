(** Every original nonzero window-5 body branch, including its last partial
    window, against the signed literal program. Not a function-entry theorem. *)
From Coq Require Import ZArith Lia List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
From compcert Require Import Integers AST Maps Memory Values Events Clight ClightBigstep.
Require Import C.jet_sx_mem C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_signed
 C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_literal_next C.jet_secp_wnaf5_signed_tail
 C.jet_secp_wnaf_digit C.jet_secp_wnaf_control C.jet_secp_wnaf_loop
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric C.jet_secp_linkage C.jets_secp.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem exec_wnaf5_signed_nonzero_body le m n bit carry sign b base bs last sb word :
 0<=n<2^129 -> 0<=bit<129 -> (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
 (sign=1 \/ sign= -1) -> literal_wnaf_signed_value sb word=sign*(n/2^bit+carry) ->
 wnaf_loop_fields le bit 129 5 carry sign b base last ->
 scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) -> b<>bs ->
 0<=base -> base+4*bit<=Ptrofs.max_unsigned -> Mem.valid_access m Mint32 b (base+4*bit) Writable ->
 let width:=Z.min 5 (129-bit) in exists lef mf sb' next nib,
 Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop_body E0 lef mf Out_normal /\
 wnaf_loop_fields lef (bit+width) 129 5 (wnaf_carry (wnaf_word n bit width carry) 5) sign b base bit /\
 Mem.store Mint32 m b (base+4*bit) (Vint (Int.repr (literal_wnaf5_value nib)))=Some mf /\
 scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of n)) /\ wnaf_memory_effect b m mf /\
 literal_wnaf5_run (Z.to_nat width) (sb,word)=
  ((sb',next),repeat (inl tt) (Z.to_nat (width-1))++[inr nib]) /\
 literal_wnaf5_value nib=sign*wnaf_digit (wnaf_word n bit width carry) 5 /\
 literal_wnaf_signed_value sb' next=sign*(n/2^(bit+width)+wnaf_carry (wnaf_word n bit width carry) 5) /\
 (wnaf_carry (wnaf_word n bit width carry) 5=0 \/ wnaf_carry (wnaf_word n bit width carry) 5=1) /\
 -16<wnaf_digit (wnaf_word n bit width carry) 5<16 /\
 wnaf_digit (wnaf_word n bit width carry) 5 mod 2=1.
Proof.
 intros N HBit Carry Different Sign Value Fields Storage Separate Base Max Writable;cbv zeta.
 assert (N256:0<=n<2^256).
 { assert (2^129<2^256) by (apply Z.pow_lt_mono_r;lia);lia. }
 set (lr:=PTree.set _t'2 (Vint (Int.repr ((n/2^bit) mod 2))) le).
 assert (Read:Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_dispatch E0 lr m Out_normal).
 { apply exec_wnaf_dispatch_nonzero with (carry:=carry);try assumption;try lia.
   - exact (proj1 Fields).
   - exact (proj1 (proj2 (proj2 (proj2 Fields)))). }
 assert (RF:wnaf_loop_fields lr bit 129 5 carry sign b base last).
 { unfold wnaf_loop_fields,lr;destruct Fields as (HB & HL & HW & HC & HS & HP & HLast).
   repeat split;rewrite PTree.gso by discriminate;assumption. }
 destruct (exec_wnaf_nonzero_body lr m n bit 129 5 carry sign b base bs last N256 HBit ltac:(lia)
  ltac:(lia) Carry Different Sign RF Storage Base Max Writable)
  as (mf & Exec & Store & Final & NewCarry & Bounds & Odd & Weighted).
 destruct (literal_wnaf5_split_signed n bit carry sign sb word N HBit Carry Different Sign Value)
  as (sb' & next & nib & Run & Digit & Last).
 exists (wnaf_nonzero_temps lr n bit 129 5 carry),mf,sb',next,nib;split.
 - rewrite wnaf_dispatch_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Read|exact Exec].
 - split;[exact Final|];split;[rewrite Digit;exact Store|];split.
   + eapply wnaf_scalar_store_preserved;[exact Store|exact Separate|exact Storage].
   + split;[eapply wnaf_memory_store;exact Store|];split;[exact Run|];split;[exact Digit|];
      split;[exact Last|];split;[exact NewCarry|];split;assumption.
Qed.
