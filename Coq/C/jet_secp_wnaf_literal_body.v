(** Branch-exact original C body transitions for the literal-aware loop. *)
From Coq Require Import ZArith Lia List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
From compcert Require Import Integers AST Maps Memory Values Events Clight ClightBigstep.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_skip C.jet_secp_wnaf_literal_zeros
  C.jet_secp_wnaf_literal_window C.jet_secp_wnaf_literal_mask C.jet_secp_wnaf_digit
  C.jet_secp_wnaf_control C.jet_secp_wnaf_loop C.jet_secp_scalar_get_b32_storage
  C.jet_secp_scalar_get_b32_numeric C.jet_secp_linkage C.jets_secp.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem exec_wnaf_literal_nonzero_body le m n bit carry b base bs last (word : Ty.tySem (Word 7)) :
  0<=n<2^128 -> 0<=bit<129 -> (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
  @toZ (WordToZ 7) word=n/2^bit+carry ->
  wnaf_loop_fields le bit 129 15 carry 1 b base last ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) -> b<>bs ->
  0<=base -> base+4*bit<=Ptrofs.max_unsigned -> Mem.valid_access m Mint32 b (base+4*bit) Writable ->
  let width:=Z.min 15 (129-bit) in
  exists lef mf (next : Ty.tySem (Word 7)) (digit : Ty.tySem (Word 4)),
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop_body E0 lef mf Out_normal /\
    wnaf_loop_fields lef (bit+width) 129 15 (wnaf_carry (wnaf_word n bit width carry) 15) 1 b base bit /\
    Mem.store Mint32 m b (base+4*bit) (Vint (Int.repr (literal_wnaf_signed16 digit)))=Some mf /\
    scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of n)) /\
    wnaf_memory_effect b m mf /\
    literal_wnaf_run (Z.to_nat width) (Bit.zero,word)=
      ((Bit.zero,next),repeat (inl tt) (Z.to_nat (width-1))++[inr digit]) /\
    literal_wnaf_signed16 digit=wnaf_digit (wnaf_word n bit width carry) 15 /\
    @toZ (WordToZ 7) next=n/2^(bit+width)+wnaf_carry (wnaf_word n bit width carry) 15 /\
    (wnaf_carry (wnaf_word n bit width carry) 15=0 \/ wnaf_carry (wnaf_word n bit width carry) 15=1).
Proof.
  intros N HBit Carry Different Value Fields Storage Separate Base Max Writable;cbv zeta.
  assert (N256 : 0<=n<2^256) by (split;[lia|change (2^256) with (2^128*2^128);nia]).
  pose (lr:=PTree.set _t'2 (Vint (Int.repr ((n/2^bit) mod 2))) le).
  assert (Read : Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_dispatch E0 lr m Out_normal).
  { apply exec_wnaf_dispatch_nonzero with (carry:=carry);try assumption;try lia.
    - exact (proj1 Fields).
    - exact (proj1 (proj2 (proj2 (proj2 Fields)))). }
  assert (RF : wnaf_loop_fields lr bit 129 15 carry 1 b base last).
  { unfold wnaf_loop_fields,lr;destruct Fields as (HB & HL & HW & HC & HS & HP & HLast).
    repeat split;rewrite PTree.gso by discriminate;assumption. }
  destruct (exec_wnaf_nonzero_body lr m n bit 129 15 carry 1 b base bs last N256 HBit ltac:(lia)
    ltac:(lia) Carry Different ltac:(left;reflexivity) RF Storage Base Max Writable)
    as (mf & Exec & Store & Final & NewCarry & Bounds & Odd & Weighted).
  destruct (literal_wnaf_split_window n bit carry word N HBit Carry Different Value)
    as (next & digit & Run & Digit & Last).
  rewrite Z.mul_1_l in Store.
  exists (wnaf_nonzero_temps lr n bit 129 15 carry),mf,next,digit.
  split.
  - rewrite wnaf_dispatch_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);
      [exact Read|exact Exec].
  - split;[exact Final|];split;[rewrite Digit;exact Store|];split.
    + eapply wnaf_scalar_store_preserved;[exact Store|exact Separate|exact Storage].
    + split;[eapply wnaf_memory_store;exact Store|];split;[exact Run|].
      split;[exact Digit|];split;assumption.
Qed.

Theorem exec_wnaf_literal_zero_body le m n bit carry b base bs last (word : Ty.tySem (Word 7)) :
  0<=n<2^128 -> 0<=bit<129 -> (carry=0 \/ carry=1) -> (n/2^bit) mod 2=carry ->
  @toZ (WordToZ 7) word=n/2^bit+carry ->
  wnaf_loop_fields le bit 129 15 carry 1 b base last ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) ->
  exists lef (next : Ty.tySem (Word 7)),
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop_body E0 lef m Out_continue /\
    wnaf_loop_fields lef (bit+1) 129 15 carry 1 b base last /\
    literal_wnaf_run 1 (Bit.zero,word)=((Bit.zero,next),[inl tt]) /\
    @toZ (WordToZ 7) next=n/2^(bit+1)+carry.
Proof.
  intros N HBit Carry Same Value Fields Storage.
  destruct (exec_wnaf_literal_skip le m bs n bit carry word
    ltac:(split;[lia|change (2^256) with (2^128*2^128);nia]) ltac:(lia) Carry Same Value
    (proj1 Fields) (proj1 (proj2 (proj2 (proj2 Fields)))) Storage) as (next & Step & Last & Exec).
  exists (PTree.set _bit (Vint (Int.repr (bit+1))) (PTree.set _t'2 (Vint (Int.repr carry)) le)),next.
  split.
  - rewrite wnaf_dispatch_source;eapply exec_Sseq_2;[exact Exec|discriminate].
  - split;[apply wnaf_skip_fields;exact Fields|];split;[|exact Last].
    exact (literal_wnaf_run_step 0 (Bit.zero,word) (Bit.zero,next) (inl tt) Step).
Qed.
