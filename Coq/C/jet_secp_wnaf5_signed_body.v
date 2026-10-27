(** Actual C window-5 body branches against the signed literal transitions.
    Full windows and skips are covered; the final partial window and enclosing
    function remain separate composition obligations. *)
From Coq Require Import ZArith Lia List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
From compcert Require Import Integers AST Maps Memory Values Events Clight ClightBigstep.
Require Import C.jet_sx_mem C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_signed
 C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_literal_next C.jet_secp_wnaf5_literal_window
 C.jet_secp_wnaf5_signed C.jet_secp_wnaf5_signed_windows C.jet_secp_wnaf_literal_skip
 C.jet_secp_wnaf_digit C.jet_secp_wnaf_control C.jet_secp_wnaf_loop
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric C.jet_secp_linkage C.jets_secp.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_wnaf5_run literal_wnaf_shift128.

Theorem exec_wnaf5_signed_full_body le m n bit carry sign b base bs last sb word :
 0<=n<2^256 -> 0<=bit<=124 -> (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
 (sign=1 \/ sign= -1) -> literal_wnaf_signed_value sb word=sign*(n/2^bit+carry) ->
 wnaf_loop_fields le bit 129 5 carry sign b base last ->
 scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) -> b<>bs ->
 0<=base -> base+4*bit<=Ptrofs.max_unsigned -> Mem.valid_access m Mint32 b (base+4*bit) Writable ->
 exists lef mf sb' next nib,
 Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop_body E0 lef mf Out_normal /\
 wnaf_loop_fields lef (bit+5) 129 5 (wnaf_carry (wnaf_word n bit 5 carry) 5) sign b base bit /\
 Mem.store Mint32 m b (base+4*bit) (Vint (Int.repr (literal_wnaf5_value nib)))=Some mf /\
 scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of n)) /\ wnaf_memory_effect b m mf /\
 literal_wnaf5_run 5 (sb,word)=((sb',next),repeat (inl tt) 4++[inr nib]) /\
 literal_wnaf5_value nib=sign*wnaf_digit (wnaf_word n bit 5 carry) 5 /\
 literal_wnaf_signed_value sb' next=sign*(n/2^(bit+5)+wnaf_carry (wnaf_word n bit 5 carry) 5) /\
 (wnaf_carry (wnaf_word n bit 5 carry) 5=0 \/ wnaf_carry (wnaf_word n bit 5 carry) 5=1).
Proof.
 intros N HBit Carry Different Sign Value Fields Storage Separate Base Max Writable.
 set (lr:=PTree.set _t'2 (Vint (Int.repr ((n/2^bit) mod 2))) le).
 assert (Read:Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_dispatch E0 lr m Out_normal).
 { apply exec_wnaf_dispatch_nonzero with (carry:=carry);try assumption;try lia.
   - exact (proj1 Fields).
   - exact (proj1 (proj2 (proj2 (proj2 Fields)))). }
 assert (RF:wnaf_loop_fields lr bit 129 5 carry sign b base last).
 { unfold wnaf_loop_fields,lr;destruct Fields as (HB & HL & HW & HC & HS & HP & HLast).
   repeat split;rewrite PTree.gso by discriminate;assumption. }
 destruct (exec_wnaf_nonzero_body lr m n bit 129 5 carry sign b base bs last N ltac:(lia) ltac:(lia)
  ltac:(lia) Carry Different Sign RF Storage Base Max Writable)
  as (mf & Exec & Store & Final & NewCarry & Bounds & Odd & Weighted).
 rewrite Z.min_l in Store,Final,NewCarry by lia.
 destruct (literal_wnaf5_window_signed n bit carry sign sb word ltac:(lia) Carry Different Sign Value)
  as (sb' & next & nib & Run & Digit & Last).
 exists (wnaf_nonzero_temps lr n bit 129 5 carry),mf,sb',next,nib;split.
 - rewrite wnaf_dispatch_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Read|exact Exec].
 - split;[exact Final|];split;[rewrite Digit;exact Store|];split.
   + eapply wnaf_scalar_store_preserved;[exact Store|exact Separate|exact Storage].
   + split;[eapply wnaf_memory_store;exact Store|];split;[exact Run|];
      split;[exact Digit|];split;assumption.
Qed.

Theorem exec_wnaf5_signed_zero_body le m n bit carry sign b base bs last sb word :
 0<=n<2^256 -> 0<=bit<129 -> (carry=0 \/ carry=1) -> (n/2^bit) mod 2=carry ->
 (sign=1 \/ sign= -1) -> literal_wnaf_signed_value sb word=sign*(n/2^bit+carry) ->
 wnaf_loop_fields le bit 129 5 carry sign b base last ->
 scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) ->
 exists lef next,
 Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop_body E0 lef m Out_continue /\
 wnaf_loop_fields lef (bit+1) 129 5 carry sign b base last /\
 literal_wnaf5_run 1 (sb,word)=((sb,next),[inl tt]) /\
 literal_wnaf_signed_value sb next=sign*(n/2^(bit+1)+carry).
Proof.
 intros N HBit Carry Same Sign Value Fields Storage.
 assert (MEven:(n/2^bit+carry) mod 2=0).
 { rewrite Z.add_mod,Same by lia;destruct Carry as [C|C];subst carry;reflexivity. }
 assert (Even:@Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.zero).
 { apply (literal_wnaf_signed_even sb word);rewrite Value,Z.mul_mod,MEven by lia.
   rewrite Z.mul_0_r;reflexivity. }
 set (next:=@literal_wnaf_shift128 Alg.CoreFunSem (sb,word)).
 pose proof (literal_wnaf5_even_signed sb word Even) as [Step Shift].
 assert (Last:literal_wnaf_signed_value sb next=sign*(n/2^(bit+1)+carry)).
 { unfold next;refine (eq_trans Shift (eq_trans (f_equal (fun q:Z=>q/2) Value) _)).
   pose proof (wnaf_skip_residual n bit carry ltac:(lia) Same) as Half.
   pose proof (Z.div_mod (n/2^bit+carry) 2 ltac:(lia)) as Divide;rewrite MEven in Divide.
   symmetry;apply Z.div_unique with (r:=0);[lia|].
   rewrite <-Half;replace (n/2^bit+carry) with (2*((n/2^bit+carry)/2)) at 1 by lia;ring. }
 set (lef:=PTree.set _bit (Vint (Int.repr (bit+1))) (PTree.set _t'2 (Vint (Int.repr carry)) le)).
 exists lef,next;split.
 - rewrite wnaf_dispatch_source;eapply exec_Sseq_2;[|discriminate].
   apply exec_wnaf_dispatch_skip with (n:=n);try assumption;try lia.
   + exact (proj1 Fields).
   + exact (proj1 (proj2 (proj2 (proj2 Fields)))).
 - split;[apply wnaf_skip_fields;exact Fields|];split;[|exact Last].
   exact (literal_wnaf5_run_step 0 (sb,word) (sb,next) (inl tt) Step).
Qed.
