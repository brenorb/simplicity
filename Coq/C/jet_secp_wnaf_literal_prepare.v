(** Actual post-memset copy/sign/loop/return against the literal wnaf15 vector.
    Caller-provided zeroing, entry/freeing and original external memset remain
    outside this internal boundary. No public jet is registered. *)
From Coq Require Import ZArith Lia List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
From compcert Require Import Integers AST Maps Memory Values Events Clight ClightBigstep.
Require Import C.jet_sx_mem C.jet_secp_wnaf_prepare C.jet_secp_wnaf_literal_loop
  C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_array C.jet_secp_wnaf_digit C.jet_secp_wnaf_control
  C.jet_secp_wnaf_loop C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
  C.jet_secp_linkage C.jets_secp.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem exec_wnaf_post_memset_literal15 le m n ba abase bs b base (word : Ty.tySem (Word 7)) :
  0<=n<2^128 -> @toZ (WordToZ 7) word=n ->
  le!_a=Some (Vptr ba (Ptrofs.repr abase)) ->
  wnaf_loop_fields le 0 129 15 0 1 b base (-1) ->
  scalar_at m ba abase (map Int64.repr (scalar_limbs_of n)) -> ba<>bs -> b<>bs ->
  Mem.range_perm m bs 0 32 Cur Writable ->
  0<=base -> base+4*129<=Ptrofs.max_unsigned ->
  (forall i, 0<=i<129 -> Mem.valid_access m Mint32 b (base+4*i) Writable) ->
  (forall i, 0<=i<129 -> Mem.load Mint32 m b (base+4*i)=Some (Vint Int.zero)) ->
  exists lef mf last digits,
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_post_memset E0 lef mf
      (Out_return (Some (Vint (Int.repr (last+1)),Ctypesdefs.tint))) /\
    wnaf_loop_fields lef 129 129 15 0 1 b base last /\
    scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of n)) /\
    wnaf_array_state mf b base 129 15 1 129 last digits /\
    0<=last+1<=129 /\ Mem.nextblock mf=Mem.nextblock m /\
    (forall bx pos k p, Mem.perm mf bx pos k p <-> Mem.perm m bx pos k p) /\
    lframe (fun bx _=>bx<>bs /\ bx<>b) m mf /\
    map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,word))=
      rev (map (fun i=>digits (Z.of_nat i)) (seq 0 129)).
Proof.
  intros N Value HA Fields Storage SourceSeparate OutputSeparate LocalWritable Base Max Access Load.
  destruct (exec_wnaf_scalar_copy le m n ba abase bs HA SourceSeparate Storage LocalWritable)
    as (mc & Copy & StorageC & BlocksC & PermC & FrameC).
  assert (AccessC : forall i, 0<=i<129 -> Mem.valid_access mc Mint32 b (base+4*i) Writable).
  { intros i Range;destruct (Access i Range) as [Cells Align];split;[|exact Align].
    intros pos R;apply (proj2 (PermC b pos Cur Writable));apply Cells;exact R. }
  assert (LoadC : forall i, 0<=i<129 -> Mem.load Mint32 mc b (base+4*i)=Some (Vint Int.zero)).
  { intros i Range;rewrite (proj1 FrameC Mint32 b (base+4*i)).
    - apply Load;exact Range.
    - eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
        [apply Access;exact Range|constructor].
    - intros pos R;exact OutputSeparate. }
  assert (Power : 2^128<=2^255) by (apply Z.pow_le_mono_r;lia).
  assert (Select : Clight2.exec_stmt secp_ge (wnaf_env bs) le mc wnaf_sign_select E0
    (wnaf_small_temps le) mc Out_normal).
  { apply exec_wnaf_sign_small with (n:=n);[lia|exact StorageC]. }
  destruct (exec_wnaf_loop_zero_literal15 (wnaf_small_temps le) mc n b base bs word N Value
    (wnaf_small_fields _ _ _ _ _ _ _ _ _ Fields) StorageC OutputSeparate Base Max AccessC LoadC)
    as (lef & mf & last & digits & Loop & Final & StorageF & ArrayF & Bound & Effect & Literal).
  destruct Effect as (BlocksF & PermF & FrameF).
  exists lef,mf,last,digits;split.
  - rewrite wnaf_post_memset_source.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Copy|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Select|exact Loop].
  - split;[exact Final|];split;[exact StorageF|];split;[exact ArrayF|];split;[exact Bound|];
      split;[congruence|];split.
    + intros bx pos k p;rewrite <-PermF;apply PermC.
    + split;[|exact Literal].
      eapply lframe_trans.
      * eapply lframe_implies;[exact FrameC|intros bx pos [NEs NEb] VB;exact NEs].
      * eapply lframe_implies;[exact FrameF|intros bx pos [NEs NEb] VB;exact NEb].
Qed.
