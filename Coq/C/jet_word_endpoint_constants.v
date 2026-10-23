(** Concrete executions at the final aligned writable word.  The block is a
    CompCert memory witness, not a claim about Linux allocator reachability. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_frame_spec C.jet_encoding C.jet_bitmachine_rep C.jet_constant C.jet_constant_layout.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition last_word_address : Z := Ptrofs.max_unsigned - 7.

Theorem last_word_frame_constructible (seed : int64) :
  exists m b,
    write_frame_at m b 0 b last_word_address 64 64 /\
    Mem.load Mint64 m b last_word_address = Some (Vlong seed).
Proof.
  destruct (Mem.alloc Mem.empty 0 18446744073709551616) as [ma b] eqn:HA.
  assert (VA : forall ofs, 0 <= ofs -> ofs + 8 <= 18446744073709551616 -> (8 | ofs) ->
    Mem.valid_access ma Mint64 b ofs Writable).
  { intros ofs Hlo Hhi Hal. eapply Mem.valid_access_implies.
    - eapply Mem.valid_access_alloc_same; [exact HA|exact Hlo|exact Hhi|exact Hal].
    - constructor. }
  assert (VA0 : Mem.valid_access ma Mptr b 0 Writable).
  { change (Mem.valid_access ma Mint64 b 0 Writable). apply VA; try lia. exists 0; reflexivity. }
  assert (VA8 : Mem.valid_access ma Mint64 b 8 Writable).
  { apply VA; try lia. exists 1; reflexivity. }
  assert (VALast : Mem.valid_access ma Mint64 b 18446744073709551608 Writable).
  { apply VA; try lia. exists 2305843009213693951; reflexivity. }
  destruct (Mem.valid_access_store _ _ _ _ (Vptr b (Ptrofs.repr 18446744073709551608)) VA0) as [mp HP].
  assert (VP8 : Mem.valid_access mp Mint64 b 8 Writable).
  { eapply Mem.store_valid_access_1; [exact HP|exact VA8]. }
  destruct (Mem.valid_access_store _ _ _ _ (Vlong (Int64.repr 64)) VP8) as [mc HC].
  assert (VCLast : Mem.valid_access mc Mint64 b 18446744073709551608 Writable).
  { eapply Mem.store_valid_access_1; [exact HC|]. eapply Mem.store_valid_access_1; [exact HP|exact VALast]. }
  destruct (Mem.valid_access_store _ _ _ _ (Vlong seed) VCLast) as [m HI].
  assert (HE : Mem.load Mptr m b 0 = Some (Vptr b (Ptrofs.repr 18446744073709551608))).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ HI Mptr b 0) by (right; left; change (8 <= 18446744073709551608); lia).
    rewrite (Mem.load_store_other _ _ _ _ _ _ HC Mptr b 0) by (right; left; change (8 <= 8); lia).
    exact (Mem.load_store_same _ _ _ _ _ _ HP). }
  assert (HO : Mem.load Mint64 m b 8 = Some (Vlong (Int64.repr 64))).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ HI Mint64 b 8) by (right; left; change (16 <= 18446744073709551608); lia).
    exact (Mem.load_store_same _ _ _ _ _ _ HC). }
  assert (HL : Mem.load Mint64 m b 18446744073709551608 = Some (Vlong seed)).
  { exact (Mem.load_store_same _ _ _ _ _ _ HI). }
  assert (VM8 : Mem.valid_access m Mint64 b 8 Writable).
  { eapply Mem.store_valid_access_1; [exact HI|]. eapply Mem.store_valid_access_1; [exact HC|exact VP8]. }
  assert (VMLast : Mem.valid_access m Mint64 b 18446744073709551608 Writable).
  { eapply Mem.store_valid_access_1; [exact HI|exact VCLast]. }
  exists m,b; split; [|exact HL].
  change (write_frame_at m b 0 b 18446744073709551608 64 64).
  split.
  - unfold frame_base_valid. change (0 <= 0 /\ 16 <= 18446744073709551616). lia.
  - split; [split; [exact HE|exact HO]|]. split; [lia|].
    split; [lia|]. split; [change (64 <= 18446744073709551615); lia|].
    split; [exact VM8|]. intros i Hi.
    unfold write_cell_address. rewrite Z.div_small by lia. cbn.
    split; [lia|]. split; [change (18446744073709551616 <= 18446744073709551615 + 1); lia|].
    split; [right; right; lia|]. split; [exact VMLast|]. exists seed; exact HL.
Qed.

Theorem constants_run_at_last_word (s : constant_size) (high : bool) (seed : int64) (env : val) :
  exists m mf b,
    write_frame_at m b 0 b last_word_address 64 (constant_bits s) /\
    Mem.load Mint64 m b last_word_address = Some (Vlong seed) /\
    Clight2.eval_funcall ge0 m (Internal (constant_jet s high))
      [Vptr b Ptrofs.zero; Vptr b Ptrofs.zero; env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf b last_word_address 64
      (encode (@constant_spec s high Alg.CoreFunSem tt)) /\
    write_prefix_at m mf b last_word_address 64 /\
    frame_fields_at mf b 0 b last_word_address (64 - constant_bits s) /\
    (forall chunk b' ofs, Mem.valid_block m b' ->
      (b' <> b \/ ofs + size_chunk chunk <= 8 \/ 16 <= ofs) ->
      (b' <> b \/ ofs + size_chunk chunk <= last_word_address \/
        last_word_address + 8 <= ofs) ->
      Mem.load chunk mf b' ofs = Mem.load chunk m b' ofs).
Proof.
  destruct (last_word_frame_constructible seed) as (m & b & HFrame & HSeed).
  pose proof HFrame as (HBase & HFields & HEdge & HCount & HMax & HWritable & HWords).
  pose proof (constant_bits_bounds s) as HBits.
  assert (HOutput : write_frame_at m b 0 b 18446744073709551608 64 (constant_bits s)).
  { split; [exact HBase|]. split; [exact HFields|]. split; [exact HEdge|].
    split; [lia|]. split; [exact HMax|]. split; [exact HWritable|].
    intros i Hi; apply HWords; lia. }
  assert (HInput : frame_input_cells_at m b 18446744073709551608 64 (@encode Ty.Unit tt)).
  { intros i c Hi; destruct i; discriminate. }
  destruct (constant_local_spec s high env m b 0 b 0 b b
    18446744073709551608 18446744073709551608 64 64 tt HBase
    ltac:(exists 0; reflexivity) HFields ltac:(lia) ltac:(exact HMax) HInput)
    as (mf & HCall & HOut & HPrefix & HFinal & HLoads).
  { rewrite constant_bitSize; exact HOutput. }
  rewrite constant_bitSize in HFinal,HLoads.
  assert (HDiv : (64 - constant_bits s) / 64 = 0).
  { clear -HBits; apply Z.div_small; lia. }
  rewrite HDiv, Z.mul_0_r, Z.add_0_r in HLoads.
  change (write_word_address 18446744073709551608 64) with 18446744073709551608 in HLoads.
  exists m,mf,b.
  exact (conj HOutput (conj HSeed (conj HCall (conj HOut (conj HPrefix (conj HFinal HLoads)))))).
Qed.
