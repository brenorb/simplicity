(** Representation contracts independent of a particular jet or initial word.
    Bit positions are in frame order (most significant cell first). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory.
Import Values Mem ListNotations.
Local Open Scope Z_scope.

Definition frame_fields (m : mem) (bf bw : block) (edge cursor : Z) : Prop :=
  Mem.load Mptr m bf 0 = Some (Vptr bw (Ptrofs.repr edge)) /\
  Mem.load Mint64 m bf 8 = Some (Vlong (Int64.repr cursor)).

Definition read_cell_address (edge cursor i : Z) : Z :=
  edge - 8 * (1 + (cursor + i) / 64).
Definition read_cell_bit (cursor i : Z) : Z := 63 - (cursor + i) mod 64.
Definition write_cell_address (edge cursor i : Z) : Z :=
  edge + 8 * ((cursor - 1 - i) / 64).
Definition write_cell_bit (cursor i : Z) : Z := (cursor - 1 - i) mod 64.

Definition read_frame (m : mem) (bf bw : block) (edge cursor : Z)
    (cells : list bool) : Prop :=
  frame_fields m bf bw edge cursor /\
  0 <= cursor /\ cursor + Z.of_nat (length cells) <= Int64.max_unsigned /\
  (forall i bit, nth_error cells i = Some bit ->
    exists w,
      Mem.load Mint64 m bw (read_cell_address edge cursor (Z.of_nat i)) =
        Some (Vlong w) /\
      Int64.testbit w (read_cell_bit cursor (Z.of_nat i)) = bit).

Definition write_frame (m : mem) (bf bw : block) (edge cursor count : Z) : Prop :=
  frame_fields m bf bw edge cursor /\
  0 <= count <= cursor /\ cursor <= Int64.max_unsigned /\ bf <> bw /\
  Mem.valid_access m Mint64 bf 8 Writable /\
  (forall i, 0 <= i < count ->
    let addr := write_cell_address edge cursor i in
    0 <= addr /\ addr + 8 <= Ptrofs.max_unsigned /\
    Mem.valid_access m Mint64 bw addr Writable /\
    exists w, Mem.load Mint64 m bw addr = Some (Vlong w)).

Definition word_slice_eq (lo count : Z) (a b : int64) : Prop :=
  forall i, lo <= i < lo + count -> Int64.testbit a i = Int64.testbit b i.

Definition word_outside_eq (lo count : Z) (a b : int64) : Prop :=
  forall i, 0 <= i < 64 -> (i < lo \/ lo + count <= i) ->
    Int64.testbit a i = Int64.testbit b i.

Definition loads_outside_blocks (m m' : mem) (bf bw : block) : Prop :=
  forall chunk b ofs, Mem.valid_block m b -> b <> bf -> b <> bw ->
    Mem.load chunk m' b ofs = Mem.load chunk m b ofs.

Definition single_word_input (m : mem) (bf bw : block)
    (count : Z) (payload : int64) : Prop :=
  frame_fields m bf bw 8 (64 - count) /\ 0 < count <= 64 /\
  exists w, Mem.load Mint64 m bw 0 = Some (Vlong w) /\
    Int64.zero_ext count w = Int64.zero_ext count payload.

(** Useful specialization for the first generalization milestone. Unlike the
    old hypotheses this places no restriction on the initial backing word. *)
Definition single_word_output (m : mem) (bf bw : block) (count : Z) : Prop :=
  frame_fields m bf bw 0 count /\ 0 < count <= 64 /\ bf <> bw /\
  Mem.valid_access m Mint64 bf 8 Writable /\
  Mem.valid_access m Mint64 bw 0 Writable /\
  exists w, Mem.load Mint64 m bw 0 = Some (Vlong w).

Lemma single_word_output_is_write_frame m bf bw count :
  single_word_output m bf bw count -> write_frame m bf bw 0 count count.
Proof.
  intros [HF [HN [HD [PF [PW [w HW]]]]]].
  split; [exact HF |]. split; [lia |].
  split; [change (count <= 18446744073709551615); lia |].
  split; [exact HD |]. split; [exact PF |].
  intros i Hi. unfold write_cell_address.
  rewrite Z.div_small by lia. cbn.
  split; [lia |]. split; [change (8 <= 18446744073709551615); lia |].
  split; [exact PW |]. exists w; exact HW.
Qed.
