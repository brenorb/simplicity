(** Derive the actual tag read for either kind of canonical buffer chunk,
    preserving its arbitrary absent padding or exact present byte cells. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_encoding C.jet_input_layout C.jet_frame_layout.
Require Import C.jet_buffer_input C.jet_readBit_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition byte_chunk_tag (c : byte_chunk) := match snd c with None => false | Some _ => true end.
Definition byte_chunk_payload_cells (c : byte_chunk) : list BitMachine.Cell :=
  match snd c with None => repeat None (8 * fst c) | Some xs => concat (map (@Translate.encode (Word.Word 3)) xs) end.
Lemma byte_chunk_tag_cells c : byte_chunk_cells c = Some (byte_chunk_tag c) :: byte_chunk_payload_cells c.
Proof. destruct c as [n [xs|]]; reflexivity. Qed.

Theorem eval_buffer8_read_tag_layout m bf base bi edge cursor c :
  frame_base_valid base -> 0 <= cursor <= Int64.max_unsigned - 1 ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bi ->
  frame_input_cells_at m bi edge cursor (byte_chunk_cells c) ->
  exists mr,
    Clight2.eval_funcall ge0 m (Internal f_readBit) [Vptr bf (Ptrofs.repr base)]
      E0 mr (Vint (bit_int (byte_chunk_tag c))) /\
    frame_fields_at mr bf base bi edge (cursor + 1) /\
    frame_input_cells_at mr bi edge (cursor + 1) (byte_chunk_payload_cells c) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mr b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mr b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mr b).
Proof.
  intros HB HC HF HW HD HCells. rewrite byte_chunk_tag_cells in HCells.
  change (frame_input_cells_at m bi edge cursor ([Some (byte_chunk_tag c)] ++ byte_chunk_payload_cells c)) in HCells.
  apply frame_input_cells_at_app in HCells. destruct HCells as [HTag HPayload].
  assert (HFirst : frame_input_bit_at m bi edge cursor (byte_chunk_tag c)).
  { pose proof (HTag 0%nat (Some (byte_chunk_tag c)) eq_refl) as H.
    change (frame_input_bit_at m bi edge (cursor + Z.of_nat 0) (byte_chunk_tag c)) in H.
    replace (cursor + Z.of_nat 0) with cursor in H by lia. exact H. }
  destruct (eval_readBit_layout m bf base bi edge cursor (byte_chunk_tag c) HB HC HF HFirst HW)
    as (mr & HR & HFrame & HMemory & HPerm & HValid).
  exists mr. split; [exact HR|]. split; [exact HFrame|]. split.
  - eapply buffer_input_cells_preserved; [|exact HPayload].
    intros ofs w HL. rewrite HMemory by (left; congruence). exact HL.
  - exact (conj HMemory (conj HPerm HValid)).
Qed.
