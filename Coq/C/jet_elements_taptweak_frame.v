(** Derive output/global separation from Elements' real tag representation. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers AST Memory Values.
Require Import C.jet_sx_mem C.jet_clight_forward C.jet_clight_internal_preserve C.jet_bitcoin_effects C.jet_read8s_layout
 C.jet_frame_layout C.jet_frame_spec C.jet_output_layout C.jet_byte_pointer_separation
 C.jet_secp_taptweak_writer_state C.jet_elements_taptweak_tag.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma write_frame_256_small_block_separate m bg hi bd base bw edge cursor:
 hi<32 ->block_extent m bg hi ->write_frame_at m bd base bw edge cursor 256 ->bw<>bg.
Proof.
 intros Small Bounds (_ & _ & _ & _ & _ & _ & Writes) Same;subst bw.
 destruct (Writes 0 ltac:(lia)) as (Low0 & _ & _ & Access0 & _).
 destruct (Writes 192 ltac:(lia)) as (Low192 & _ & _ & _ & _).
 assert (Step:write_cell_address edge cursor 0=write_cell_address edge cursor 192+24).
 { unfold write_cell_address;replace (cursor-1-0) with (cursor-1) by lia.
 replace (cursor-1-192) with ((cursor-1)+(-3)*64) by ring.
 rewrite Z.div_add by lia;lia. }
 pose proof (proj1 Access0 (write_cell_address edge cursor 0+7)
 ltac:(change (write_cell_address edge cursor 0<=write_cell_address edge cursor 0+7<write_cell_address edge cursor 0+8);lia)) as Permission.
 pose proof (Bounds _ Cur Writable Permission) as Limit;lia.
Qed.
Theorem elements_taptweak_tag_output_separate m bd base bw edge cursor:
 elements_taptweak_tag_state m ->write_frame_at m bd base bw edge cursor 256 ->
 bd<>elements_taptweak_tag_block /\bw<>elements_taptweak_tag_block.
Proof.
 intros [Bytes [_ [_ Bounds]]] Frame;split.
 - intro Same;subst bd.
   destruct Frame as (Base & Fields & _ & _ & _ & Cursor & _).
   pose proof (proj1 Cursor (base+15)
    ltac:(change (base+8<=base+15<base+8+8);lia)) as Last.
   pose proof (Bounds _ Cur Writable Last) as EndBound.
   pose proof (proj2 (Mem.load_valid_access _ _ _ _ _ (proj1 Fields))) as Alignment.
   change (8|base) in Alignment;unfold frame_base_valid in Base.
   destruct Alignment as [k Factor].
   assert (Zero:base=0) by lia;rewrite Zero in Fields.
   eapply readable_byte_not_pointer;[exact (Bytes 0%nat (Int.repr 84) eq_refl)|exact (proj1 Fields)].
 - eapply write_frame_256_small_block_separate with (hi:=18);[lia| |exact Frame].
   intros pos kind p Perm;exact (proj1 (Bounds pos kind p Perm)).
Qed.

Lemma elements_taptweak_tag_framed m mf P:
 elements_taptweak_tag_state m ->mem_forward m mf ->lframe P m mf ->
 (forall pos,P elements_taptweak_tag_block pos) ->elements_taptweak_tag_state mf.
Proof.
 intros [Bytes [Nul [Readable Bounds]]] Forward Frame Outside.
 assert (Valid:Mem.valid_block m elements_taptweak_tag_block).
 { eapply Mem.perm_valid_block;apply (Readable 0);lia. }
 split.
 - intros i x Nth;rewrite (proj1 Frame) by (try exact Valid;intros;apply Outside);apply Bytes;exact Nth.
 - split.
   + rewrite (proj1 Frame) by (try exact Valid;intros;apply Outside);exact Nul.
   + split.
     * intros pos Range;apply (proj1 (proj2 Frame));[exact Valid|apply Outside|apply Readable;exact Range].
     * intros pos kind p Perm;apply (Bounds pos Max p).
       apply (proj2 (Forward _ Valid));eapply Mem.perm_max;exact Perm.
Qed.
Theorem elements_taptweak_tag_after_write m mf bd base bw edge cursor cells:
 elements_taptweak_tag_state m ->write_frame_at m bd base bw edge cursor 256 ->
 readonly_preserved m mf ->write_effect m mf bd base bw edge cursor 256 cells ->elements_taptweak_tag_state mf.
Proof.
 intros State Output Read Effect.
 destruct (elements_taptweak_tag_output_separate m bd base bw edge cursor State Output) as [D W].
 eapply elements_taptweak_tag_framed;[exact State|exact (proj1 Read)|exact (write_effect_lframe m mf bd base bw edge cursor 256 cells Effect)|].
 intros;split;congruence.
Qed.
