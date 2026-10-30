(** Program-independent representation of the original Elements tag bytes.
    The concrete caller establishes its actual global lookup separately. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Memory Globalenvs Values.
Require Import C.jets_elements C.jet_elements_taptweak_tag C.jet_read8s_layout
 C.jet_sx_mem C.jet_clight_forward C.jet_clight_internal_preserve C.jet_bitcoin_effects
 C.jet_frame_layout C.jet_frame_spec C.jet_output_layout C.jet_byte_pointer_separation
 C.jet_secp_taptweak_writer_state C.jet_elements_taptweak_frame.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition elements_taptweak_tag_state_at (bg:block) m:=
 uint8_array_at m bg 0 elements_taptweak_tag_bytes /\
 Mem.load Mint8unsigned m bg 17=Some (Vint Int.zero) /\
 Mem.range_perm m bg 0 18 Cur Readable /\
 (forall pos kind p,Mem.perm m bg pos kind p ->0<=pos<18 /\perm_order Writable p).
Theorem elements_taptweak_tag_initial_at (prg:Clight.program) bg m:
 Genv.find_var_info (Genv.globalenv prg) bg=Some jets_elements.v_taptweak ->
 Genv.init_mem prg=Some m ->elements_taptweak_tag_state_at bg m.
Proof.
 intros Info Init;destruct (Genv.init_mem_characterization prg bg Info Init)
 as (Perm & Bounds & Loads & _).
 change (Mem.range_perm m bg 0 18 Cur Writable) in Perm.
 specialize (Loads eq_refl).
 change (Mem.load Mint8unsigned m bg 0=Some (Vint (Int.repr 84)) /\
 Mem.load Mint8unsigned m bg 1=Some (Vint (Int.repr 97)) /\
 Mem.load Mint8unsigned m bg 2=Some (Vint (Int.repr 112)) /\
 Mem.load Mint8unsigned m bg 3=Some (Vint (Int.repr 84)) /\
 Mem.load Mint8unsigned m bg 4=Some (Vint (Int.repr 119)) /\
 Mem.load Mint8unsigned m bg 5=Some (Vint (Int.repr 101)) /\
 Mem.load Mint8unsigned m bg 6=Some (Vint (Int.repr 97)) /\
 Mem.load Mint8unsigned m bg 7=Some (Vint (Int.repr 107)) /\
 Mem.load Mint8unsigned m bg 8=Some (Vint (Int.repr 47)) /\
 Mem.load Mint8unsigned m bg 9=Some (Vint (Int.repr 101)) /\
 Mem.load Mint8unsigned m bg 10=Some (Vint (Int.repr 108)) /\
 Mem.load Mint8unsigned m bg 11=Some (Vint (Int.repr 101)) /\
 Mem.load Mint8unsigned m bg 12=Some (Vint (Int.repr 109)) /\
 Mem.load Mint8unsigned m bg 13=Some (Vint (Int.repr 101)) /\
 Mem.load Mint8unsigned m bg 14=Some (Vint (Int.repr 110)) /\
 Mem.load Mint8unsigned m bg 15=Some (Vint (Int.repr 116)) /\
 Mem.load Mint8unsigned m bg 16=Some (Vint (Int.repr 115)) /\
 Mem.load Mint8unsigned m bg 17=Some (Vint Int.zero) /\True) in Loads.
 split.
 - intros i v Nth;destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]];
   cbn [elements_taptweak_tag_bytes map nth_error] in Nth;
   try (destruct i;discriminate Nth);injection Nth as Same;subst v;cbn [Z.of_nat Z.add];tauto.
 - split;[tauto|];split.
   + intros pos Range;eapply Mem.perm_implies;[apply Perm;exact Range|constructor].
   + intros pos kind p Permission;exact (Bounds pos kind p Permission).
Qed.
Theorem elements_taptweak_tag_owned_separate_at bg m b size:elements_taptweak_tag_state_at bg m ->0<size ->
 Mem.range_perm m b 0 size Cur Freeable ->b<>bg.
Proof.
 intros [_ [_ [_ Bounds]]] Positive Free Same;subst b.
 pose proof (proj2 (Bounds 0 Cur Freeable (Free 0 ltac:(clear -Positive;lia)))) as Order;inversion Order.
Qed.
Theorem elements_taptweak_tag_output_separate_at bg m bd base bw edge cursor:
 elements_taptweak_tag_state_at bg m ->write_frame_at m bd base bw edge cursor 256 ->
 bd<>bg /\bw<>bg.
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

Lemma elements_taptweak_tag_framed_at bg m mf P:
 elements_taptweak_tag_state_at bg m ->mem_forward m mf ->lframe P m mf ->
 (forall pos,P bg pos) ->elements_taptweak_tag_state_at bg mf.
Proof.
 intros [Bytes [Nul [Readable Bounds]]] Forward Frame Outside.
 assert (Valid:Mem.valid_block m bg).
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
Theorem elements_taptweak_tag_after_write_at bg m mf bd base bw edge cursor cells:
 elements_taptweak_tag_state_at bg m ->write_frame_at m bd base bw edge cursor 256 ->
 readonly_preserved m mf ->write_effect m mf bd base bw edge cursor 256 cells ->elements_taptweak_tag_state_at bg mf.
Proof.
 intros State Output Read Effect.
 destruct (elements_taptweak_tag_output_separate_at bg m bd base bw edge cursor State Output) as [D W].
 eapply elements_taptweak_tag_framed_at;[exact State|exact (proj1 Read)|exact (write_effect_lframe m mf bd base bw edge cursor 256 cells Effect)|].
 intros;split;congruence.
Qed.
