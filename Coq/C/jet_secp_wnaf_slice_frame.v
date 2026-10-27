(** The actual wNAF stores preserve every byte outside the digit-buffer slice,
    including other writable arrays in the same containing object. *)
From Coq Require Import ZArith Lia.
From compcert Require Import AST Integers Memory Values.
Require Import C.jet_sx_mem C.jet_memset_model.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wnaf_slice_outside (b:block) base len (old:block) pos : Prop :=
 old<>b \/ pos<base \/ base+4*len<=pos.

Lemma wnaf_slice_store_frame m mf b base len bit value :
 0<=bit<len -> Mem.store Mint32 m b (base+4*bit) value=Some mf ->
 lframe (wnaf_slice_outside b base len) m mf.
Proof.
 intros Bit Store;apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|].
 intros pos Range Outside;change (base+4*bit<=pos<base+4*bit+4) in Range.
 unfold wnaf_slice_outside in Outside;destruct Outside as [Other | [Low | High]];
 [apply Other;reflexivity|lia|lia].
Qed.

Lemma wnaf_slice_memset_frame m mf b base len :
 0<=len -> Mem.storebytes m b base (memset_bytes Int.zero (4*len))=Some mf ->
 lframe (wnaf_slice_outside b base len) m mf.
Proof.
 intros Len Store;apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|].
 intros pos Range Outside;rewrite memset_bytes_length in Range by lia.
 unfold wnaf_slice_outside in Outside;destruct Outside as [Other | [Low | High]];
 [apply Other;reflexivity|lia|lia].
Qed.
