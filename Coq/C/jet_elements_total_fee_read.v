(** Derive lookup storage from the real readHash output. The caller's
    existing table is preserved by actual load framing, not assumed anew. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_sha_program.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_hash_io.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_uint32_array_init C.jet_read32s_layout.
Require Import C.jet_memcmp_model C.jet_memcmp_words C.jet_elements_fee_lookup_table C.jet_elements_total_fee_suffix.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge sha_ge.
Set Default Timeout 10.

Definition total_fee_input_key (hs : list (Ty.tySem Word32)) := words_bytes(map word32_array_value hs).
Definition total_fee_table_storage m tableval entries := entries=[] \/ exists bt base,
  tableval=Vptr bt (Ptrofs.repr base) /\ fee_table_at m bt base entries.

Lemma total_fee_entry_preserved m mf x : fee_entry_at m x ->
  (forall ch b ofs v,Mem.load ch m b ofs=Some v -> Mem.load ch mf b ofs=Some v) -> fee_entry_at mf x.
Proof.
  intros (Base & Max & Len & Bytes & Fee) Loads;split;[exact Base|];split;[exact Max|];split;[exact Len|];split.
  - intros i I;apply Loads;apply Bytes;exact I.
  - apply Loads;exact Fee.
Qed.
Lemma total_fee_table_preserved m mf bt base entries : fee_table_at m bt base entries ->
  (forall ch b ofs v,Mem.load ch m b ofs=Some v -> Mem.load ch mf b ofs=Some v) -> fee_table_at mf bt base entries.
Proof.
  intros (Base & Max & Rows) Loads;split;[exact Base|];split;[exact Max|].
  intros j x At;destruct (Rows j x At) as (Ptr & Entry);split;[apply Loads;exact Ptr|].
  apply (total_fee_entry_preserved m mf x Entry Loads).
Qed.
Lemma total_fee_storage_preserved m mf tableval entries : total_fee_table_storage m tableval entries ->
  (forall ch b ofs v,Mem.load ch m b ofs=Some v -> Mem.load ch mf b ofs=Some v) ->
  total_fee_table_storage mf tableval entries.
Proof.
  intros [Empty|(bt & base & Ptr & Table)] Loads;[left;exact Empty|].
  right;exists bt,base;split;[exact Ptr|apply (total_fee_table_preserved m mf bt base entries Table Loads)].
Qed.

Lemma total_fee_array_key m ba hs : length hs=8%nat ->
  uint32_array_at m ba 0 (map word32_array_value hs) -> fee_key_at m ba 0 (total_fee_input_key hs).
Proof.
  intros Len Array;split;[lia|];split;[change (32<=18446744073709551615+1);lia|];split.
  - unfold total_fee_input_key;rewrite words_bytes_length,map_length,Len;reflexivity.
  - apply words_bytes_at;exact Array.
Qed.

Lemma total_fee_lookup_storage m ba tableval hs entries : length hs=8%nat ->
  uint32_array_at m ba 0 (map word32_array_value hs) -> total_fee_table_storage m tableval entries ->
  fee_lookup_storage m (Vptr ba Ptrofs.zero) tableval (total_fee_input_key hs) entries.
Proof.
  intros Len Array [Empty|(bt & base & Ptr & Table)];[left;exact Empty|].
  right;exists ba,0,bt,base;split;[reflexivity|];split;[exact Ptr|];split;[apply total_fee_array_key;assumption|exact Table].
Qed.

Theorem exec_total_fee_read bs ba le m bi edge rc hs : length hs=8%nat ->
  Mem.range_perm m ba 0 32 Cur Writable -> bs<>ba -> bs<>bi -> ba<>bi ->
  0<=rc -> rc+256<=Int64.max_unsigned -> frame_fields_at m bs 0 bi edge rc ->
  Mem.valid_access m Mint64 bs 8 Writable ->
  (forall i x,nth_error hs i=Some x -> frame_input_word_at m bi edge (rc+32*Z.of_nat i) x) -> exists mf,
  Clight2.exec_stmt elements_ge (total_fee_locals bs ba) le m total_fee_read_stmt E0 le mf Out_normal /\
  uint32_array_at mf ba 0 (map word32_array_value hs) /\
  fee_key_at mf ba 0 (total_fee_input_key hs) /\
  frame_fields_at mf bs 0 bi edge (rc+256) /\
  (forall ch b ofs,b<>bs -> b<>ba -> Mem.load ch mf b ofs=Mem.load ch m b ofs) /\
  (forall b ofs k p,Mem.perm m b ofs k p -> Mem.perm mf b ofs k p) /\
  (forall b,Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros Len Writable Separate SrcInput KeyInput RC Max Fields Cursor Input.
  destruct (eval_sha_readHash m ba 0 bs 0 bi edge rc hs Len ltac:(lia)
    ltac:(change (32<=18446744073709551615);lia) ltac:(exists 0;reflexivity)
    Writable Separate SrcInput KeyInput ltac:(split;[lia|change (16<=18446744073709551615+1);lia])
    RC Max Fields Cursor Input) as (mf & Call & Array & Next & Loads & Perms & Valid).
  rewrite elements_sha_genv in Call.
  exists mf;split.
  - unfold total_fee_read_stmt.
    eapply exec_Scall with (vf:=Vptr(sha_symbol_block _readHash) Ptrofs.zero)
      (f:=Internal f_readHash) (vargs:=[Vptr ba Ptrofs.zero;Vptr bs Ptrofs.zero]) (vres:=Vundef).
    + reflexivity.
    + eapply eval_Elvalue.
      * apply eval_Evar_global;[reflexivity|rewrite <-elements_sha_genv;exact hio_readHash_symbol].
      * apply deref_loc_reference;reflexivity.
    + eapply eval_Econs.
      * unfold total_fee_local_key;apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
      * reflexivity.
      * eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
    + rewrite <-elements_sha_genv;exact hio_readHash_funct.
    + reflexivity.
    + exact Call.
  - split;[exact Array|];split;[apply total_fee_array_key;assumption|];split;[exact Next|];split.
    + intros ch b ofs NotSrc NotKey;apply Loads;left;assumption.
    + split;assumption.
Qed.
