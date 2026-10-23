(** Concrete three-region preparation for the original scalar split call. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_word_repr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_scalar_split128.
Require Import C.jet_secp_scalar_split128_literal C.jet_secp_b32_exec C.jet_secp_local_regions.
Require Import C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage.
Require Import C.jet_secp_scalar_negate_canonical C.jet_secp_scalar_overflow_numeric.
Require Import C.jet_secp_canonical_scalar.
Require Import C.jet_secp_scalar_limb_bridge C.jet_secp_scalar_reader_lifecycle.
Require Import C.jet_secp_wrapper_run C.jet_input_layout.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma scalar_split128_empty_region rho beta m r :
 bas beta r=0 -> Mem.range_perm m (blk beta r) 0 32 Cur Freeable ->
 region_ok rho beta m r scalar_split128_empty.
Proof.
 intros Base Free.
 unfold region_ok;cbn [scalar_split128_empty rcells rw rfree map].
 split;[rewrite Base;lia|];split.
 - eapply Mem.perm_valid_block;apply (Free 0);lia.
 - split;[reflexivity|];split.
   + apply Forall_forall;intros c [E | [E | [E | [E | E]]]];try contradiction;subst c.
     all:apply writable_undefined_cell;rewrite Base;cbn [size_chunk align_chunk].
     all:try solve [exists 0;reflexivity|exists 1;reflexivity|exists 2;reflexivity|exists 3;reflexivity].
     all:try solve [change Ptrofs.max_unsigned with 18446744073709551615;lia].
     all:intros pos Range;eapply Mem.perm_implies;[apply Free;lia|apply perm_F_any].
   + split;[exact Base|];split;[reflexivity|];split;[exact Free|].
     repeat constructor;cbn;lia.
Qed.

Lemma scalar_split128_initial_storage value m b0 b1 bs base :
 b0<>b1 -> b0<>bs -> b1<>bs ->
 Mem.range_perm m b0 0 32 Cur Freeable -> Mem.range_perm m b1 0 32 Cur Freeable ->
 scalar_at m bs base (map Int64.repr (scalar_limbs_of value)) ->
 rep (scalar_limb_rho value) [(b0,0);(b1,0);(bs,base)] (scalar_split128_regs false) m.
Proof.
 intros S01 S0S S1S F0 F1 Storage.
 change (rep (scalar_limb_rho value) ([(b0,0);(b1,0)]++[(bs,base)])
  ([scalar_split128_empty;scalar_split128_empty]++[scalar_split128_input_region false]) m).
 apply rep_add.
 - change (rep (scalar_limb_rho value) ([(b0,0)]++[(b1,0)])
    ([scalar_split128_empty]++[scalar_split128_empty]) m).
   apply rep_add.
   + change (rep (scalar_limb_rho value) ([]++[(b0,0)]) ([]++[scalar_split128_empty]) m).
     apply rep_add;[apply rep_nil|cbn;tauto|].
     apply scalar_split128_empty_region;[reflexivity|exact F0].
   + cbn;intuition congruence.
   + apply scalar_split128_empty_region;[reflexivity|exact F1].
 - cbn;intuition congruence.
 - apply scalar_region_from_storage;exact Storage.
Qed.

Theorem eval_scalar_split128_from_normalized_storage value m b0 b1 bs base :
 b0<>b1 -> b0<>bs -> b1<>bs ->
 Mem.range_perm m b0 0 32 Cur Freeable -> Mem.range_perm m b1 0 32 Cur Freeable ->
 scalar_at m bs base (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))) ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_split_128)
  [Vptr b0 Ptrofs.zero;Vptr b1 Ptrofs.zero;Vptr bs (Ptrofs.repr base)] E0 mf Vundef /\
 scalar_at mf b0 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (literal_split128_low value)))) /\
 scalar_at mf b1 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (literal_split128_high value)))) /\
 Mem.range_perm mf b0 0 32 Cur Freeable /\ Mem.range_perm mf b1 0 32 Cur Freeable /\
 lframe (fun b pos=>~foot [(b0,0);(b1,0);(bs,base)]
  (map rshape (scalar_split128_regs false)) b pos) m mf.
Proof.
 intros S01 S0S S1S F0 F1 Storage.
 pose proof (scalar_split128_initial_storage _ m b0 b1 bs base S01 S0S S1S F0 F1 Storage) as Rep.
 assert (Input:scalar_split128_input_value
  (scalar_limb_rho (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))=
  @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)).
 { apply scalar_limb_rho_value;apply word_toZ_range. }
 destruct (eval_scalar_split128_normalized_literal false _ _ m value Rep Input)
  as (mf & Call & Final & Low & High & FO & FI & FS & Frame).
 exists mf;split;[exact Call|];split;[exact Low|];split;[exact High|];
 split;[exact FO|];split;assumption.
Qed.

Lemma scalar_split128_rep_after_reader value rc readerbeta bi edge m b0 b1 :
 rep (read_fe_rho (frame_input_word_bits value) rc) readerbeta (scalar_reader_final_regs bi edge) m ->
 b0<>b1 -> b0<>blk readerbeta 0 -> b1<>blk readerbeta 0 ->
 Mem.range_perm m b0 0 32 Cur Freeable -> Mem.range_perm m b1 0 32 Cur Freeable ->
 rep (scalar_limb_rho (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))
  [(b0,0);(b1,0);(blk readerbeta 0,bas readerbeta 0)] (scalar_split128_regs false) m.
Proof.
 intros Reader S01 S0S S1S Free0 Free1.
 destruct (scalar_reader_storage_for_serializer value rc readerbeta bi edge m Reader) as [Storage _].
 apply scalar_split128_initial_storage;assumption.
Qed.
