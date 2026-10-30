(** Word-level connection for the exact signed C lookup output. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word C.jet_toZ C.jet_word_repr.
Require Import C.jet_secp_fe_math C.jet_secp_generator_globals C.jet_secp_generator_tables_check
 C.jet_secp_generator_table_samples C.jet_secp_generate_literal C.jet_secp_wnaf_literal_mask
 C.jet_secp_table_index C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_generator_table_bounds C.jet_secp_generator_lookup_words.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_clight_forward C.jet_clight_readonly_frame C.jet_secp_generator_tables_certificates.
Require Import C.jet_secp_square_columns.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_generator_lookup_literal C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_generator_globals C.jet_clight_internal_preserve.
Require Import C.jet_elements_taptweak_internal.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_generator_table_block generator_tables_check.
Theorem eval_elements_taptweak_generator_lookup_literal high (word : Ty.tySem (Word 4)) m bout :
 literal_wnaf_signed16 word mod 2=1 -> -16384<literal_wnaf_signed16 word<16384 ->
 elements_taptweak_generator_table_state high m -> Mem.range_perm m bout 0 88 Cur Freeable ->
 let n:=literal_wnaf_signed16 word in
 let coords:=generator_lookup_words high (Z.to_nat (table_storage_index n)) (negb (0<?n)) in
 exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_ecmult_table_get_ge_storage)
 [Vptr bout Ptrofs.zero;Vptr (elements_taptweak_generator_table_block high) Ptrofs.zero;
  Vint (Int.repr n);Vint (Int.repr 15)] E0 mf Vundef /\
 Mem.range_perm mf bout 0 88 Cur Freeable /\
 (forall k:bool,fe_at mf bout (if k then 40 else 0) (words5 (coords k))) /\
 (forall k:bool,radix_value (coords k) mod feP=
   @toZ (WordToZ 8) (if k then snd (@literal_generate_small high Alg.CoreFunSem word)
     else fst (@literal_generate_small high Alg.CoreFunSem word))) /\
 (forall k i,(i<5)%nat -> Int64.unsigned (coords k i)<=2^60) /\
 (forall k,square_input_bounds (coords k)) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\ elements_taptweak_generator_table_state high mf /\
 lframe (fun b pos=>b<>bout \/ pos<0 \/ 84<=pos) m mf.
Proof.
 intros Odd Range Table Owned;cbn zeta.
 destruct (elements_taptweak_eval_generator_table_lookup high (literal_wnaf_signed16 word) m bout
   (generator_digit_magnitude word Odd Range) Table Owned)
   as (mf & Call & Free & Fields & Infinity & State & Frame).
 exists mf;split;[exact Call|];split;[exact Free|];split.
 - intro k;rewrite generator_lookup_words_list;apply Fields.
 - split.
   + intro k;apply generator_lookup_words_literal;[apply generator_tables_checked|exact Odd|exact Range].
   + split;[apply generator_lookup_words_bounds|];split;[apply generator_lookup_words_square_bounds|];
       split;[exact Infinity|];split;assumption.
Qed.

Theorem eval_elements_taptweak_generator_lookup_literal_caller high (word : Ty.tySem (Word 4)) size m bout :
 literal_wnaf_signed16 word mod 2=1 -> -16384<literal_wnaf_signed16 word<16384 ->
 88<=size -> (forall h,elements_taptweak_generator_table_state h m) -> Mem.range_perm m bout 0 size Cur Freeable ->
 let n:=literal_wnaf_signed16 word in
 let coords:=generator_lookup_words high (Z.to_nat (table_storage_index n)) (negb (0<?n)) in
 exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_ecmult_table_get_ge_storage)
 [Vptr bout Ptrofs.zero;Vptr (elements_taptweak_generator_table_block high) Ptrofs.zero;
  Vint (Int.repr n);Vint (Int.repr 15)] E0 mf Vundef /\
 Mem.range_perm mf bout 0 size Cur Freeable /\
 (forall k:bool,fe_at mf bout (if k then 40 else 0) (words5 (coords k))) /\
 (forall k:bool,radix_value (coords k) mod feP=
   @toZ (WordToZ 8) (if k then snd (@literal_generate_small high Alg.CoreFunSem word)
     else fst (@literal_generate_small high Alg.CoreFunSem word))) /\
 (forall k i,(i<5)%nat -> Int64.unsigned (coords k i)<=2^60) /\
 (forall k,square_input_bounds (coords k)) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\ (forall h,elements_taptweak_generator_table_state h mf) /\
 lframe (fun b pos=>b<>bout \/ pos<0 \/ 84<=pos) m mf.
Proof.
 intros Odd Range Size Tables Owned;cbn zeta.
 assert (InitialOwned : Mem.range_perm m bout 0 88 Cur Freeable) by (intros pos Pos;apply Owned;lia).
 destruct (eval_elements_taptweak_generator_lookup_literal high word m bout Odd Range (Tables high) InitialOwned)
   as (mf & Call & Free & Fields & Literal & Bounds & Square & Infinity & State & Frame).
 assert (FinalOwned : Mem.range_perm mf bout 0 size Cur Freeable)
   by (eapply generator_lookup_retains_owned;eassumption).
 assert (FinalTables : forall h,elements_taptweak_generator_table_state h mf).
 { intro h;eapply elements_taptweak_generator_readonly;[apply Tables|].
   eapply elements_taptweak_internal_preserved;
   [exact elements_taptweak_has_table_get_ge_storage|exact Call]. }
 exists mf;split;[exact Call|];split;[exact FinalOwned|];split;[exact Fields|];
   split;[exact Literal|];split;[exact Bounds|];split;[exact Square|];split;[exact Infinity|];split;assumption.
Qed.
