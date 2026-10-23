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
Local Opaque secp_ge generator_tables_check.

Lemma generator_digit_magnitude (word : Ty.tySem (Word 4)) :
 literal_wnaf_signed16 word mod 2=1 -> -16384<literal_wnaf_signed16 word<16384 ->
 0<Z.abs (literal_wnaf_signed16 word)<16384.
Proof.
 intros Odd Range.
 assert (Nonzero : literal_wnaf_signed16 word<>0)
   by (intro Zero;rewrite Zero in Odd;discriminate).
 destruct (Z_le_dec 0 (literal_wnaf_signed16 word));
   [rewrite Z.abs_eq by lia|rewrite Z.abs_neq by lia];lia.
Qed.

Theorem generator_lookup_words_literal high (word : Ty.tySem (Word 4)) k :
 (forall neg,generator_tables_check high neg=Some nil) ->
 literal_wnaf_signed16 word mod 2=1 -> -16384<literal_wnaf_signed16 word<16384 ->
 let n:=literal_wnaf_signed16 word in
 radix_value (generator_lookup_words high (Z.to_nat (table_storage_index n)) (negb (0<?n)) k) mod feP=
 @toZ (WordToZ 8) (if k then snd (@literal_generate_small high Alg.CoreFunSem word)
   else fst (@literal_generate_small high Alg.CoreFunSem word)).
Proof.
 intros Checked Odd Range;cbn zeta.
 pose proof (generator_digit_magnitude word Odd Range) as Magnitude.
 pose proof (table_storage_index_bound _ Magnitude) as Index.
 assert (NI : Z.of_nat (Z.to_nat (table_storage_index (literal_wnaf_signed16 word)))<8192)
   by (rewrite Z2Nat.id by lia;lia).
 rewrite generator_lookup_words_numeric by (apply Checked || exact NI).
 pose proof (generator_signed_entry_bounds high _ (negb (0<?literal_wnaf_signed16 word)) (Checked false) NI) as Bounds.
 rewrite (generator_tables_match_digit high word Checked Odd Range).
 unfold generator_affine_bounds in Bounds;destruct k;cbn [fst snd];
 rewrite to_fromZ;change (ToZ.Theory.bitSize (WordToZ 8)) with 256%nat;
 rewrite two_power_nat_equiv;rewrite Z.mod_small;
 try reflexivity;unfold feP,feR in Bounds;lia.
Qed.

Lemma generator_lookup_retains_owned size m mf bout : 88<=size ->
 Mem.range_perm m bout 0 size Cur Freeable -> Mem.range_perm mf bout 0 88 Cur Freeable ->
 lframe (fun b pos=>b<>bout \/ pos<0 \/ 84<=pos) m mf ->
 Mem.range_perm mf bout 0 size Cur Freeable.
Proof.
 intros Size Owned Free Frame pos Range;destruct (Z_lt_dec pos 88).
 - apply Free;lia.
 - apply (proj1 (proj2 Frame)).
   + eapply Mem.perm_valid_block;apply (Owned 0);lia.
   + right;right;lia.
   + apply Owned;exact Range.
Qed.

Lemma generator_lookup_retains_table high m mf bout :
 generator_table_state high m -> Mem.range_perm m bout 0 88 Cur Freeable ->
 mem_forward m mf -> lframe (fun b pos=>b<>bout \/ pos<0 \/ 84<=pos) m mf ->
 generator_table_state high mf.
Proof.
 intros [Table Bounds] Owned Forward Frame.
 assert (Sep : bout<>generator_table_block high).
 { intro Equal;subst bout.
   destruct (proj1 (Bounds 0 Cur Freeable) (Owned 0 ltac:(lia))) as [_ Order];inversion Order. }
 pose proof Table as [Valid _];split.
 - eapply generator_table_rep_lframe;[exact Table|exact Frame|].
   intro pos;left;congruence.
 - apply (readonly_bounds_transport m mf _ _ _ Valid Bounds Forward).
   intros pos Range;apply (proj1 (proj2 Frame));[exact Valid|left;congruence|].
   apply (proj2 (Bounds pos Cur Readable));split;[exact Range|constructor].
Qed.

Theorem eval_generator_lookup_literal high (word : Ty.tySem (Word 4)) m bout :
 literal_wnaf_signed16 word mod 2=1 -> -16384<literal_wnaf_signed16 word<16384 ->
 generator_table_state high m -> Mem.range_perm m bout 0 88 Cur Freeable ->
 let n:=literal_wnaf_signed16 word in
 let coords:=generator_lookup_words high (Z.to_nat (table_storage_index n)) (negb (0<?n)) in
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_table_get_ge_storage)
 [Vptr bout Ptrofs.zero;Vptr (generator_table_block high) Ptrofs.zero;
  Vint (Int.repr n);Vint (Int.repr 15)] E0 mf Vundef /\
 Mem.range_perm mf bout 0 88 Cur Freeable /\
 (forall k:bool,fe_at mf bout (if k then 40 else 0) (words5 (coords k))) /\
 (forall k:bool,radix_value (coords k) mod feP=
   @toZ (WordToZ 8) (if k then snd (@literal_generate_small high Alg.CoreFunSem word)
     else fst (@literal_generate_small high Alg.CoreFunSem word))) /\
 (forall k i,(i<5)%nat -> Int64.unsigned (coords k i)<=2^60) /\
 (forall k,square_input_bounds (coords k)) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\ generator_table_state high mf /\
 lframe (fun b pos=>b<>bout \/ pos<0 \/ 84<=pos) m mf.
Proof.
 intros Odd Range Table Owned;cbn zeta.
 destruct (eval_generator_table_lookup high (literal_wnaf_signed16 word) m bout
   (generator_digit_magnitude word Odd Range) Table Owned)
   as (mf & Call & Free & Fields & Infinity & State & Frame).
 exists mf;split;[exact Call|];split;[exact Free|];split.
 - intro k;rewrite generator_lookup_words_list;apply Fields.
 - split.
   + intro k;apply generator_lookup_words_literal;[apply generator_tables_checked|exact Odd|exact Range].
   + split;[apply generator_lookup_words_bounds|];split;[apply generator_lookup_words_square_bounds|];
       split;[exact Infinity|];split;assumption.
Qed.

Theorem eval_generator_lookup_literal_caller high (word : Ty.tySem (Word 4)) size m bout :
 literal_wnaf_signed16 word mod 2=1 -> -16384<literal_wnaf_signed16 word<16384 ->
 88<=size -> (forall h,generator_table_state h m) -> Mem.range_perm m bout 0 size Cur Freeable ->
 let n:=literal_wnaf_signed16 word in
 let coords:=generator_lookup_words high (Z.to_nat (table_storage_index n)) (negb (0<?n)) in
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_table_get_ge_storage)
 [Vptr bout Ptrofs.zero;Vptr (generator_table_block high) Ptrofs.zero;
  Vint (Int.repr n);Vint (Int.repr 15)] E0 mf Vundef /\
 Mem.range_perm mf bout 0 size Cur Freeable /\
 (forall k:bool,fe_at mf bout (if k then 40 else 0) (words5 (coords k))) /\
 (forall k:bool,radix_value (coords k) mod feP=
   @toZ (WordToZ 8) (if k then snd (@literal_generate_small high Alg.CoreFunSem word)
     else fst (@literal_generate_small high Alg.CoreFunSem word))) /\
 (forall k i,(i<5)%nat -> Int64.unsigned (coords k i)<=2^60) /\
 (forall k,square_input_bounds (coords k)) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\ (forall h,generator_table_state h mf) /\
 lframe (fun b pos=>b<>bout \/ pos<0 \/ 84<=pos) m mf.
Proof.
 intros Odd Range Size Tables Owned;cbn zeta.
 assert (InitialOwned : Mem.range_perm m bout 0 88 Cur Freeable) by (intros pos Pos;apply Owned;lia).
 destruct (eval_generator_lookup_literal high word m bout Odd Range (Tables high) InitialOwned)
   as (mf & Call & Free & Fields & Literal & Bounds & Square & Infinity & State & Frame).
 assert (FinalOwned : Mem.range_perm mf bout 0 size Cur Freeable)
   by (eapply generator_lookup_retains_owned;eassumption).
 assert (FinalTables : forall h,generator_table_state h mf).
 { intro h;eapply generator_lookup_retains_table;
   [apply Tables|exact InitialOwned| |exact Frame].
   exact (proj2 (clight_exec_forward secp_ge) _ _ _ _ _ _ Call). }
 exists mf;split;[exact Call|];split;[exact FinalOwned|];split;[exact Fields|];
   split;[exact Literal|];split;[exact Bounds|];split;[exact Square|];split;[exact Infinity|];split;assumption.
Qed.
