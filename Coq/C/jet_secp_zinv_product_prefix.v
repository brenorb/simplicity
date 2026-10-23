(** Join the original finite-path multiplication and square from initial memory. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_curve_statements
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_point_mul_storage C.jet_secp_square_columns C.jet_secp_field_mul_small
 C.jet_secp_square_point_x C.jet_secp_square_execution C.jet_secp_square_numeric
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_zinv_initial_products
 C.jet_secp_statement_prefix.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words.

Definition zinv_first_products := statement_sequence [zinv_az_statement;zinv_z12_statement] Sskip.
Definition zinv_product_frame (bo bz ba bb bx : block) pos :=
 bx<>bo /\ bx<>bz /\ (bx<>ba \/ pos<80 \/ 120<=pos) /\ bx<>bb.

Lemma zinv_tight_square w : mul_small_input_bounds w -> square_input_bounds w.
Proof. intros Bounds i Index;specialize (Bounds i Index);destruct (Nat.eqb i 4);lia. Qed.

Theorem exec_zinv_first_products a b e le m bo bz ba bb :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_bzinv=Some (Vptr bb Ptrofs.zero) ->
 e!_az=Some (bo,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
 e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
 NoDup [bo;bz;ba;bb] -> square_input_bounds a -> square_input_bounds b ->
 Mem.range_perm m bo 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable ->
 fe_at m ba 80 (words5 a) -> Mem.range_perm m ba 0 128 Cur Freeable ->
 fe_at m bb 0 (words5 b) -> Mem.range_perm m bb 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m zinv_first_products E0 le mf Out_normal /\
 fe_at mf bo 0 (words5 (point_mul_words a b)) /\
 fe_at mf bz 0 (words5 (square_words (point_mul_words a b))) /\
 fe_at mf ba 80 (words5 a) /\ fe_at mf bb 0 (words5 b) /\
 Mem.range_perm mf bo 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
 Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
 radix_value (point_mul_words a b) mod feP=(radix_value a*radix_value b) mod feP /\
 radix_value (square_words (point_mul_words a b)) mod feP=
   (radix_value (point_mul_words a b)*radix_value (point_mul_words a b)) mod feP /\
 mul_small_input_bounds (point_mul_words a b) /\
 mul_small_input_bounds (square_words (point_mul_words a b)) /\
 lframe (zinv_product_frame bo bz ba bb) m mf.
Proof.
 intros HA HB EO EZ EM ES Sep BA BB Owned ZOwned A AOwned B BOwned.
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep.
 destruct (exec_zinv_az_from_owned a b e le m bo ba bb HA HB EO EM BA BB
   ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence)
   Owned A AOwned B BOwned)
   as (mi & Az & AZ & AI & BI & OFI & AFI & BFI & Value & Tight & FI).
 assert (ZI : Mem.range_perm mi bz 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact ZOwned|exact FI|].
   intro pos;repeat split;try (left;intuition congruence);intuition congruence. }
 destruct (exec_zinv_z12_from_owned (point_mul_words a b) e le mi bz bo EZ EO ES
   (zinv_tight_square _ Tight) ZI AZ OFI ltac:(intuition congruence))
   as (mf & Square & ZF & ZFF & AZF & OFF & FS).
 assert (OutA : forall pos,square_two_ranges bz bo ba pos).
 { intros pos;unfold square_two_ranges;intuition congruence. }
 assert (OutB : forall pos,square_two_ranges bz bo bb pos).
 { intros pos;unfold square_two_ranges;intuition congruence. }
 pose proof (field_at_lframe _ _ _ _ _ _ AI FS OutA) as AF.
 pose proof (field_at_lframe _ _ _ _ _ _ BI FS OutB) as BF.
 pose proof (curve_keep_free _ _ _ _ 128 ltac:(lia) AFI FS OutA) as AFF.
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(lia) BFI FS OutB) as BFF.
 assert (SquareBound : mul_small_input_bounds (square_words (point_mul_words a b))).
 { intros i Index;exact (proj2 (square_output_bounds _ (zinv_tight_square _ Tight) i Index)). }
 exists mf;split.
 - unfold zinv_first_products;cbn [statement_sequence].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mi);[exact Az|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);[exact Square|constructor].
 - split;[exact AZF|];split;[exact ZF|];split;[exact AF|];split;[exact BF|];
   split;[exact OFF|];split;[exact ZFF|];split;[exact AFF|];split;[exact BFF|];
   split;[exact Value|];split;[apply square_output_numeric;apply zinv_tight_square;exact Tight|];
   split;[exact Tight|];split;[exact SquareBound|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact FI|].
     intros bx pos (NO & NZ & NA & NB) Valid;split;[exact NO|];split;assumption.
   + eapply lframe_implies;[exact FS|].
     intros bx pos (NO & NZ & NA & NB) Valid;unfold square_two_ranges;intuition congruence.
Qed.
