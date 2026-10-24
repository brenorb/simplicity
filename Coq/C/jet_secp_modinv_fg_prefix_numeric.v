(** Numeric outputs of the actual inverse-transition initialization.
    Matrix-row bounds are internal divstep obligations; this does not narrow
    a public input domain or add a helper-execution premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_eval C.jet_sx_pure C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_fns C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix.
Require Import C.jet_secp_i128_shift62_oracle.
Require Import C.jet_secp_symbolic_substitution C.jet_secp_i128_mul_exec C.jet_secp_i128_shift62_rep.
Require Import C.jet_secp_i128_mul_numeric C.jet_secp_i128_accum_mul_numeric C.jet_secp_i128_shift62_numeric.
Require Import C.jet_secp_i128_shift62.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_modinv_fg_prefix.

Definition fg_row_low (rho : nat -> int64) i j :=
 smul_accum_lo_word (smul128_lo_word (rho i) (rho 0%nat)) (rho j) (rho 5%nat).
Definition fg_row_high (rho : nat -> int64) i j :=
 smul_accum_hi_word (smul128_lo_word (rho i) (rho 0%nat))
  (smul128_hi_word (rho i) (rho 0%nat)) (rho j) (rho 5%nat).
Definition fg_row_value (rho : nat -> int64) i j :=
 Int64.signed (rho i)*Int64.signed (rho 0%nat)+Int64.signed (rho j)*Int64.signed (rho 5%nat).
Lemma fg_shifted_row_den rho beta i j : map (den rho beta) (fg_shifted_row (XLv i) (XLv j))=
 [Vlong (i128_shift62_low (fg_row_low rho i j) (fg_row_high rho i j));
  Vlong (i128_shift62_high (fg_row_high rho i j))].
Proof. reflexivity. Qed.
Lemma fg_row_numeric rho i j : -2^127<=fg_row_value rho i j<2^127 ->
 i128_signed_value (i128_shift62_low (fg_row_low rho i j) (fg_row_high rho i j))
  (i128_shift62_high (fg_row_high rho i j))=fg_row_value rho i j/2^62.
Proof.
 intro Range;rewrite i128_shift62_numeric;unfold fg_row_low,fg_row_high.
 rewrite smul_accum_exact_if_in_range.
 - rewrite smul128_exact_product;reflexivity.
 - rewrite smul128_exact_product;exact Range.
Qed.

Lemma fg_row_range u v f g : Z.abs (Int64.signed u)+Z.abs (Int64.signed v)<=2^62 ->
 -2^127<=Int64.signed u*Int64.signed f+Int64.signed v*Int64.signed g<2^127.
Proof.
 intro Row.
 pose proof (smul128_word_signed_range f) as F;pose proof (smul128_word_signed_range g) as G.
 assert (AF : Z.abs (Int64.signed f)<=2^63) by (apply Z.abs_le;lia).
 assert (AG : Z.abs (Int64.signed g)<=2^63) by (apply Z.abs_le;lia).
 pose proof (Z.mul_le_mono_nonneg _ _ _ _ (Z.abs_nonneg (Int64.signed u))
  (Z.le_refl _) (Z.abs_nonneg (Int64.signed f)) AF) as UF.
 pose proof (Z.mul_le_mono_nonneg _ _ _ _ (Z.abs_nonneg (Int64.signed v))
  (Z.le_refl _) (Z.abs_nonneg (Int64.signed g)) AG) as VG.
 rewrite <-Z.abs_mul in UF,VG.
 pose proof (Z.abs_triangle (Int64.signed u*Int64.signed f) (Int64.signed v*Int64.signed g)) as Sum.
 assert (B : Z.abs (Int64.signed u*Int64.signed f+Int64.signed v*Int64.signed g)<=2^125) by lia.
 apply Z.abs_le in B;lia.
Qed.

Definition fg_row_at (rho : nat -> int64) beta m (high : bool) : Prop :=
 let r:=if high then 4%nat else 3%nat in
 let i:=if high then 12%nat else 10%nat in
 let j:=if high then 13%nat else 11%nat in
 Mem.load Mint64 m (blk beta r) (bas beta r)=
  Some (Vlong (i128_shift62_low (fg_row_low rho i j) (fg_row_high rho i j))) /\
 Mem.load Mint64 m (blk beta r) (bas beta r+8)=
  Some (Vlong (i128_shift62_high (fg_row_high rho i j))) /\
 i128_signed_value (i128_shift62_low (fg_row_low rho i j) (fg_row_high rho i j))
  (i128_shift62_high (fg_row_high rho i j))=fg_row_value rho i j/2^62.

Lemma fg_prefix_row_storage rho beta m (high : bool) : rep rho beta fg_prefix_out m ->
 Z.abs (Int64.signed (rho (if high then 12%nat else 10%nat)))+
 Z.abs (Int64.signed (rho (if high then 13%nat else 11%nat)))<=2^62 ->
 fg_row_at rho beta m high.
Proof.
 intros Rep Bound.
 set (r:=if high then 4%nat else 3%nat).
 set (i:=if high then 12%nat else 10%nat).
 set (j:=if high then 13%nat else 11%nat).
 pose proof (rep_region rho beta _ m r
  (mkreg (u64_cells 0 (fg_shifted_row (XLv i) (XLv j))) true (Some 16)) Rep
  ltac:(destruct high;reflexivity)) as Region.
 pose proof (region_load rho beta m r _ 0 Mint64
  (i128_shift62_lo_sx (fg_row_lo (XLv i) (XLv j)) (fg_row_hi (XLv i) (XLv j))) Region
  ltac:(cbn [rcells u64_cells fg_shifted_row];left;reflexivity)) as Low.
 pose proof (region_load rho beta m r _ 8 Mint64
  (i128_shift62_hi_sx (fg_row_hi (XLv i) (XLv j))) Region
  ltac:(cbn [rcells u64_cells fg_shifted_row];right;left;reflexivity)) as High.
 change (Mem.load Mint64 m (blk beta r) (bas beta r+0)=
  Some (Vlong (i128_shift62_low (fg_row_low rho i j) (fg_row_high rho i j)))) in Low.
 change (Mem.load Mint64 m (blk beta r) (bas beta r+8)=
  Some (Vlong (i128_shift62_high (fg_row_high rho i j)))) in High.
 rewrite Z.add_0_r in Low.
 split;[exact Low|];split;[exact High|];apply fg_row_numeric.
 apply fg_row_range;exact Bound.
Qed.

Theorem exec_fg_prefix_numeric rho beta e le m :
 rep rho beta (sregs fg_initial) m -> tmatch rho beta (stemps fg_initial) le ->
 ematch beta (snd fg_alloc) e ->
 Z.abs (Int64.signed (rho 10%nat))+Z.abs (Int64.signed (rho 11%nat))<=2^62 ->
 Z.abs (Int64.signed (rho 12%nat))+Z.abs (Int64.signed (rho 13%nat))<=2^62 ->
 exists le' mf,
 Clight2.exec_stmt secp_ge e le m fg_prefix E0 le' mf Out_normal /\
 fg_row_at rho beta mf false /\ fg_row_at rho beta mf true /\
 rep rho beta fg_prefix_out mf /\
 tmatch rho beta (stemps (fst (rsel rho (lay beta) fg_prefix_tree))) le' /\
 lframe (fun b ofs=>~foot beta (map rshape (sregs fg_initial)) b ofs) m mf.
Proof.
 intros Rep Temps Env Low High.
 destruct (exec_fg_prefix rho beta e le m Rep Temps Env) as (le' & mf & Exec & Out & Match & Frame).
 exists le',mf;split;[exact Exec|];split;[apply fg_prefix_row_storage;assumption|];
 split;[apply fg_prefix_row_storage;assumption|];split;[exact Out|];split;assumption.
Qed.
