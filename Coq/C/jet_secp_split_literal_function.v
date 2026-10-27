(** Complete original scalar_split_lambda call against the frozen literal
    Simplicity signed-half outputs. Inputs are the canonical reader's storage
    for an arbitrary Word256; no signed bound is left as a caller premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_linkage C.jets_secp C.jet_sx_mem C.jet_secp_canonical_scalar
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
 C.jet_secp_split_constants C.jet_secp_split_function C.jet_secp_split_literal C.jet_secp_split_numeric
 C.jet_secp_wnaf5_input C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_scalar_normalize literal_scalar_split_lambda.

Theorem eval_scalar_split_lambda_literal (raw:Ty.tySem (Word 8)) m bk br1 br2 :
 split_constants_ready m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m br1 0 32 Cur Freeable ->
 Mem.range_perm m br2 0 32 Cur Freeable -> NoDup [bk;br1;br2] ->
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_split_lambda)
 [Vptr br1 Ptrofs.zero;Vptr br2 Ptrofs.zero;Vptr bk Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf br1 0 (map Int64.repr (scalar_limbs_of
  (wnaf5_input_scalar (fst (fst halves)) (snd (fst halves))))) /\
 scalar_at mf br2 0 (map Int64.repr (scalar_limbs_of
  (wnaf5_input_scalar (fst (snd halves)) (snd (snd halves))))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) /\
 Mem.range_perm mf br1 0 32 Cur Freeable /\ Mem.range_perm mf br2 0 32 Cur Freeable /\
 Mem.range_perm mf bk 0 32 Cur Freeable /\ split_constants_ready mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (split_function_frame bk br1 br2) m mf.
Proof.
 intros Ready Input FK FR1 FR2 Separate;cbv zeta.
 pose (k:=@canonical_scalar_normalize Alg.CoreFunSem raw).
 assert (K:0<= @toZ (WordToZ 8) k<canonical_group_order).
 { unfold k;rewrite canonical_scalar_normalize_numeric;apply Z.mod_pos_bound.
   pose proof canonical_group_order_range;lia. }
 destruct (eval_scalar_split_lambda k m bk br1 br2 K Ready Input FK FR1 FR2 Separate)
  as (mf & Call & First & Second & Rest).
 pose proof (literal_scalar_split_lambda_residues raw) as Bridge.
 change (wnaf5_input_scalar
   (fst (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw)))
   (snd (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw)))=split_first_value (@toZ (WordToZ 8) k) /\
  wnaf5_input_scalar
   (fst (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw)))
   (snd (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw)))=split_second_value (@toZ (WordToZ 8) k)) in Bridge.
 destruct Bridge as [FirstValue SecondValue].
 exists mf;split;[exact Call|];split.
 - exact (eq_rect _ (fun v:Z=>scalar_at mf br1 0 (map Int64.repr (scalar_limbs_of v)))
    First _ (eq_sym FirstValue)).
 - split.
   + exact (eq_rect _ (fun v:Z=>scalar_at mf br2 0 (map Int64.repr (scalar_limbs_of v)))
      Second _ (eq_sym SecondValue)).
   + exact Rest.
Qed.

