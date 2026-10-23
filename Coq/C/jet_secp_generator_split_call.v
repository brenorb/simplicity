(** The original scalar-split call inside Strauss's nonnull-ng branch.
    The following two original wNAF calls are not executed by this module. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_sx_state C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns.
Require Import C.jet_secp_statement_prefix C.jet_secp_curve_statements.
Require Import C.jet_secp_scalar_split128 C.jet_secp_scalar_split128_literal C.jet_secp_scalar_split128_storage.
Require Import C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_overflow_numeric.
Require Import C.jet_secp_scalar_get_b32_numeric.
Require Import C.jet_secp_scalar_split128_effects.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition generator_scalar_branch := nth 8
 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf))) Sskip.
Definition generator_scalar_split_call := match generator_scalar_branch with
 | Sifthenelse _ (Ssequence call _) _=>call | _=>Sskip end.
Definition generator_wnaf_setup := match generator_scalar_branch with
 | Sifthenelse _ (Ssequence _ rest) _=>rest | _=>Sskip end.

Lemma generator_scalar_branch_source : generator_scalar_branch=
 Sifthenelse (Etempvar _ng (tptr (Tstruct __5826 noattr)))
  (Ssequence generator_scalar_split_call generator_wnaf_setup) Sskip.
Proof. reflexivity. Qed.
Lemma generator_scalar_split_call_source : generator_scalar_split_call=
 curve_call _secp256k1_scalar_split_128 f_secp256k1_scalar_split_128 None
 [Eaddrof (Evar _ng_1 (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
  Eaddrof (Evar _ng_128 (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
  Etempvar _ng (tptr (Tstruct __5826 noattr))].
Proof. reflexivity. Qed.

Lemma scalar_split128_foot_blocks b0 b128 bs base b pos :
 foot [(b0,0);(b128,0);(bs,base)] (map rshape (scalar_split128_regs false)) b pos ->
 b=b0 \/ b=b128 \/ b=bs.
Proof.
 intros (r & shape & delta & chunk & Nth & Cell & Block & Range).
 assert (Index:(r<3)%nat).
 { apply (proj1 (nth_error_Some (map rshape (scalar_split128_regs false)) r));
    rewrite Nth;discriminate. }
 destruct r as [| [| [|r]]];[left;exact Block|right;left;exact Block|right;right;exact Block|lia].
Qed.

Theorem exec_generator_scalar_split e le m value b0 b128 bs base :
 e!_ng_1=Some (b0,Tstruct __5826 noattr) ->
 e!_ng_128=Some (b128,Tstruct __5826 noattr) -> e!_secp256k1_scalar_split_128=None ->
 le!_ng=Some (Vptr bs (Ptrofs.repr base)) -> b0<>b128 -> b0<>bs -> b128<>bs ->
 Mem.range_perm m b0 0 32 Cur Freeable -> Mem.range_perm m b128 0 32 Cur Freeable ->
 scalar_at m bs base (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))) -> exists mf,
 Clight2.exec_stmt secp_ge e le m generator_scalar_split_call E0 le mf Out_normal /\
 scalar_at mf b0 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (literal_split128_low value)))) /\
 scalar_at mf b128 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (literal_split128_high value)))) /\
 Mem.range_perm mf b0 0 32 Cur Freeable /\ Mem.range_perm mf b128 0 32 Cur Freeable /\
 Mem.nextblock mf=Mem.nextblock m /\
 (forall b pos k p,Mem.perm mf b pos k p <-> Mem.perm m b pos k p) /\
 lframe (fun b _=>b<>b0 /\ b<>b128 /\ b<>bs) m mf.
Proof.
 intros LowLocal HighLocal Symbol NG Separate LowSource HighSource LowFree HighFree Input.
 destruct (eval_scalar_split128_from_normalized_storage value m b0 b128 bs base
  Separate LowSource HighSource LowFree HighFree Input)
  as (mf & Call & Low & High & LF & HF & Frame).
 destruct (scalar_split128_permissions m mf _ _ Call) as (Blocks & Perms).
 exists mf;split.
 - rewrite generator_scalar_split_call_source;eapply exec_curve_call with
    (vargs:=[Vptr b0 Ptrofs.zero;Vptr b128 Ptrofs.zero;Vptr bs (Ptrofs.repr base)]) (v:=Vundef).
   + unfold secp_pure;repeat first [left;reflexivity|right].
   + exact Symbol.
   + eapply eval_Econs with (v1:=Vptr b0 Ptrofs.zero).
     * apply eval_Eaddrof;apply eval_Evar_local;exact LowLocal.
     * reflexivity.
     * eapply eval_Econs with (v1:=Vptr b128 Ptrofs.zero).
       -- apply eval_Eaddrof;apply eval_Evar_local;exact HighLocal.
       -- reflexivity.
       -- eapply eval_Econs with (v1:=Vptr bs (Ptrofs.repr base));
           [apply eval_Etempvar;exact NG|reflexivity|constructor].
   + exact Call.
 - split;[exact Low|];split;[exact High|];split;[exact LF|];split;[exact HF|];
    split;[exact Blocks|];split;[exact Perms|].
   eapply lframe_implies;[exact Frame|].
   intros b pos (L & H & S) Valid Foot;destruct (scalar_split128_foot_blocks b0 b128 bs base b pos Foot)
    as [Eq | [Eq | Eq]];contradiction.
Qed.
