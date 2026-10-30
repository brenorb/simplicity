(** The original scalar-split call inside Strauss's nonnull-ng branch.
    The following two original wNAF calls are not executed by this module. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
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

Require Import C.jet_secp_generator_split_call C.jet_elements_taptweak_pure C.jet_elements_taptweak_curve_transport
 C.jet_elements_taptweak_load_body C.jet_elements_taptweak_internal C.jet_clight_internal_preserve.
Lemma elements_taptweak_has_scalar_split128:
 In(_secp256k1_scalar_split_128,f_secp256k1_scalar_split_128)elements_taptweak_curve_helpers.
Proof.
 assert(Found:find(fun it=>Pos.eqb(fst it)_secp256k1_scalar_split_128)elements_taptweak_curve_helpers=
 Some(_secp256k1_scalar_split_128,f_secp256k1_scalar_split_128))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
Local Opaque elements_taptweak_ge.
Theorem exec_elements_taptweak_generator_scalar_split e le m value b0 b128 bs base :
 e!_ng_1=Some (b0,Tstruct __5826 noattr) ->
 e!_ng_128=Some (b128,Tstruct __5826 noattr) -> e!_secp256k1_scalar_split_128=None ->
 le!_ng=Some (Vptr bs (Ptrofs.repr base)) -> b0<>b128 -> b0<>bs -> b128<>bs ->
 Mem.range_perm m b0 0 32 Cur Freeable -> Mem.range_perm m b128 0 32 Cur Freeable ->
 scalar_at m bs base (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))) -> exists mf,
 Clight2.exec_stmt elements_taptweak_ge e le m generator_scalar_split_call E0 le mf Out_normal /\
 scalar_at mf b0 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (literal_split128_low value)))) /\
 scalar_at mf b128 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) (literal_split128_high value)))) /\
 Mem.range_perm mf b0 0 32 Cur Freeable /\ Mem.range_perm mf b128 0 32 Cur Freeable /\
 Mem.nextblock mf=Mem.nextblock m /\
 (forall b pos k p,Mem.perm mf b pos k p <-> Mem.perm m b pos k p) /\
 lframe (fun b _=>b<>b0 /\ b<>b128 /\ b<>bs) m mf /\readonly_preserved m mf.
Proof.
 intros LowLocal HighLocal Symbol NG Separate LowSource HighSource LowFree HighFree Input.
 destruct (eval_scalar_split128_from_normalized_storage value m b0 b128 bs base
  Separate LowSource HighSource LowFree HighFree Input)
  as (mf & Call & Low & High & LF & HF & Frame).
 destruct (scalar_split128_permissions m mf _ _ Call) as (Blocks & Perms).
 pose proof(elements_taptweak_curve_transport _ _ m _ E0 mf _ elements_taptweak_has_scalar_split128 Call)as CallT.
 pose proof(elements_taptweak_internal_preserved _ _ m _ E0 mf _ elements_taptweak_has_scalar_split128 CallT)as Readonly.
 exists mf;split.
 - rewrite generator_scalar_split_call_source;eapply exec_elements_taptweak_arith_call with
    (vargs:=[Vptr b0 Ptrofs.zero;Vptr b128 Ptrofs.zero;Vptr bs (Ptrofs.repr base)]) (v:=Vundef).
   + exact elements_taptweak_has_scalar_split128.
   + exact Symbol.
   + eapply eval_Econs with (v1:=Vptr b0 Ptrofs.zero).
     * apply eval_Eaddrof;apply eval_Evar_local;exact LowLocal.
     * reflexivity.
     * eapply eval_Econs with (v1:=Vptr b128 Ptrofs.zero).
       -- apply eval_Eaddrof;apply eval_Evar_local;exact HighLocal.
       -- reflexivity.
       -- eapply eval_Econs with (v1:=Vptr bs (Ptrofs.repr base));
           [apply eval_Etempvar;exact NG|reflexivity|constructor].
   + exact CallT.
 - split;[exact Low|];split;[exact High|];split;[exact LF|];split;[exact HF|];
    split;[exact Blocks|];split;[exact Perms|].
   split;[|exact Readonly].
   eapply lframe_implies;[exact Frame|].
   intros b pos (L & H & S) Valid Foot;destruct (scalar_split128_foot_blocks b0 b128 bs base b pos Foot)
    as [Eq | [Eq | Eq]];contradiction.
Qed.
