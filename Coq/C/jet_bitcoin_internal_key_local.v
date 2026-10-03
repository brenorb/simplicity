(** Actual Bitcoin internal_key jet against the extended primitive
    InternalKey: [writeHash(dst, &env->taproot->internalKey)]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_wrapper C.jet_bitcoin_hash_getters.
Require Import C.jet_bitcoin_script_cmr_local C.jet_bitcoin_hash_getter_local C.jet_bitcoin_hash_getter_writehash C.jet_bitcoin_ext_prim.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Import PrimitiveBitcoinExt.Primitive.Coercions.
Import PrimitiveBitcoinExt.Primitive.CanonicalStructures.
Set Default Timeout 60.

Definition bitcoin_internal_key_spec {alg : PrimitiveBitcoinExt.Primitive.Algebra} : alg Ty.Unit Word256 :=
  PrimitiveBitcoinExt.Primitive.Combinators.prim BitcoinExt.InternalKey.

Lemma bitcoin_internal_key_spec_sem (environment : ext_environment) :
  @bitcoin_internal_key_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) tt environment =
    Some (from_hash256 (extInternalKey environment)).
Proof. reflexivity. Qed.

Lemma bitcoin_internal_key_getter_body :
  bitcoin_wrapper_shape f_simplicity_bitcoin_internal_key (bitcoin_simple_rest
    (bitcoin_hash_mid_writeHash _taproot _bitcoinTapEnv _internalKey)).
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma bitcoin_internal_key_at : bitcoin_field_at _bitcoinTapEnv _internalKey 104.
Proof. vm_compute; reflexivity. Qed.

Theorem bitcoin_internal_key_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_internal_key bitcoin_ge ext_environment Ty.Unit Word256
    (hash_getter_rep extInternalKey 8 104 176)
    (fun a environment => @bitcoin_internal_key_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply bitcoin_hash_getter_writeHash_local with (ptrfield := _taproot) (sid := _bitcoinTapEnv)
    (hashfield := _internalKey).
  - intros e. reflexivity.
  - exact bitcoin_internal_key_getter_body.
  - exact bitcoin_txEnv_taproot.
  - exact bitcoin_internal_key_at.
  - lia.
  - lia.
Qed.
