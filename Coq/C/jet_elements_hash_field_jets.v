(** Elements jets that write a 256-bit field reached through one pointer of
    the environment: [transaction_id] ([env->tx->txid]) and [internal_key]
    ([env->taproot->internalKey]), against primitives TransactionId and
    InternalKey (Haskell: [specificationTransaction X = primitive Prim.X]).

    The environment relation states that the C field holds the 256-bit value
    the primitive denotes.  For [transaction_id] that value is [txid] of the
    logical transaction: the relation is an initial representation
    requirement on the environment (the C constructor caches it); nothing
    here proves that [env.c] computes it. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option C.jet_elements_prim.
Require Import C.jet_application_sep C.jets_elements C.jet_elements_linkage.
Require Import C.jet_elements_field_eval C.jet_elements_wrapper C.jet_elements_hash_getters.
Require Import C.jet_elements_script_cmr_local C.jet_elements_hash_getter_local.
Require Import C.jet_elements_hash_getter_writehash.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 60.

Ltac getter_body :=
  repeat split; try reflexivity;
  intros x y HX HY Hxy; cbn in HX, HY;
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].

(** ** transaction_id *)

Definition elements_transaction_id_spec {alg : Primitive.Algebra} : alg Ty.Unit Word256 :=
  Primitive.Combinators.prim Elements.TransactionId.

Lemma elements_transaction_id_spec_parametric :
  Primitive.Parametric (@elements_transaction_id_spec).
Proof. intros alg1 alg2 R. apply prim_Parametric. Qed.

Lemma elements_transaction_id_getter_body :
  elements_wrapper_shape f_simplicity_transaction_id (elements_simple_rest
    (elements_hash_mid_write32s _tx _elementsTransaction _txid)).
Proof. getter_body. Qed.

Lemma elements_transaction_txid_at : elements_field_at _elementsTransaction _txid 664.
Proof. vm_compute; reflexivity. Qed.

Theorem elements_transaction_id_local_spec :
  application_jet_local_spec_sep f_simplicity_transaction_id elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => txid (Elements.envTx e)) 0 664 760)
    (fun a environment => @elements_transaction_id_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply elements_hash_getter_write32s_local with (ptrfield := _tx) (sid := _elementsTransaction)
    (hashfield := _txid).
  - intros e. reflexivity.
  - exact elements_transaction_id_getter_body.
  - exact elements_txEnv_tx.
  - exact elements_transaction_txid_at.
  - lia.
  - lia.
Qed.

(** ** internal_key *)

Definition elements_internal_key_spec {alg : Primitive.Algebra} : alg Ty.Unit Word256 :=
  Primitive.Combinators.prim Elements.InternalKey.

Lemma elements_internal_key_spec_parametric :
  Primitive.Parametric (@elements_internal_key_spec).
Proof. intros alg1 alg2 R. apply prim_Parametric. Qed.

Lemma elements_internal_key_getter_body :
  elements_wrapper_shape f_simplicity_internal_key (elements_simple_rest
    (elements_hash_mid_writeHash _taproot _elementsTapEnv _internalKey)).
Proof. getter_body. Qed.

Theorem elements_internal_key_local_spec :
  application_jet_local_spec_sep f_simplicity_internal_key elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => tapInternalKey (Elements.envTap e)) 8 104 176)
    (fun a environment => @elements_internal_key_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply elements_hash_getter_writeHash_local with (ptrfield := _taproot) (sid := _elementsTapEnv)
    (hashfield := _internalKey).
  - intros e. reflexivity.
  - exact elements_internal_key_getter_body.
  - exact elements_txEnv_taproot.
  - exact elements_tapEnv_internalKey.
  - lia.
  - lia.
Qed.
