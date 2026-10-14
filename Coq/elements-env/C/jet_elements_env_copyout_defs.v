(** [copyOutput(result, allocation, allocationLen, output)]
    (elements/env.c): the layout of [sigOutput] and [rawElementsOutput] and
    the ten statements of the body. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_add_n_init.
Require Import C.jet_elements_env_field_eval.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.

Notation SOUT := (Tstruct _sigOutput noattr).
Notation ROUT := (Tstruct _rawElementsOutput noattr).
Notation RBUF := (Tstruct _rawElementsBuffer noattr).

Lemma envu_sout_asset : envu_field_at _sigOutput _asset 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sout_surjectionProofHash : envu_field_at _sigOutput _surjectionProofHash 36.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sout_rangeProofHash : envu_field_at _sigOutput _rangeProofHash 68.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sout_amt : envu_field_at _sigOutput _amt 104.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sout_nonce : envu_field_at _sigOutput _nonce 144.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sout_scriptPubKey : envu_field_at _sigOutput _scriptPubKey 180.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sout_assetFee : envu_field_at _sigOutput _assetFee 216.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sout_pnd : envu_field_at _sigOutput _pnd 224.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sout_isNullData : envu_field_at _sigOutput _isNullData 240.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sout_emptyScript : envu_field_at _sigOutput _emptyScript 241.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.

Lemma envu_rout_asset : envu_field_at _rawElementsOutput _asset 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rout_value : envu_field_at _rawElementsOutput _value 8.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rout_nonce : envu_field_at _rawElementsOutput _nonce 16.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rout_scriptPubKey : envu_field_at _rawElementsOutput _scriptPubKey 24.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rout_surjectionProof : envu_field_at _rawElementsOutput _surjectionProof 40.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rout_rangeProof : envu_field_at _rawElementsOutput _rangeProof 56.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.

Lemma co_sizeof_SOUT : sizeof sha_ge SOUT = 248.
Proof. vm_compute. reflexivity. Qed.
Lemma co_sizeof_ROUT : sizeof sha_ge ROUT = 72.
Proof. vm_compute. reflexivity. Qed.

Ltac co_stmt k :=
  let b := eval cbv delta [f_copyOutput fn_body] beta iota in (fn_body f_copyOutput) in
  lazymatch b with
  | Ssequence ?s1 (Ssequence ?s2 (Ssequence ?s3 (Ssequence ?s4 (Ssequence ?s5 (Ssequence ?s6
      (Ssequence ?s7 (Ssequence ?s8 (Ssequence ?s9 ?s10)))))))) =>
      lazymatch k with
      | 1%nat => exact s1 | 2%nat => exact s2 | 3%nat => exact s3 | 4%nat => exact s4 | 5%nat => exact s5
      | 6%nat => exact s6 | 7%nat => exact s7 | 8%nat => exact s8 | 9%nat => exact s9 | 10%nat => exact s10
      end
  end.

Definition co_s1 : statement := ltac:(co_stmt 1%nat).
Definition co_s2 : statement := ltac:(co_stmt 2%nat).
Definition co_s3 : statement := ltac:(co_stmt 3%nat).
Definition co_s4 : statement := ltac:(co_stmt 4%nat).
Definition co_s5 : statement := ltac:(co_stmt 5%nat).
Definition co_s6 : statement := ltac:(co_stmt 6%nat).
Definition co_s7 : statement := ltac:(co_stmt 7%nat).
Definition co_s8 : statement := ltac:(co_stmt 8%nat).
Definition co_s9 : statement := ltac:(co_stmt 9%nat).
Definition co_s10 : statement := ltac:(co_stmt 10%nat).

Lemma copyOutput_body_shape :
  fn_body f_copyOutput =
    Ssequence co_s1 (Ssequence co_s2 (Ssequence co_s3 (Ssequence co_s4 (Ssequence co_s5 (Ssequence co_s6
      (Ssequence co_s7 (Ssequence co_s8 (Ssequence co_s9 co_s10)))))))).
Proof. reflexivity. Qed.

(** The two proof-hash statements: [hashBuffer(&result->fld, is_confidential(result->src.prefix) ? &output->prf : &(rawElementsBuffer){0})]. *)
Definition co_proof_stmt (tp tc tb : ident) (src fld prf cid : ident) (srcty : type) : statement :=
  Ssequence
    (Ssequence
      (Ssequence
        (Sset tp (Efield (Efield (Ederef (Etempvar _result (tptr SOUT)) SOUT) src srcty) _prefix tint))
        (Scall (Some tc) (Evar _is_confidential (Tfunction (Tcons tint Tnil) tbool cc_default))
           [Etempvar tp tint]))
      (Sifthenelse (Etempvar tc tbool)
        (Sset tb (Ecast (Eaddrof (Efield (Ederef (Etempvar _output (tptr ROUT)) ROUT) prf RBUF) (tptr RBUF))
                    (tptr RBUF)))
        (Ssequence
          (Ssequence
            (Sassign (Efield (Evar cid RBUF) _buf (tptr tuchar)) (Econst_int (Int.repr 0) tint))
            (Sassign (Efield (Evar cid RBUF) _len tuint) (Econst_int (Int.repr 0) tint)))
          (Sset tb (Ecast (Eaddrof (Evar cid RBUF) (tptr RBUF)) (tptr RBUF))))))
    (Scall None
      (Evar _hashBuffer (Tfunction (Tcons (tptr (Tstruct _sha256_midstate noattr)) (Tcons (tptr RBUF) Tnil))
                           tvoid cc_default))
      [Eaddrof (Efield (Ederef (Etempvar _result (tptr SOUT)) SOUT) fld (Tstruct _sha256_midstate noattr))
         (tptr (Tstruct _sha256_midstate noattr)); Etempvar tb (tptr RBUF)]).

Lemma co_s8_shape :
  co_s8 = co_proof_stmt _t'6 _t'1 _t'2 _asset _surjectionProofHash _surjectionProof ___compound
            (Tstruct _confidential noattr).
Proof. reflexivity. Qed.

Lemma co_s9_shape :
  Ssequence co_s9 co_s10 =
    Ssequence (co_proof_stmt _t'5 _t'3 _t'4 _amt _rangeProofHash _rangeProof ___compound__1
                 (Tstruct _confAmount noattr))
      (Sassign (Efield (Ederef (Etempvar _result (tptr SOUT)) SOUT) _assetFee tulong)
         (Econst_int (Int.repr 0) tint)).
Proof. reflexivity. Qed.
