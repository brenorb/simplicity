(** The original lookup_fee midpoint load and memcmp, under the existing
    explicit libc contract. No fee-classification/specification claim. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clightdefs Clight ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval C.jet_elements_index_eval.
Require Import C.jet_elements_asset_helper C.jet_elements_fee_flag_exec C.jet_memcmp_model.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition fee_lookup_half := Ebinop Odiv (Etempvar _len tulong) (Econst_int (Int.repr 2) tint) tulong.
Definition fee_lookup_mid := Ederef
  (Ebinop Oadd (Etempvar _feeOutputs (tptr (tptr (Tstruct _sigOutput noattr)))) fee_lookup_half
    (tptr (tptr (Tstruct _sigOutput noattr)))) (tptr (Tstruct _sigOutput noattr)).
Definition fee_lookup_key := Efield
  (Ederef (Etempvar _assetid (tptr (Tstruct _sha256_midstate noattr))) (Tstruct _sha256_midstate noattr))
  _s (tarray tuint 8).
Definition fee_lookup_candidate := Efield
  (Efield (Efield
    (Ederef (Etempvar _t'4 (tptr (Tstruct _sigOutput noattr))) (Tstruct _sigOutput noattr))
    _asset (Tstruct _confidential noattr)) _data (Tstruct _sha256_midstate noattr)) _s (tarray tuint 8).
Definition fee_lookup_memcmp := Scall (Some _t'1)
  (Evar _memcmp (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) tint cc_default))
  [fee_lookup_key;fee_lookup_candidate;Esizeof (tarray tuint 8) tulong].
Definition fee_lookup_compare := Ssequence
  (Ssequence (Sset _t'4 fee_lookup_mid) fee_lookup_memcmp) (Sset _cmp (Etempvar _t'1 tint)).
Definition fee_lookup_work := match fn_body f_lookup_fee with
  Ssequence (Sloop (Ssequence _ s) _) _=>s | _=>Sskip end.
Definition fee_lookup_after_compare := match fee_lookup_work with Ssequence _ s=>s | _=>Sskip end.
Lemma fee_lookup_compare_source : fee_lookup_work=Ssequence fee_lookup_compare fee_lookup_after_compare.
Proof. reflexivity. Qed.

Lemma fee_lookup_memcmp_symbol : Genv.find_symbol (Clight.genv_genv elements_ge) _memcmp=
  Some(elements_symbol_block _memcmp).
Proof. vm_compute;reflexivity. Qed.
Lemma fee_lookup_memcmp_funct : Genv.find_funct (Clight.genv_genv elements_ge)
  (Vptr(elements_symbol_block _memcmp) Ptrofs.zero)=
  Some(External (EF_external "memcmp" memcmp_sig)
    (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) tint cc_default).
Proof. vm_compute;reflexivity. Qed.

Lemma fee_lookup_div_sem len m : 0<=len<=Int64.max_unsigned ->
  sem_binary_operation elements_ge Odiv (Vlong(Int64.repr len)) tulong (Vint(Int.repr 2)) tint m=
    Some(Vlong(Int64.repr(len/2))).
Proof.
  intro Len;change (Some(Vlong(Int64.divu (Int64.repr len) (Int64.repr 2)))=Some(Vlong(Int64.repr(len/2)))).
  unfold Int64.divu;rewrite Int64.unsigned_repr by exact Len;reflexivity.
Qed.

Lemma eval_fee_lookup_half e le m len : le!_len=Some(Vlong(Int64.repr len)) ->
  0<=len<=Int64.max_unsigned -> eval_expr elements_ge e le m fee_lookup_half (Vlong(Int64.repr(len/2))).
Proof.
  intros Length Len;unfold fee_lookup_half;eapply eval_Ebinop.
  - apply eval_Etempvar;exact Length.
  - apply eval_Econst_int.
  - apply fee_lookup_div_sem;exact Len.
Qed.

Lemma eval_fee_lookup_mid e le m len bt base bp ofs :
  le!_len=Some(Vlong(Int64.repr len)) -> le!_feeOutputs=Some(Vptr bt (Ptrofs.repr base)) ->
  0<=len<=Int64.max_unsigned -> 0<=base -> base+8*(len/2)<=Ptrofs.max_unsigned ->
  Mem.load Mptr m bt (base+8*(len/2))=Some(Vptr bp (Ptrofs.repr ofs)) ->
  eval_expr elements_ge e le m fee_lookup_mid (Vptr bp (Ptrofs.repr ofs)).
Proof.
  intros Length Table Len Base Max Load;unfold fee_lookup_mid;eapply eval_Elvalue.
  - apply eval_Ederef;eapply eval_Ebinop.
    + apply eval_Etempvar;exact Table.
    + apply eval_fee_lookup_half with (len:=len);assumption.
    + cbn [typeof fee_lookup_half];unfold sem_binary_operation.
      rewrite (sem_add_ptr_long_sizeof (Clight.genv_cenv elements_ge) (tptr (Tstruct _sigOutput noattr))
        (Int64.repr(len/2)) (Ptrofs.repr base) bt 8 m eq_refl).
      rewrite elements_ptr_index_repr;[reflexivity|exact Base|lia|apply Z.div_pos;lia|exact Max].
  - eapply deref_loc_value with (chunk:=Mptr);[reflexivity|].
    apply elements_loadv_repr;[pose proof (Z.div_pos len 2 ltac:(lia) ltac:(lia));lia|exact Load].
Qed.

Lemma eval_fee_lookup_key e le m b ofs : le!_assetid=Some(Vptr b ofs) ->
  eval_expr elements_ge e le m fee_lookup_key (Vptr b ofs).
Proof.
  intro Key;replace ofs with (Ptrofs.add ofs (Ptrofs.repr 0)) at 1 by apply Ptrofs.add_zero.
  unfold fee_lookup_key;eapply eval_elements_field_array with (sid:=_sha256_midstate) (delta:=0).
  - reflexivity.
  - exact elements_midstate_s.
  - intros;discriminate.
  - reflexivity.
  - apply eval_elements_deref_struct;exact Key.
Qed.

Lemma eval_fee_lookup_candidate e le m b ofs : le!_t'4=Some(Vptr b ofs) ->
  eval_expr elements_ge e le m fee_lookup_candidate (Vptr b ofs).
Proof.
  intro Candidate.
  replace ofs with (Ptrofs.add (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr 0)) (Ptrofs.repr 0)) (Ptrofs.repr 0))
    at 1 by (change (Ptrofs.repr 0) with Ptrofs.zero;rewrite !Ptrofs.add_zero;reflexivity).
  unfold fee_lookup_candidate;eapply eval_elements_field_array with (sid:=_sha256_midstate) (delta:=0).
  - reflexivity.
  - exact elements_midstate_s.
  - intros;discriminate.
  - reflexivity.
  - eapply eval_elements_field_struct with (sid:=_confidential) (delta:=0).
    + reflexivity.
    + exact elements_confidential_data.
    + eapply eval_elements_field_struct with (sid:=_sigOutput) (delta:=0).
      * reflexivity.
      * exact fee_asset_field.
      * apply eval_elements_deref_struct;exact Candidate.
Qed.

Definition fee_lookup_compared bp ofs cmp le := PTree.set _cmp (Vint cmp)
  (PTree.set _t'1 (Vint cmp) (PTree.set _t'4 (Vptr bp (Ptrofs.repr ofs)) le)).

Theorem exec_fee_lookup_compare (Model : memcmp_model) le m len bt base bk keybase bp ofs key candidate :
  le!_len=Some(Vlong(Int64.repr len)) -> le!_feeOutputs=Some(Vptr bt (Ptrofs.repr base)) ->
  le!_assetid=Some(Vptr bk (Ptrofs.repr keybase)) ->
  0<=len<=Int64.max_unsigned -> 0<=base -> base+8*(len/2)<=Ptrofs.max_unsigned ->
  0<=keybase -> keybase+32<=Ptrofs.max_unsigned+1 -> 0<=ofs -> ofs+32<=Ptrofs.max_unsigned+1 ->
  Mem.load Mptr m bt (base+8*(len/2))=Some(Vptr bp (Ptrofs.repr ofs)) ->
  length key=32%nat -> length candidate=32%nat ->
  bytes_at m bk keybase key -> bytes_at m bp ofs candidate -> exists cmp,
  Clight2.exec_stmt elements_ge empty_env le m fee_lookup_compare E0 (fee_lookup_compared bp ofs cmp le) m Out_normal /\
  memcmp_sign (bytes_cmp key candidate) cmp.
Proof.
  intros Length Table Key Len Base Max K0 KMax C0 CMax Load KeyLen CandidateLen KeyBytes CandidateBytes.
  destruct (Model (Clight.genv_genv elements_ge) m bk (Ptrofs.repr keybase) bp (Ptrofs.repr ofs) key candidate)
    as (cmp & Call & Sign).
  - congruence.
  - rewrite KeyLen;change (32<=18446744073709551615);lia.
  - rewrite KeyLen,Ptrofs.unsigned_repr by lia;exact KMax.
  - rewrite KeyLen,Ptrofs.unsigned_repr by lia;exact CMax.
  - rewrite Ptrofs.unsigned_repr by lia;exact KeyBytes.
  - rewrite Ptrofs.unsigned_repr by lia;exact CandidateBytes.
  - exists cmp;split;[|exact Sign].
    set (la:=PTree.set _t'4 (Vptr bp (Ptrofs.repr ofs)) le).
    set (lb:=PTree.set _t'1 (Vint cmp) la).
    assert (Compare : Clight2.exec_stmt elements_ge empty_env la m fee_lookup_memcmp E0 lb m Out_normal).
    { unfold fee_lookup_memcmp,lb;eapply exec_Scall with
        (vf:=Vptr(elements_symbol_block _memcmp) Ptrofs.zero)
        (vargs:=[Vptr bk (Ptrofs.repr keybase);Vptr bp (Ptrofs.repr ofs);Vlong(Int64.repr 32)])
        (vres:=Vint cmp).
      - reflexivity.
      - eapply eval_Elvalue;[apply eval_Evar_global;[reflexivity|exact fee_lookup_memcmp_symbol]|].
        apply deref_loc_reference;reflexivity.
      - eapply eval_Econs.
        + apply eval_fee_lookup_key;unfold la;rewrite PTree.gso by discriminate;exact Key.
        + reflexivity.
        + eapply eval_Econs.
          * apply eval_fee_lookup_candidate;unfold la;apply PTree.gss.
          * reflexivity.
          * eapply eval_Econs;[apply eval_Esizeof|reflexivity|constructor].
      - exact fee_lookup_memcmp_funct.
      - reflexivity.
      - apply eval_funcall_external;rewrite KeyLen in Call;exact Call. }
    unfold fee_lookup_compare,fee_lookup_compared.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lb) (m1:=m).
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=la) (m1:=m);[|exact Compare].
      apply exec_Sset;apply eval_fee_lookup_mid with (bt:=bt) (base:=base) (len:=len);assumption.
    + apply exec_Sset;apply eval_Etempvar;unfold lb;apply PTree.gss.
Qed.
