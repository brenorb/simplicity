(** Evaluation of indexed fields of arrays of Bitcoin environment
    structures: pointer-plus-long arithmetic at the actual struct size. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Maps Memory Values Errors.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_field_eval.
Import Ctypes Values Mem ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge.
Set Default Timeout 30.

Lemma bitcoin_ptr_index_repr base sz n :
  0 <= base -> 0 < sz <= 1000 -> 0 <= n -> base + sz * n <= Ptrofs.max_unsigned ->
  Ptrofs.add (Ptrofs.repr base) (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_int64 (Int64.repr n))) =
    Ptrofs.repr (base + sz * n).
Proof.
  intros HB HS HN HM.
  assert (Hmax : Ptrofs.max_unsigned = 18446744073709551615) by reflexivity.
  rewrite Hmax in HM.
  assert (Hn : n <= 18446744073709551615) by nia.
  assert (Hsn : sz * n <= 18446744073709551615) by lia.
  assert (Hsn0 : 0 <= sz * n) by nia.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  unfold Ptrofs.mul, Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr sz) by (rewrite Hmax; lia).
  rewrite (Ptrofs.unsigned_repr n) by (rewrite Hmax; lia).
  rewrite (Ptrofs.unsigned_repr base) by (rewrite Hmax; lia).
  rewrite (Ptrofs.unsigned_repr (sz * n)) by (rewrite Hmax; lia).
  reflexivity.
Qed.

Lemma sem_add_ptr_long_sizeof ce S r ofs b sz m :
  sizeof ce S = sz ->
  sem_add ce (Vptr b ofs) (tptr S) (Vlong r) tulong m =
    Some (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr sz) (Ptrofs.of_int64 r)))).
Proof. intros H. unfold sem_add. simpl. unfold sem_add_ptr_long. rewrite H. reflexivity. Qed.

(** Dereference of [xp + ip] where [xp] is a pointer to [struct sid] and [ip : unsigned long] are temporaries. *)
Lemma eval_bitcoin_index e le m xp ip sid sz b base r :
  sizeof (Clight.genv_cenv bitcoin_ge) (Tstruct sid noattr) = sz ->
  le!xp = Some (Vptr b (Ptrofs.repr base)) -> le!ip = Some (Vlong (Int64.repr r)) ->
  0 <= base -> 0 < sz <= 1000 -> 0 <= r -> base + sz * r <= Ptrofs.max_unsigned ->
  eval_expr bitcoin_ge e le m
    (Ederef (Ebinop Oadd (Etempvar xp (tptr (Tstruct sid noattr))) (Etempvar ip tulong)
      (tptr (Tstruct sid noattr))) (Tstruct sid noattr))
    (Vptr b (Ptrofs.repr (base + sz * r))).
Proof.
  intros Hsz HX HI HB HS HR HM.
  rewrite <- (bitcoin_ptr_index_repr base sz r HB HS HR HM).
  eapply eval_Elvalue.
  - apply eval_Ederef. eapply eval_Ebinop.
    + apply eval_Etempvar; exact HX.
    + apply eval_Etempvar; exact HI.
    + cbn [typeof]. unfold sem_binary_operation.
      rewrite (sem_add_ptr_long_sizeof (Clight.genv_cenv bitcoin_ge) (Tstruct sid noattr)
        (Int64.repr r) (Ptrofs.repr base) b sz m Hsz). reflexivity.
  - apply deref_loc_copy; reflexivity.
Qed.

Lemma bitcoin_sizeof_sigInput : sizeof (Clight.genv_cenv bitcoin_ge) (Tstruct _sigInput noattr) = 160.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_sizeof_sigOutput : sizeof (Clight.genv_cenv bitcoin_ge) (Tstruct _sigOutput noattr) = 40.
Proof. vm_compute; reflexivity. Qed.

Lemma bitcoin_bitcoinTransaction_input : bitcoin_field_at _bitcoinTransaction _input 0.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_bitcoinTransaction_output : bitcoin_field_at _bitcoinTransaction _output 8.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_bitcoinTransaction_numInputs : bitcoin_field_at _bitcoinTransaction _numInputs 448.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_bitcoinTransaction_numOutputs : bitcoin_field_at _bitcoinTransaction _numOutputs 456.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_sigInput_txo : bitcoin_field_at _sigInput _txo 104.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_sigInput_sequence : bitcoin_field_at _sigInput _sequence 144.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_sigInput_prevOutpoint : bitcoin_field_at _sigInput _prevOutpoint 64.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_sigOutput_value : bitcoin_field_at _sigOutput _value 0.
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_sigOutput_scriptPubKey : bitcoin_field_at _sigOutput _scriptPubKey 8.
Proof. vm_compute; reflexivity. Qed.

(** [(xp[i]).field] for a scalar 64-bit field at offset [fdelta], index in temporary [ip]. *)
Lemma eval_bitcoin_elem_field_at e le m t4 ip sid sz field fdelta b inbase r v :
  sizeof (Clight.genv_cenv bitcoin_ge) (Tstruct sid noattr) = sz ->
  bitcoin_field_at sid field fdelta ->
  le!t4 = Some (Vptr b (Ptrofs.repr inbase)) -> le!ip = Some (Vlong r) ->
  0 <= inbase -> 0 < sz <= 1000 -> 0 <= fdelta ->
  inbase + sz * Int64.unsigned r + fdelta + 8 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m b (inbase + sz * Int64.unsigned r + fdelta) = Some (Vlong v) ->
  eval_expr bitcoin_ge e le m
    (Efield (Ederef (Ebinop Oadd (Etempvar t4 (tptr (Tstruct sid noattr))) (Etempvar ip tulong)
      (tptr (Tstruct sid noattr))) (Tstruct sid noattr)) field tulong) (Vlong v).
Proof.
  intros Hsz HF H4 HI HB HS Hd HM HL.
  assert (HR : 0 <= Int64.unsigned r) by (apply Int64.unsigned_range).
  assert (HI' : le!ip = Some (Vlong (Int64.repr (Int64.unsigned r)))) by (rewrite Int64.repr_unsigned; exact HI).
  assert (Hsr : 0 <= sz * Int64.unsigned r) by (apply Z.mul_nonneg_nonneg; [lia|exact HR]).
  pose proof (eval_bitcoin_index e le m t4 ip sid sz b inbase (Int64.unsigned r) Hsz H4 HI' HB HS HR
    ltac:(clear - HM Hd Hsr; lia)) as HElem.
  eapply eval_bitcoin_field_value with (sid := sid) (delta := fdelta) (chunk := Mint64).
  - reflexivity.
  - exact HF.
  - reflexivity.
  - exact HElem.
  - rewrite bitcoin_ptr_add_repr by (clear - HM Hd Hsr HB; lia).
    apply bitcoin_loadv_repr; [clear - HM Hd Hsr HB; lia|exact HL].
Qed.

Lemma eval_bitcoin_elem_field e le m t4 sid sz field fdelta b inbase r v :
  sizeof (Clight.genv_cenv bitcoin_ge) (Tstruct sid noattr) = sz ->
  bitcoin_field_at sid field fdelta ->
  le!t4 = Some (Vptr b (Ptrofs.repr inbase)) -> le!_i = Some (Vlong r) ->
  0 <= inbase -> 0 < sz <= 1000 -> 0 <= fdelta ->
  inbase + sz * Int64.unsigned r + fdelta + 8 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m b (inbase + sz * Int64.unsigned r + fdelta) = Some (Vlong v) ->
  eval_expr bitcoin_ge e le m
    (Efield (Ederef (Ebinop Oadd (Etempvar t4 (tptr (Tstruct sid noattr))) (Etempvar _i tulong)
      (tptr (Tstruct sid noattr))) (Tstruct sid noattr)) field tulong) (Vlong v).
Proof. intros. eapply eval_bitcoin_elem_field_at; eassumption. Qed.

(** [(xp[i]).f1.f2] where [f1] is a struct-valued field. *)
Lemma eval_bitcoin_elem_nested_field_at e le m t4 ip sid sz f1 d1 sid1 f2 d2 b inbase r v :
  sizeof (Clight.genv_cenv bitcoin_ge) (Tstruct sid noattr) = sz ->
  bitcoin_field_at sid f1 d1 -> bitcoin_field_at sid1 f2 d2 ->
  le!t4 = Some (Vptr b (Ptrofs.repr inbase)) -> le!ip = Some (Vlong r) ->
  0 <= inbase -> 0 < sz <= 1000 -> 0 <= d1 -> 0 <= d2 ->
  inbase + sz * Int64.unsigned r + d1 + d2 + 8 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m b (inbase + sz * Int64.unsigned r + (d1 + d2)) = Some (Vlong v) ->
  eval_expr bitcoin_ge e le m
    (Efield (Efield (Ederef (Ebinop Oadd (Etempvar t4 (tptr (Tstruct sid noattr))) (Etempvar ip tulong)
      (tptr (Tstruct sid noattr))) (Tstruct sid noattr)) f1 (Tstruct sid1 noattr)) f2 tulong) (Vlong v).
Proof.
  intros Hsz HF1 HF2 H4 HI HB HS Hd1 Hd2 HM HL.
  assert (HR : 0 <= Int64.unsigned r) by (apply Int64.unsigned_range).
  assert (HI' : le!ip = Some (Vlong (Int64.repr (Int64.unsigned r)))) by (rewrite Int64.repr_unsigned; exact HI).
  assert (Hsr : 0 <= sz * Int64.unsigned r) by (apply Z.mul_nonneg_nonneg; [lia|exact HR]).
  pose proof (eval_bitcoin_index e le m t4 ip sid sz b inbase (Int64.unsigned r) Hsz H4 HI' HB HS HR
    ltac:(clear - HM Hd1 Hd2 Hsr; lia)) as HElem.
  eapply eval_bitcoin_field_value with (sid := sid1) (delta := d2) (chunk := Mint64).
  - reflexivity.
  - exact HF2.
  - reflexivity.
  - eapply eval_bitcoin_field_struct; [reflexivity|exact HF1|exact HElem].
  - rewrite bitcoin_ptr_add_repr by (clear - HM Hd1 Hd2 Hsr HB; lia).
    rewrite bitcoin_ptr_add_repr by (clear - HM Hd1 Hd2 Hsr HB; lia).
    apply bitcoin_loadv_repr; [clear - HM Hd1 Hd2 Hsr HB; lia|].
    replace (inbase + sz * Int64.unsigned r + d1 + d2) with (inbase + sz * Int64.unsigned r + (d1 + d2)) by lia.
    exact HL.
Qed.

(** [&(xp[i]).field] for a struct-valued field. *)
Lemma eval_bitcoin_elem_field_addr e le m t4 ip sid sz field fdelta sid1 b inbase r :
  sizeof (Clight.genv_cenv bitcoin_ge) (Tstruct sid noattr) = sz ->
  bitcoin_field_at sid field fdelta ->
  le!t4 = Some (Vptr b (Ptrofs.repr inbase)) -> le!ip = Some (Vlong r) ->
  0 <= inbase -> 0 < sz <= 1000 -> 0 <= fdelta ->
  inbase + sz * Int64.unsigned r + fdelta <= Ptrofs.max_unsigned ->
  inbase + sz * Int64.unsigned r + 1 <= Ptrofs.max_unsigned ->
  eval_expr bitcoin_ge e le m
    (Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar t4 (tptr (Tstruct sid noattr))) (Etempvar ip tulong)
      (tptr (Tstruct sid noattr))) (Tstruct sid noattr)) field (Tstruct sid1 noattr))
      (tptr (Tstruct sid1 noattr)))
    (Vptr b (Ptrofs.repr (inbase + sz * Int64.unsigned r + fdelta))).
Proof.
  intros Hsz HF H4 HI HB HS Hd HM HM1.
  assert (HR : 0 <= Int64.unsigned r) by (apply Int64.unsigned_range).
  assert (HI' : le!ip = Some (Vlong (Int64.repr (Int64.unsigned r)))) by (rewrite Int64.repr_unsigned; exact HI).
  assert (Hsr : 0 <= sz * Int64.unsigned r) by (apply Z.mul_nonneg_nonneg; [lia|exact HR]).
  pose proof (eval_bitcoin_index e le m t4 ip sid sz b inbase (Int64.unsigned r) Hsz H4 HI' HB HS HR
    ltac:(clear - HM1 Hsr; lia)) as HElem.
  eapply eval_Eaddrof.
  rewrite <- (bitcoin_ptr_add_repr (inbase + sz * Int64.unsigned r) fdelta) by (clear - HM Hd Hsr HB; lia).
  eapply eval_bitcoin_field_lvalue; [reflexivity|exact HF|exact HElem].
Qed.
