(** Actual point-negation entry and generated flag load/store prefix. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_gej_flag_read.
Require Import C.jet_secp_gej_read_flag_store.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition gej_negate_helper_temps b base : temp_env :=
  PTree.set _a (Vptr b (Ptrofs.repr base))
    (PTree.set _r (Vptr b (Ptrofs.repr base))
      (create_undef_temps (fn_temps f_secp256k1_gej_neg))).
Lemma gej_negate_helper_entry m b base :
  function_entry2 secp_ge f_secp256k1_gej_neg
    [Vptr b (Ptrofs.repr base); Vptr b (Ptrofs.repr base)] m
    empty_env (gej_negate_helper_temps b base) m.
Proof.
  constructor.
  - constructor.
  - repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY HE; cbn in HX,HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in HE;discriminate|congruence].
  - constructor.
  - reflexivity.
Qed.
Lemma gej_negate_helper_temp_r b base :
  (gej_negate_helper_temps b base)!_r = Some (Vptr b (Ptrofs.repr base)).
Proof.
  unfold gej_negate_helper_temps; rewrite PTree.gso by discriminate; apply PTree.gss.
Qed.
Lemma gej_negate_helper_temp_a b base :
  (gej_negate_helper_temps b base)!_a = Some (Vptr b (Ptrofs.repr base)).
Proof. unfold gej_negate_helper_temps; apply PTree.gss. Qed.

Definition gej_negate_flag_prefix : statement :=
  Ssequence
    (Sset _t'1
      (Efield (Ederef (Etempvar _a (tptr (Tstruct __6123 noattr)))
        (Tstruct __6123 noattr)) _infinity tint))
    (Sassign
      (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
        (Tstruct __6123 noattr)) _infinity tint)
      (Etempvar _t'1 tint)).

Theorem exec_gej_negate_flag_owned le m b base flag :
  0 <= base -> (8 | base) -> base+128 <= Ptrofs.max_unsigned ->
  le!_r = Some (Vptr b (Ptrofs.repr base)) ->
  le!_a = Some (Vptr b (Ptrofs.repr base)) ->
  Mem.range_perm m b base (base+128) Cur Freeable ->
  Mem.load Mint32 m b (base+120) = Some (Vint flag) ->
  exists mi,
    Clight2.exec_stmt secp_ge empty_env le m gej_negate_flag_prefix E0
      (PTree.set _t'1 (Vint flag) le) mi Out_normal /\
    Mem.load Mint32 mi b (base+120) = Some (Vint flag) /\
    Mem.range_perm mi b base (base+128) Cur Freeable /\
    (forall chunk b' ofs,
      b' <> b \/ ofs+size_chunk chunk <= base+120 \/ base+124 <= ofs ->
      Mem.load chunk mi b' ofs = Mem.load chunk m b' ofs) /\
    (forall b' ofs k p, Mem.perm mi b' ofs k p <-> Mem.perm m b' ofs k p) /\
    (forall b', Mem.valid_block m b' -> Mem.valid_block mi b').
Proof.
  intros HB HA HM HR HS HP HL.
  assert (HR' : (PTree.set _t'1 (Vint flag) le)!_r =
    Some (Vptr b (Ptrofs.repr base))).
  { rewrite PTree.gso by discriminate; exact HR. }
  destruct (exec_gej_read_flag_owned (PTree.set _t'1 (Vint flag) le)
    m b base flag HB HA HM HR' ltac:(apply PTree.gss) HP)
    as (mi & HStore & HFlag & HPerm & HLoads & HPerms & HValid).
  exists mi; split.
  - unfold gej_negate_flag_prefix.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _t'1 (Vint flag) le).
    + apply exec_Sset. eapply eval_gej_flag_load; eassumption.
    + exact HStore.
  - split; [exact HFlag|]. split; [exact HPerm|].
    split; [exact HLoads|]. split; assumption.
Qed.
Print Assumptions gej_negate_helper_entry.
Timeout 60 Print Assumptions exec_gej_negate_flag_owned.
