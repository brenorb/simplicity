(** Actual taken-loop body: load and decrement the eight-byte quotient slot,
    then update rh and d. The whole helper must derive the store premise and
    compose this body with its guard and bounded loop; no jet coverage here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_divmod96_expr.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divmod96_correction_stmt :=
  Ssequence
    (Ssequence
      (Sset _t'3 (Ederef (Etempvar _q (tptr tulong)) tulong))
      (Sassign (Ederef (Etempvar _q (tptr tulong)) tulong)
        (Ebinop Osub (Etempvar _t'3 tulong) (Econst_int Int.one tint) tulong)))
    (Ssequence
      (Sset _rh (Ebinop Oadd (Etempvar _rh tulong) (Etempvar _bh tulong) tulong))
      (Sset _d (Ebinop Osub (Etempvar _d tulong) (Etempvar _bl tulong) tulong))).

Lemma eval_divmod96_quotient e le m bq ofs q :
  le!_q = Some (Vptr bq ofs) -> Mem.load Mint64 m bq (Ptrofs.unsigned ofs) = Some (Vlong q) ->
  eval_expr ge0 e le m (Ederef (Etempvar _q (tptr tulong)) tulong) (Vlong q).
Proof.
  intros HQ HL. eapply eval_Elvalue.
  - apply eval_Ederef. apply eval_Etempvar; exact HQ.
  - apply deref_loc_value with (chunk := Mint64); [reflexivity|exact HL].
Qed.

Lemma exec_divmod96_correction_stmt e le m ms bq ofs q rh bh d bl :
  le!_q = Some (Vptr bq ofs) -> le!_rh = Some (Vlong rh) -> le!_bh = Some (Vlong bh) ->
  le!_d = Some (Vlong d) -> le!_bl = Some (Vlong bl) ->
  Mem.load Mint64 m bq (Ptrofs.unsigned ofs) = Some (Vlong q) ->
  Mem.store Mint64 m bq (Ptrofs.unsigned ofs) (Vlong (Int64.sub q Int64.one)) = Some ms ->
  Clight2.exec_stmt ge0 e le m divmod96_correction_stmt E0
    (PTree.set _d (Vlong (Int64.sub d bl))
      (PTree.set _rh (Vlong (Int64.add rh bh)) (PTree.set _t'3 (Vlong q) le))) ms Out_normal.
Proof.
  intros HQ HR HB HD HBL HL HS.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ms)
    (le1 := PTree.set _t'3 (Vlong q) le).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
    + apply exec_set. eapply eval_divmod96_quotient; eauto.
    + eapply exec_Sassign with (loc := bq) (ofs := ofs) (bf := Full)
        (v2 := Vlong (Int64.sub q Int64.one)) (v := Vlong (Int64.sub q Int64.one)).
      * apply eval_Ederef. apply eval_Etempvar. rewrite PTree.gso by discriminate. exact HQ.
      * eapply eval_Ebinop with (v1 := Vlong q) (v2 := Vint Int.one).
        -- apply eval_Etempvar. rewrite PTree.gss. reflexivity.
        -- apply eval_Econst_int.
        -- reflexivity.
      * reflexivity.
      * apply assign_loc_value with (chunk := Mint64); [reflexivity|exact HS].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ms).
    + apply exec_set. eapply eval_Ebinop with (v1 := Vlong rh) (v2 := Vlong bh).
      * apply eval_Etempvar. rewrite PTree.gso by discriminate. exact HR.
      * apply eval_Etempvar. rewrite PTree.gso by discriminate. exact HB.
      * reflexivity.
    + apply exec_set. eapply eval_Ebinop with (v1 := Vlong d) (v2 := Vlong bl).
      * apply eval_Etempvar. rewrite !PTree.gso by discriminate. exact HD.
      * apply eval_Etempvar. rewrite !PTree.gso by discriminate. exact HBL.
      * reflexivity.
Qed.

Lemma divmod96_machine_step_values q rh bh d bl :
  0 < Int64.unsigned q ->
  Int64.unsigned rh + Int64.unsigned bh < Int64.modulus ->
  Int64.unsigned bl <= Int64.unsigned d ->
  Int64.unsigned (Int64.sub q Int64.one) = Int64.unsigned q - 1 /\
  Int64.unsigned (Int64.add rh bh) = Int64.unsigned rh + Int64.unsigned bh /\
  Int64.unsigned (Int64.sub d bl) = Int64.unsigned d - Int64.unsigned bl.
Proof.
  intros HQ Hsum Hdiff. pose proof (Int64.unsigned_range q).
  pose proof (Int64.unsigned_range rh). pose proof (Int64.unsigned_range bh).
  pose proof (Int64.unsigned_range d). pose proof (Int64.unsigned_range bl).
  unfold Int64.sub, Int64.add. rewrite Int64.unsigned_one.
  repeat split; apply Int64.unsigned_repr; unfold Int64.max_unsigned; lia.
Qed.
