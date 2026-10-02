(** Compositional execution of the actual correction loop. The tail premise
    in the taken-step rule must be discharged by the two-correction invariant
    in the forthcoming whole-helper proof; it is not a public jet contract. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_readBit_layout C.jet_divmod96_value.
Require Import C.jet_divmod96_expr C.jet_divmod96_step.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divmod96_loop_stmt :=
  Sloop
    (Ssequence
      (Ssequence divmod96_guard_stmt (Sifthenelse (Etempvar _t'2 tint) Sskip Sbreak))
      divmod96_correction_stmt)
    Sskip.
Definition divmod96_next_env le q rh bh d bl :=
  PTree.set _d (Vlong (Int64.sub d bl))
    (PTree.set _rh (Vlong (Int64.add rh bh))
      (PTree.set _t'3 (Vlong q) (PTree.set _t'2 (Vint Int.one) le))).

Lemma exec_divmod96_loop_exit e le m rh al d :
  le!_rh = Some (Vlong rh) -> le!_al = Some (Vlong al) -> le!_d = Some (Vlong d) ->
  divmod96_guard rh al d = Datatypes.false ->
  Clight2.exec_stmt ge0 e le m divmod96_loop_stmt
    E0 (PTree.set _t'2 (Vint Int.zero) le) m Out_normal.
Proof.
  intros HR HA HD HG.
  eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
  eapply exec_Sseq_2; [|discriminate].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _t'2 (Vint Int.zero) le).
  - pose proof (exec_divmod96_guard_stmt e le m rh al d HR HA HD) as Hguard.
    rewrite HG in Hguard. exact Hguard.
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + apply eval_Etempvar. rewrite PTree.gss. reflexivity.
    + reflexivity.
    + apply exec_Sbreak.
Qed.

Lemma exec_divmod96_loop_take e le m ms mf lef bq ofs q rh bh al d bl :
  le!_q = Some (Vptr bq ofs) -> le!_rh = Some (Vlong rh) -> le!_bh = Some (Vlong bh) ->
  le!_al = Some (Vlong al) -> le!_d = Some (Vlong d) -> le!_bl = Some (Vlong bl) ->
  Mem.load Mint64 m bq (Ptrofs.unsigned ofs) = Some (Vlong q) ->
  Mem.store Mint64 m bq (Ptrofs.unsigned ofs) (Vlong (Int64.sub q Int64.one)) = Some ms ->
  divmod96_guard rh al d = Datatypes.true ->
  Clight2.exec_stmt ge0 e (divmod96_next_env le q rh bh d bl) ms divmod96_loop_stmt E0 lef mf Out_normal ->
  Clight2.exec_stmt ge0 e le m divmod96_loop_stmt E0 lef mf Out_normal.
Proof.
  intros HQ HR HB HA HD HBL HL HS HG Htail.
  eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0) (out1 := Out_normal)
    (le1 := divmod96_next_env le q rh bh d bl) (m1 := ms)
    (le2 := divmod96_next_env le q rh bh d bl) (m2 := ms).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _t'2 (Vint Int.one) le).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
        (le1 := PTree.set _t'2 (Vint Int.one) le).
      * pose proof (exec_divmod96_guard_stmt e le m rh al d HR HA HD) as Hguard.
        rewrite HG in Hguard. exact Hguard.
      * eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
        -- apply eval_Etempvar. rewrite PTree.gss. reflexivity.
        -- reflexivity.
        -- apply exec_Sskip.
    + eapply exec_divmod96_correction_stmt; try eassumption;
        rewrite PTree.gso by discriminate; assumption.
  - constructor.
  - apply exec_Sskip.
  - exact Htail.
Qed.
