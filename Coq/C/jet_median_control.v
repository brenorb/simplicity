(** Shared byte/wide median control tree, including every identity cast emitted
    by clightgen. Expression premises are discharged by the carrier adapters. *)
From Coq Require Import Bool.
From compcert Require Import Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Events.
Require Import C.jets C.jet_exec C.jet_readBit_layout.
Import Values Ctypes Clightdefs.
Set Default Timeout 10.

Definition median_cmp ty a b := Ebinop Olt (Etempvar a ty) (Etempvar b ty) tint.
Definition median_identity ty := Sset _t'4 (Ecast (Etempvar _t'4 ty) ty).
Definition median_set2 src_ty dst_ty id := Ssequence
  (Sset _t'4 (Ecast (Etempvar id src_ty) dst_ty)) (median_identity dst_ty).
Definition median_set3 src_ty dst_ty id := Ssequence
  (median_set2 src_ty dst_ty id) (median_identity dst_ty).
Definition median_choose src_ty dst_ty :=
  Sifthenelse (median_cmp src_ty _x _y)
    (Sifthenelse (median_cmp src_ty _y _z) (median_set2 src_ty dst_ty _y)
      (Sifthenelse (median_cmp src_ty _z _x)
        (median_set3 src_ty dst_ty _x) (median_set3 src_ty dst_ty _z)))
    (Sifthenelse (median_cmp src_ty _x _z) (median_set2 src_ty dst_ty _x)
      (Sifthenelse (median_cmp src_ty _z _y)
        (median_set3 src_ty dst_ty _y) (median_set3 src_ty dst_ty _z))).
Definition median_decision {A : Type} (bxy byz bzx bxz bzy : bool) (x y z : A) :=
  if bxy then if byz then y else if bzx then x else z
  else if bxz then x else if bzy then y else z.

Lemma exec_median_identity e le m ty v :
  sem_cast v ty ty m = Some v ->
  Clight2.exec_stmt ge0 e (PTree.set _t'4 v le) m (median_identity ty)
    E0 (PTree.set _t'4 v le) m Out_normal.
Proof.
  intros HC. rewrite <- (PTree.set2 _t'4 le v v) at 2.
  apply exec_set. eapply eval_Ecast; [apply eval_Etempvar; rewrite PTree.gss; reflexivity|exact HC].
Qed.
Lemma exec_median_set2 e le m src_ty dst_ty id v :
  eval_expr ge0 e le m (Ecast (Etempvar id src_ty) dst_ty) v ->
  sem_cast v dst_ty dst_ty m = Some v ->
  Clight2.exec_stmt ge0 e le m (median_set2 src_ty dst_ty id)
    E0 (PTree.set _t'4 v le) m Out_normal.
Proof.
  intros HE HC. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
  - apply exec_set. exact HE.
  - apply exec_median_identity. exact HC.
Qed.
Lemma exec_median_set3 e le m src_ty dst_ty id v :
  eval_expr ge0 e le m (Ecast (Etempvar id src_ty) dst_ty) v ->
  sem_cast v dst_ty dst_ty m = Some v ->
  Clight2.exec_stmt ge0 e le m (median_set3 src_ty dst_ty id)
    E0 (PTree.set _t'4 v le) m Out_normal.
Proof.
  intros HE HC. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _t'4 v le).
  - apply exec_median_set2; assumption.
  - apply exec_median_identity. exact HC.
Qed.
Lemma exec_median_if e le m ty a b yes no bit le' :
  eval_expr ge0 e le m (median_cmp ty a b) (Vint (bit_int bit)) ->
  Clight2.exec_stmt ge0 e le m (if bit then yes else no) E0 le' m Out_normal ->
  Clight2.exec_stmt ge0 e le m (Sifthenelse (median_cmp ty a b) yes no) E0 le' m Out_normal.
Proof.
  intros HE HS. eapply exec_Sifthenelse with (v1 := Vint (bit_int bit)) (b := bit).
  - exact HE.
  - destruct bit; reflexivity.
  - exact HS.
Qed.
Lemma exec_median_choose e le m src_ty dst_ty bxy byz bzx bxz bzy xv yv zv :
  eval_expr ge0 e le m (median_cmp src_ty _x _y) (Vint (bit_int bxy)) ->
  eval_expr ge0 e le m (median_cmp src_ty _y _z) (Vint (bit_int byz)) ->
  eval_expr ge0 e le m (median_cmp src_ty _z _x) (Vint (bit_int bzx)) ->
  eval_expr ge0 e le m (median_cmp src_ty _x _z) (Vint (bit_int bxz)) ->
  eval_expr ge0 e le m (median_cmp src_ty _z _y) (Vint (bit_int bzy)) ->
  eval_expr ge0 e le m (Ecast (Etempvar _x src_ty) dst_ty) xv ->
  eval_expr ge0 e le m (Ecast (Etempvar _y src_ty) dst_ty) yv ->
  eval_expr ge0 e le m (Ecast (Etempvar _z src_ty) dst_ty) zv ->
  sem_cast xv dst_ty dst_ty m = Some xv ->
  sem_cast yv dst_ty dst_ty m = Some yv ->
  sem_cast zv dst_ty dst_ty m = Some zv ->
  Clight2.exec_stmt ge0 e le m (median_choose src_ty dst_ty) E0
    (PTree.set _t'4 (median_decision bxy byz bzx bxz bzy xv yv zv) le) m Out_normal.
Proof.
  intros Hxy Hyz Hzx Hxz Hzy HX HY HZ CX CY CZ. unfold median_choose, median_decision.
  apply (exec_median_if _ _ _ _ _ _ _ _ bxy); [exact Hxy|]. destruct bxy.
  - apply (exec_median_if _ _ _ _ _ _ _ _ byz); [exact Hyz|]. destruct byz.
    + apply exec_median_set2; assumption.
    + apply (exec_median_if _ _ _ _ _ _ _ _ bzx); [exact Hzx|]. destruct bzx;
        apply exec_median_set3; assumption.
  - apply (exec_median_if _ _ _ _ _ _ _ _ bxz); [exact Hxz|]. destruct bxz.
    + apply exec_median_set2; assumption.
    + apply (exec_median_if _ _ _ _ _ _ _ _ bzy); [exact Hzy|]. destruct bzy;
        apply exec_median_set3; assumption.
Qed.
