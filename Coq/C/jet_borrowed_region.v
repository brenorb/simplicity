(** Shared metadata lemmas for reading borrowed constant field inputs.
    No claim about a complete beta jet or a whole-function execution. *)
From Coq Require Import ZArith List Bool.
From compcert Require Import AST Ctypes Memory.
Require Import C.jet_sx_expr C.jet_sx_state.
Import ListNotations.
Set Default Timeout 10.

Definition borrowed_region (reg : region) : region := mkreg (rcells reg) false None.
Definition borrow_at (q : nat) (regs : list region) : list region :=
  match nth_error regs q with
  | Some reg => upd regs q (borrowed_region reg)
  | None => regs
  end.

Lemma borrow_at_cells q regs : map rcells (borrow_at q regs) = map rcells regs.
Proof.
  unfold borrow_at; destruct (nth_error regs q) as [reg|] eqn:E; [|reflexivity].
  eapply upd_map_id; [exact E|reflexivity].
Qed.

Lemma nth_error_cells regs regs' r : map rcells regs = map rcells regs' ->
  option_map rcells (nth_error regs r) = option_map rcells (nth_error regs' r).
Proof.
  intro H; pose proof (f_equal (fun cs => nth_error cs r) H) as Hnth.
  change (nth_error (map rcells regs) r = nth_error (map rcells regs') r) in Hnth.
  rewrite !nth_error_map in Hnth; exact Hnth.
Qed.

Lemma xload_cells regs regs' r d ty : map rcells regs = map rcells regs' ->
  xload regs r d ty = xload regs' r d ty.
Proof.
  intro H; unfold xload; destruct (access_mode ty); try reflexivity.
  pose proof (nth_error_cells regs regs' r H) as Hnth.
  destruct (nth_error regs r) as [reg|], (nth_error regs' r) as [reg'|];
    cbn in Hnth; try discriminate; try reflexivity.
  injection Hnth as Hcells; rewrite Hcells; reflexivity.
Qed.

Lemma xload_borrow_at q regs r d ty :
  xload (borrow_at q regs) r d ty = xload regs r d ty.
Proof. apply xload_cells, borrow_at_cells. Qed.

Lemma borrowed_store_rejected q regs d ch x :
  xstore (borrow_at q regs) q d ch x = None.
Proof.
  unfold borrow_at; destruct (nth_error regs q) as [reg|] eqn:E.
  - unfold xstore; rewrite (upd_same regs q (borrowed_region reg) reg E); reflexivity.
  - unfold xstore; rewrite E; reflexivity.
Qed.

Lemma cell_ok_borrow rho beta m r w c :
  cell_ok rho beta m r w c -> cell_ok rho beta m r false c.
Proof.
  intros (Hmax & Halign & Hperm & Hvalue).
  split; [exact Hmax|]; split; [exact Halign|]; split; [|exact Hvalue].
  intros ofs Hofs; eapply Mem.perm_implies; [exact (Hperm ofs Hofs)|].
  destruct w; constructor.
Qed.

Lemma region_ok_borrow rho beta m r reg :
  region_ok rho beta m r reg -> region_ok rho beta m r (borrowed_region reg).
Proof.
  intros (Hbase & Hvalid & Hsorted & Hcells & Hfree).
  split; [exact Hbase|]; split; [exact Hvalid|]; split; [exact Hsorted|]; split; [|exact I].
  apply Forall_forall; intros c Hin.
  apply cell_ok_borrow with (w := rw reg).
  exact (proj1 (Forall_forall _ _) Hcells c Hin).
Qed.
