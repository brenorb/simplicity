(** Metadata-only transport; the numeric checkpoint definitions are unchanged. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Memory Maps.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_revalue_cells.
Require Import C.jet_secp_multiply_checkpoint_atomic.
Require Import C.jet_borrowed_region.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition borrow_state q st := mkst (stemps st) (borrow_at q (sregs st)) (slog st) (snv st).

Lemma borrow_at_length q regs : length (borrow_at q regs) = length regs.
Proof. unfold borrow_at; destruct (nth_error regs q); [apply upd_length|reflexivity]. Qed.

Lemma map_upd {A B : Type} (f : A -> B) xs q value :
  map f (upd xs q value) = upd (map f xs) q (f value).
Proof. revert q; induction xs; intros [|q]; cbn; try reflexivity; rewrite IHxs; reflexivity. Qed.

Lemma borrow_map f q regs :
  (forall reg, f (borrowed_region reg) = borrowed_region (f reg)) ->
  map f (borrow_at q regs) = borrow_at q (map f regs).
Proof.
  intro H; unfold borrow_at; rewrite nth_error_map.
  destruct (nth_error regs q) as [reg|]; cbn [option_map]; [|reflexivity].
  rewrite map_upd, H; reflexivity.
Qed.

Lemma revalue_borrow f reg :
  revalue_region f (borrowed_region reg) = borrowed_region (revalue_region f reg).
Proof. reflexivity. Qed.

Lemma atomic_regs_borrow rho beta q regs :
  atomic_regs rho beta (borrow_at q regs) = borrow_at q (atomic_regs rho beta regs).
Proof. apply borrow_map; intro reg; apply revalue_borrow. Qed.

Lemma atomic_state_borrow rho beta q st :
  atomic_state rho beta (borrow_state q st) = borrow_state q (atomic_state rho beta st).
Proof.
  unfold atomic_state, borrow_state; cbn [stemps sregs slog snv].
  rewrite atomic_regs_borrow; reflexivity.
Qed.

Lemma borrow_head a b rest : borrow_at 1 (a :: b :: rest) = a :: borrowed_region b :: rest.
Proof. reflexivity. Qed.

Lemma foot_regions beta regs b ofs :
  foot beta (map rshape regs) b ofs <->
  exists r reg d ch, nth_error regs r = Some reg /\ In (d, ch) (map cshape (rcells reg)) /\
    b = blk beta r /\ bas beta r + d <= ofs < bas beta r + d + size_chunk ch.
Proof.
  unfold foot; split.
  - intros (r & shape & d & ch & HN & HI & HB & HO).
    rewrite nth_error_map in HN; destruct (nth_error regs r) as [reg|] eqn:ER; [|discriminate].
    cbn [option_map] in HN; injection HN as HS; subst shape.
    exists r, reg, d, ch; split; [exact ER|]; split; [exact HI|]; split; assumption.
  - intros (r & reg & d & ch & HN & HI & HB & HO).
    exists r, (rshape reg), d, ch; split; [rewrite nth_error_map, HN; reflexivity|].
    split; [exact HI|]; split; assumption.
Qed.

Lemma foot_cells beta regs regs' b ofs : map rcells regs = map rcells regs' ->
  foot beta (map rshape regs) b ofs -> foot beta (map rshape regs') b ofs.
Proof.
  intro HC; rewrite !foot_regions.
  intros (r & reg & d & ch & HN & HI & HB & HO).
  pose proof (nth_error_cells regs regs' r HC) as HE.
  rewrite HN in HE; destruct (nth_error regs' r) as [reg'|] eqn:ER; [|discriminate].
  cbn [option_map] in HE; injection HE as HE.
  exists r, reg', d, ch; split; [exact ER|]; split; [rewrite <- HE; exact HI|]; split; assumption.
Qed.

Lemma foot_borrow beta q regs b ofs :
  foot beta (map rshape (borrow_at q regs)) b ofs <-> foot beta (map rshape regs) b ofs.
Proof.
  split; apply foot_cells; [apply borrow_at_cells|symmetry; apply borrow_at_cells].
Qed.

Lemma lframe_borrow beta q regs m mf :
  lframe (fun b ofs => ~ foot beta (map rshape (borrow_at q regs)) b ofs) m mf ->
  lframe (fun b ofs => ~ foot beta (map rshape regs) b ofs) m mf.
Proof.
  intro HF; eapply lframe_implies; [exact HF|].
  intros b ofs HN HV HP; apply HN; apply (proj1 (foot_borrow beta q regs b ofs)); exact HP.
Qed.
