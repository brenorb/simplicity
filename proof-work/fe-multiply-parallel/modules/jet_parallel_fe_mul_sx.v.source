(** Generic symbolic-term support for the parallel field-multiplication proof:
    a checked syntactic equality, substitution under [den], and replacement of
    a represented cell by a term with the same denotation. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clightdefs Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec.
Require Import C.jet_secp_symbolic_substitution.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition bop_beq (a b : bop) : bool :=
  match a, b with
  | Badd, Badd | Bsub, Bsub | Bmul, Bmul | Band, Band | Bor, Bor | Bxor, Bxor => true
  | _, _ => false
  end.
Definition shop_beq (a b : shop) : bool :=
  match a, b with Hshl, Hshl | Hshr, Hshr | Hshru, Hshru => true | _, _ => false end.
Definition cmp_beq (a b : comparison) : bool :=
  match a, b with
  | Ceq, Ceq | Cne, Cne | Clt, Clt | Cle, Cle | Cgt, Cgt | Cge, Cge => true
  | _, _ => false
  end.
Definition sg_beq (a b : signedness) : bool :=
  match a, b with Signed, Signed | Unsigned, Unsigned => true | _, _ => false end.
Definition isz_beq (a b : intsize) : bool :=
  match a, b with I8, I8 | I16, I16 | I32, I32 | IBool, IBool => true | _, _ => false end.

Lemma bop_beq_true a b : bop_beq a b = true -> a = b.
Proof. destruct a, b; cbn; congruence. Qed.
Lemma shop_beq_true a b : shop_beq a b = true -> a = b.
Proof. destruct a, b; cbn; congruence. Qed.
Lemma cmp_beq_true a b : cmp_beq a b = true -> a = b.
Proof. destruct a, b; cbn; congruence. Qed.
Lemma sg_beq_true a b : sg_beq a b = true -> a = b.
Proof. destruct a, b; cbn; congruence. Qed.
Lemma isz_beq_true a b : isz_beq a b = true -> a = b.
Proof. destruct a, b; cbn; congruence. Qed.

(** Conservative: opaque values [XV] are never identified. *)
Fixpoint sx_beq (x y : sx) : bool :=
  match x, y with
  | XI i, XI j | XIc i, XIc j => Int.eq i j
  | XL i, XL j | XLc i, XLc j => Int64.eq i j
  | XLv n, XLv k => Nat.eqb n k
  | XA b o, XA c p => Pos.eqb b c && Ptrofs.eq o p
  | XP r d, XP s e => Nat.eqb r s && Z.eqb d e
  | XIb o a b, XIb p c d | XLb o a b, XLb p c d =>
      bop_beq o p && sx_beq a c && sx_beq b d
  | XIsh o a k, XIsh p c l | XLsh o a k, XLsh p c l =>
      shop_beq o p && sx_beq a c && Z.eqb k l
  | XIcmp o s a b, XIcmp p t c d | XLcmp o s a b, XLcmp p t c d =>
      cmp_beq o p && sg_beq s t && sx_beq a c && sx_beq b d
  | XI2L s a, XI2L t c => sg_beq s t && sx_beq a c
  | XIcast z s a, XIcast w t c => isz_beq z w && sg_beq s t && sx_beq a c
  | XL2I a, XL2I c | XInz a, XInz c | XLnz a, XLnz c | XIz a, XIz c
  | XLz a, XLz c | XIneg a, XIneg c | XLneg a, XLneg c | XInot a, XInot c
  | XLnot a, XLnot c => sx_beq a c
  | _, _ => false
  end.

Ltac beq_split :=
  repeat match goal with
  | H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H
  | H : Int.eq _ _ = true |- _ => apply Int.same_if_eq in H; subst
  | H : Int64.eq _ _ = true |- _ => apply Int64.same_if_eq in H; subst
  | H : Ptrofs.eq _ _ = true |- _ => apply Ptrofs.same_if_eq in H; subst
  | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H; subst
  | H : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in H; subst
  | H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H; subst
  | H : bop_beq _ _ = true |- _ => apply bop_beq_true in H; subst
  | H : shop_beq _ _ = true |- _ => apply shop_beq_true in H; subst
  | H : cmp_beq _ _ = true |- _ => apply cmp_beq_true in H; subst
  | H : sg_beq _ _ = true |- _ => apply sg_beq_true in H; subst
  | H : isz_beq _ _ = true |- _ => apply isz_beq_true in H; subst
  end.

Lemma sx_beq_true x : forall y, sx_beq x y = true -> x = y.
Proof.
  induction x; intros y H; destruct y; cbn [sx_beq] in H; try discriminate; beq_split;
    repeat match goal with
    | IH : forall y, sx_beq ?a y = true -> ?a = y, H : sx_beq ?a ?b = true |- _ =>
        apply IH in H; subst b
    end; reflexivity.
Qed.

(** Substitution of long-kinded terms for variables. *)
Definition long_subst (sigma : nat -> sx) : Prop := forall n, isk KL (sigma n) = true.

Lemma den_sx_subst rho beta sigma x :
  long_subst sigma ->
  den rho beta (sx_subst sigma x) = den (fun n => lv rho (sigma n)) beta x.
Proof.
  intros HS. induction x; cbn [sx_subst den]; try rewrite ?IHx, ?IHx1, ?IHx2; try reflexivity.
  rewrite (den_KL rho beta (sigma n) (HS n)), lv_den. reflexivity.
Qed.

Lemma lv_sx_subst rho sigma x :
  long_subst sigma -> lv rho (sx_subst sigma x) = lv (fun n => lv rho (sigma n)) x.
Proof. intros HS. unfold lv. rewrite den_sx_subst by exact HS. reflexivity. Qed.

(** Replace the term held by an existing cell, without touching memory. *)
Definition xreplace (regs : list region) (r : nat) (d : Z) (ch : memory_chunk) (x : sx)
    : option (list region) :=
  match nth_error regs r with
  | Some reg =>
      match find_cell (rcells reg) d ch with
      | Some _ => Some (upd regs r (mkreg (set_cell (rcells reg) d ch (Some x)) (rw reg) (rfree reg)))
      | None => None
      end
  | None => None
  end.

Lemma xreplace_shape regs r d ch x regs' :
  xreplace regs r d ch x = Some regs' -> map rshape regs' = map rshape regs.
Proof.
  unfold xreplace. destruct (nth_error regs r) as [reg|] eqn:E; [|discriminate].
  destruct (find_cell (rcells reg) d ch); [|discriminate].
  intros H; inversion H; subst regs'.
  eapply upd_map_id; [exact E|]. unfold rshape; cbn. rewrite set_cell_shape. reflexivity.
Qed.

Lemma rep_replace rho beta regs m r d x y regs' :
  rep rho beta regs m -> xload regs r d tulong = Some x ->
  den rho (lay beta) y = den rho (lay beta) x -> xp_le r y = true ->
  xreplace regs r d Mint64 y = Some regs' ->
  rep rho beta regs' m.
Proof.
  intros (HLen & HSep & HRegs) HLoad HDen HXp HRepl.
  change (match nth_error regs r with
    | Some reg => match find_cell (rcells reg) d Mint64 with Some c => cval c | None => None end
    | None => None end = Some x) in HLoad.
  unfold xreplace in HRepl.
  destruct (nth_error regs r) as [reg|] eqn:HR; [|discriminate].
  destruct (find_cell (rcells reg) d Mint64) as [c|] eqn:HC; [|discriminate].
  inversion HRepl; subst regs'; clear HRepl.
  destruct (find_cell_In _ _ _ _ HC) as (HIn & HOfs & HCh).
  assert (HShape : map rshape (upd regs r (mkreg (set_cell (rcells reg) d Mint64 (Some y))
     (rw reg) (rfree reg))) = map rshape regs).
  { eapply upd_map_id; [exact HR|]. unfold rshape; cbn. rewrite set_cell_shape. reflexivity. }
  split; [rewrite upd_length; exact HLen|]. split; [eapply rsep_shape; [exact HShape|exact HSep]|].
  intros r' reg' HR'.
  destruct (Nat.eq_dec r' r) as [->|HNe].
  - rewrite (upd_same _ _ _ _ HR) in HR'. inversion HR'; subst reg'; clear HR'.
    destruct (HRegs r reg HR) as (HB & HV & HSort & HCells & HFree).
    pose proof (proj1 (Forall_forall _ _) HCells c HIn) as (HMax & HAl & HPerm & HVal).
    split; [exact HB|]. split; [exact HV|]. split; [cbn; apply set_cell_sorted; exact HSort|].
    split.
    + apply Forall_forall. intros c' HIn'. cbn [rcells rw] in HIn' |- *.
      destruct (set_cell_In _ _ _ _ _ HIn') as [->|HOld].
      * cbn [cofs cchunk cval]. rewrite <- HOfs, <- HCh.
        split; [exact HMax|]. split; [exact HAl|]. split; [exact HPerm|].
        intros z Hz; inversion Hz; subst z. split; [|exact HXp].
        rewrite HDen. try rewrite HR in HLoad; try rewrite HC in HLoad. exact (proj1 (HVal x HLoad)).
      * exact (proj1 (Forall_forall _ _) HCells c' HOld).
    + cbn [rfree rcells]. destruct (rfree reg) as [sz|]; [|exact I].
      destruct HFree as (HB0 & HW & HFP & HFit). split; [exact HB0|]. split; [exact HW|].
      split; [exact HFP|]. apply Forall_forall. intros c' HIn'.
      destruct (set_cell_In _ _ _ _ _ HIn') as [->|HOld].
      * cbn [cofs cchunk]. pose proof (proj1 (Forall_forall _ _) HFit c HIn) as HF.
        rewrite <- HOfs, <- HCh; exact HF.
      * exact (proj1 (Forall_forall _ _) HFit c' HOld).
  - rewrite (upd_other _ _ _ _ (not_eq_sym HNe)) in HR'. exact (HRegs r' reg' HR').
Qed.
Print Assumptions sx_beq_true.
Print Assumptions den_sx_subst.
Print Assumptions rep_replace.
