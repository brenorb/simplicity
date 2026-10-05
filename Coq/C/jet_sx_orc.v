(** Helpers for writing oracles of the symbolic executor and proving them
    correct: constants, and re-establishing the region invariant after a
    call that changed the memory. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Maps Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

(** Value of a constant 64-bit argument. *)
Definition xconst (x : sx) : option Z :=
  match x with
  | XLc l => Some (Int64.unsigned l)
  | XI2L Unsigned (XIc i) => Some (Int.unsigned i)
  | XI2L Signed (XIc i) => if Z.leb 0 (Int.signed i) then Some (Int.signed i) else None
  | _ => None
  end.

Lemma xconst_sound ρ β x z :
  xconst x = Some z -> den ρ β x = Vlong (Int64.repr z) /\ 0 <= z <= Int64.max_unsigned.
Proof.
  destruct x; simpl; try discriminate.
  - intros H; inversion H; subst. rewrite Int64.repr_unsigned. split; [reflexivity|].
    pose proof (Int64.unsigned_range_2 l). lia.
  - destruct sg; destruct x; try discriminate.
    + destruct (Z.leb 0 (Int.signed i)) eqn:E; [|discriminate]. apply Z.leb_le in E.
      intros H; inversion H; subst. split; [reflexivity|].
      pose proof (Int.signed_range i). change Int.max_signed with 2147483647 in *.
      change Int64.max_unsigned with 18446744073709551615. lia.
    + intros H; inversion H; subst. split; [reflexivity|].
      pose proof (Int.unsigned_range_2 i). change Int.max_unsigned with 4294967295 in *.
      change Int64.max_unsigned with 18446744073709551615. lia.
Qed.

Lemma cells_sorted_shape cs cs' : forall lo,
  map cshape cs' = map cshape cs -> cells_sorted lo cs = cells_sorted lo cs'.
Proof.
  revert cs'. induction cs as [|c t IH]; intros cs' lo H; destruct cs' as [|c' t']; try discriminate; [reflexivity|].
  simpl in H. inversion H as [[H1 H2 H3]]. simpl. rewrite H1, H2. f_equal. apply IH. exact H3.
Qed.

(** After a change of memory that preserves permissions, the invariant holds
    for regions of the same shape whose defined cells are either unchanged
    cells whose content was preserved, or hold their new value. *)
Lemma rep_update ρ β regs regs' m m' :
  rep ρ β regs m ->
  map rshape regs' = map rshape regs ->
  (forall b o k p, Mem.perm m b o k p -> Mem.perm m' b o k p) ->
  (forall b, Mem.valid_block m b -> Mem.valid_block m' b) ->
  (forall r reg reg' c' x,
     nth_error regs r = Some reg -> nth_error regs' r = Some reg' ->
     In c' (rcells reg') -> cval c' = Some x ->
     (In c' (rcells reg) /\
      Mem.load (cchunk c') m' (blk β r) (bas β r + cofs c') =
      Mem.load (cchunk c') m (blk β r) (bas β r + cofs c')) \/
     (Mem.load (cchunk c') m' (blk β r) (bas β r + cofs c') = Some (den ρ (lay β) x) /\
      xp_le r x = true)) ->
  rep ρ β regs' m'.
Proof.
  intros (Hlen & Hnr & Hreg) Hsh Hperm Hvb Hcells.
  assert (Hlen' : length regs' = length regs).
  { rewrite <- (map_length rshape regs'), Hsh, map_length. reflexivity. }
  split; [congruence|]. split; [exact (rsep_shape β regs regs' Hsh Hnr)|].
  intros r reg' E'.
  destruct (nth_error regs r) as [reg|] eqn:E.
  2: { apply nth_error_None in E. assert (r < length regs')%nat by (apply nth_error_Some; congruence). lia. }
  assert (Hs : rshape reg' = rshape reg).
  { assert (H1 : nth_error (map rshape regs') r = nth_error (map rshape regs) r) by congruence.
    rewrite !nth_error_map, E, E' in H1. simpl in H1. congruence. }
  unfold rshape in Hs. inversion Hs as [[Hs1 Hs2 Hs3]].
  destruct (Hreg r reg E) as (Hb0 & Hv & Hsort & Hc & Hfree).
  split; [exact Hb0|]. split; [apply Hvb; exact Hv|].
  split; [rewrite <- (cells_sorted_shape _ _ 0 Hs1); exact Hsort|]. split.
  - apply Forall_forall. intros c' Hin'.
    destruct (shape_In _ _ c' Hs1 Hin') as (c & Hin & Eo & Ech).
    pose proof (proj1 (Forall_forall _ _) Hc c Hin) as (Hmax & Hal & Hpm & Hval).
    unfold cell_ok. rewrite <- Eo, <- Ech, Hs2.
    split; [exact Hmax|]. split; [exact Hal|].
    split; [intros o Ho; apply Hperm; apply Hpm; exact Ho|].
    intros x Hx. rewrite Eo, Ech.
    destruct (Hcells r reg reg' c' x E E' Hin' Hx) as [[Hold Hl]|Hnew]; [|exact Hnew].
    pose proof (proj1 (Forall_forall _ _) Hc c' Hold) as (_ & _ & _ & Hval').
    rewrite Hl. exact (Hval' x Hx).
  - rewrite Hs3. destruct (rfree reg) as [sz|]; [|exact I].
    destruct Hfree as (F1 & F2 & F3 & F4).
    split; [exact F1|]. split; [congruence|]. split; [intros o Ho; apply Hperm; apply F3; exact Ho|].
    apply Forall_forall. intros c' Hin'.
    destruct (shape_In _ _ c' Hs1 Hin') as (c & Hin & Eo & Ech).
    pose proof (proj1 (Forall_forall _ _) F4 c Hin) as H. simpl in H. rewrite <- Eo, <- Ech. exact H.
Qed.

(** Bounds of the variables defined by logged events. *)
Fixpoint bnd_of_log (tb : nat -> nat -> Z * Z) (log : list event) (n : nat) : Z * Z :=
  match log with
  | [] => (0, 18446744073709551615)
  | ev :: t =>
      if Nat.leb (ebase ev) n && Nat.ltb n (ebase ev + ecnt ev)
      then tb (etag ev) (n - ebase ev)%nat
      else bnd_of_log tb t n
  end.

Lemma bnd_of_log_sound (tb : nat -> nat -> Z * Z) (ev_ok : (nat -> int64) -> event -> Prop) ρ log :
  (forall ev, ev_ok ρ ev -> forall j, (j < ecnt ev)%nat ->
     fst (tb (etag ev) j) <= Int64.unsigned (ρ (ebase ev + j)%nat) <= snd (tb (etag ev) j)) ->
  Forall (ev_ok ρ) log ->
  forall n, fst (bnd_of_log tb log n) <= Int64.unsigned (ρ n) <= snd (bnd_of_log tb log n).
Proof.
  intros Htb Hs n. induction Hs as [|ev t Hev Ht IH]; simpl.
  - pose proof (Int64.unsigned_range_2 (ρ n)). change Int64.max_unsigned with 18446744073709551615 in *. lia.
  - destruct (Nat.leb (ebase ev) n && Nat.ltb n (ebase ev + ecnt ev)) eqn:E; [|exact IH].
    apply andb_true_iff in E. destruct E as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
    pose proof (Htb ev Hev (n - ebase ev)%nat ltac:(lia)) as H.
    replace (ebase ev + (n - ebase ev))%nat with n in H by lia. exact H.
Qed.
