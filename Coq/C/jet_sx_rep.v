(** Building and using the region invariant of the symbolic executor. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Maps Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

Lemma rep_nil ρ m : rep ρ [] [] m.
Proof.
  split; [reflexivity|]. split; [constructor|]. intros r reg E. destruct r; discriminate.
Qed.

Lemma lay_app_new β p : lay (β ++ [p]) (length β) = p.
Proof. unfold lay. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma rep_add ρ β regs m b base reg :
  rep ρ β regs m -> ~ In b (map fst β) ->
  region_ok ρ (β ++ [(b, base)]) m (length regs) reg ->
  rep ρ (β ++ [(b, base)]) (regs ++ [reg]) m.
Proof.
  intros (Hlen & Hnr & Hreg) Hnew Hok.
  split; [rewrite !app_length, Hlen; reflexivity|].
  split.
  { rewrite map_app. apply list_norepet_app. split; [exact Hnr|]. split.
    - constructor; [simpl; tauto|constructor].
    - intros x y Hx [<-|[]] ->. apply Hnew. exact Hx. }
  intros r reg' E.
  destruct (lt_dec r (length regs)) as [Hr|Hr].
  - rewrite nth_error_app1 in E by exact Hr.
    eapply region_ok_ext; [|exact (Hreg r reg' E)].
    intros r' Hr'. apply lay_app_l. lia.
  - assert (r = length regs).
    { assert (r < length (regs ++ [reg]))%nat by (apply nth_error_Some; congruence).
      rewrite app_length in H; simpl in H. lia. }
    subst r. rewrite nth_error_app2, Nat.sub_diag in E by lia. simpl in E. inversion E; subst reg'.
    exact Hok.
Qed.

Lemma rep_region ρ β regs m r reg :
  rep ρ β regs m -> nth_error regs r = Some reg -> region_ok ρ β m r reg.
Proof. intros (_ & _ & H) E. exact (H r reg E). Qed.

Lemma region_load ρ β m r reg d ch x :
  region_ok ρ β m r reg -> In (mkcell d ch (Some x)) (rcells reg) ->
  Mem.load ch m (blk β r) (bas β r + d) = Some (den ρ (lay β) x).
Proof.
  intros (_ & _ & _ & Hc & _) Hin.
  pose proof (proj1 (Forall_forall _ _) Hc _ Hin) as (_ & _ & _ & Hv).
  exact (proj1 (Hv x eq_refl)).
Qed.

(** Arrays of 64-bit words. *)
Fixpoint u64_cells (ofs : Z) (xs : list sx) : list cell :=
  match xs with
  | [] => []
  | x :: t => mkcell ofs Mint64 (Some x) :: u64_cells (ofs + 8) t
  end.

Lemma u64_cells_sorted xs : forall ofs lo, lo <= ofs -> cells_sorted lo (u64_cells ofs xs) = true.
Proof.
  induction xs as [|x t IH]; intros ofs lo H; simpl; [reflexivity|].
  apply andb_true_iff. split; [apply Z.leb_le; exact H|apply IH; lia].
Qed.

Lemma u64_cells_In xs : forall ofs c, In c (u64_cells ofs xs) ->
  exists i x, nth_error xs i = Some x /\ c = mkcell (ofs + 8 * Z.of_nat i) Mint64 (Some x).
Proof.
  induction xs as [|x t IH]; intros ofs c Hin; simpl in Hin; [contradiction|].
  destruct Hin as [<-|Hin].
  - exists 0%nat, x. split; [reflexivity|]. f_equal. simpl. lia.
  - destruct (IH _ _ Hin) as (i & y & Hn & ->). exists (S i), y. split; [exact Hn|]. f_equal. lia.
Qed.

Lemma u64_cells_nth xs : forall ofs i x, nth_error xs i = Some x ->
  In (mkcell (ofs + 8 * Z.of_nat i) Mint64 (Some x)) (u64_cells ofs xs).
Proof.
  induction xs as [|y t IH]; intros ofs i x Hn; destruct i; simpl in Hn; try discriminate.
  - inversion Hn; subst. left. f_equal. simpl. lia.
  - right. replace (ofs + 8 * Z.of_nat (S i)) with (ofs + 8 + 8 * Z.of_nat i) by lia. apply IH. exact Hn.
Qed.

Lemma region_u64 ρ β m r xs (w : bool) :
  0 <= bas β r -> (8 | bas β r) ->
  bas β r + 8 * Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  Mem.valid_block m (blk β r) ->
  Mem.range_perm m (blk β r) (bas β r) (bas β r + 8 * Z.of_nat (length xs)) Cur
    (if w then Writable else Readable) ->
  (forall i x, nth_error xs i = Some x ->
     Mem.load Mint64 m (blk β r) (bas β r + 8 * Z.of_nat i) = Some (den ρ (lay β) x) /\ xp_le r x = true) ->
  region_ok ρ β m r (mkreg (u64_cells 0 xs) w None).
Proof.
  intros H0 Hal Hmax Hvb Hperm Hl.
  split; [exact H0|]. split; [exact Hvb|]. split; [apply u64_cells_sorted; lia|]. split; [|exact I].
  apply Forall_forall. intros c Hc. destruct (u64_cells_In _ _ _ Hc) as (i & x & Hn & ->).
  assert (Hi : (i < length xs)%nat) by (apply nth_error_Some; congruence).
  unfold cell_ok; cbn [cofs cchunk cval]; change (size_chunk Mint64) with 8; change (align_chunk Mint64) with 8;
    rewrite !Z.add_0_l.
  split; [lia|]. split; [apply Z.divide_add_r; [exact Hal|apply Z.divide_mul_l; exists 1; lia]|].
  split; [intros o Ho; apply Hperm; lia|].
  intros y Hy. inversion Hy; subst y. exact (Hl i x Hn).
Qed.
