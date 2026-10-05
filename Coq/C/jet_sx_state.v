(** Symbolic memory for the symbolic executor: regions of typed cells, the
    invariant relating them to a CompCert memory, and stores. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Maps Values Memory.
Require Import C.jet_sx_expr.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Record cell := mkcell { cofs : Z; cchunk : memory_chunk; cval : option sx }.
Record region := mkreg { rcells : list cell; rw : bool; rfree : option Z }.
Definition layout := list (block * Z).
Definition lay (β : layout) (r : nat) : block * Z := nth r β (1%positive, 0).
Definition blk (β : layout) (r : nat) : block := fst (lay β r).
Definition bas (β : layout) (r : nat) : Z := snd (lay β r).

Definition chunk_eqb (a b : memory_chunk) : bool := if chunk_eq a b then true else false.
Lemma chunk_eqb_eq a b : chunk_eqb a b = true -> a = b.
Proof. unfold chunk_eqb. destruct (chunk_eq a b); congruence. Qed.

Definition cell_at (c : cell) (d : Z) (ch : memory_chunk) : bool :=
  Z.eqb (cofs c) d && chunk_eqb (cchunk c) ch.

Fixpoint find_cell (cs : list cell) (d : Z) (ch : memory_chunk) : option cell :=
  match cs with
  | [] => None
  | c :: t => if cell_at c d ch then Some c else find_cell t d ch
  end.
Fixpoint set_cell (cs : list cell) (d : Z) (ch : memory_chunk) (v : option sx) : list cell :=
  match cs with
  | [] => []
  | c :: t => if cell_at c d ch then mkcell d ch v :: t else c :: set_cell t d ch v
  end.

Fixpoint cells_sorted (lo : Z) (cs : list cell) : bool :=
  match cs with
  | [] => true
  | c :: t => Z.leb lo (cofs c) && cells_sorted (cofs c + size_chunk (cchunk c)) t
  end.

Lemma size_chunk_pos' ch : 0 < size_chunk ch.
Proof. destruct ch; simpl; lia. Qed.

Lemma cell_at_true c d ch : cell_at c d ch = true -> cofs c = d /\ cchunk c = ch.
Proof.
  unfold cell_at. intros H. apply andb_true_iff in H. destruct H as [H1 H2].
  split; [apply Z.eqb_eq; exact H1|apply chunk_eqb_eq; exact H2].
Qed.

Lemma find_cell_In cs d ch c : find_cell cs d ch = Some c -> In c cs /\ cofs c = d /\ cchunk c = ch.
Proof.
  induction cs as [|c0 t IH]; simpl; [discriminate|].
  destruct (cell_at c0 d ch) eqn:E.
  - intros H; inversion H; subst c0. split; [left; reflexivity|apply cell_at_true; exact E].
  - intros H. destruct (IH H) as (H1 & H2). split; [right; exact H1|exact H2].
Qed.

Lemma sorted_lower lo cs c : cells_sorted lo cs = true -> In c cs -> lo <= cofs c.
Proof.
  revert lo. induction cs as [|c0 t IH]; simpl; intros lo H Hin; [contradiction|].
  apply andb_true_iff in H. destruct H as [H1 H2]. apply Z.leb_le in H1.
  destruct Hin as [->|Hin]; [exact H1|].
  specialize (IH _ H2 Hin). pose proof (size_chunk_pos' (cchunk c0)). lia.
Qed.

Lemma sorted_disj lo cs c1 c2 :
  cells_sorted lo cs = true -> In c1 cs -> In c2 cs ->
  c1 = c2 \/ cofs c1 + size_chunk (cchunk c1) <= cofs c2 \/ cofs c2 + size_chunk (cchunk c2) <= cofs c1.
Proof.
  revert lo. induction cs as [|c0 t IH]; simpl; intros lo H H1 H2; [contradiction|].
  apply andb_true_iff in H. destruct H as [Hlo Ht].
  destruct H1 as [->|H1], H2 as [->|H2].
  - left; reflexivity.
  - right; left. exact (sorted_lower _ _ _ Ht H2).
  - right; right. exact (sorted_lower _ _ _ Ht H1).
  - exact (IH _ Ht H1 H2).
Qed.

Lemma sorted_unique lo cs c1 c2 :
  cells_sorted lo cs = true -> In c1 cs -> In c2 cs -> cofs c1 = cofs c2 -> c1 = c2.
Proof.
  intros H H1 H2 E. destruct (sorted_disj lo cs c1 c2 H H1 H2) as [?|[?|?]]; [assumption| |].
  - pose proof (size_chunk_pos' (cchunk c1)). lia.
  - pose proof (size_chunk_pos' (cchunk c2)). lia.
Qed.

Lemma set_cell_sorted lo cs d ch v : cells_sorted lo cs = true -> cells_sorted lo (set_cell cs d ch v) = true.
Proof.
  revert lo. induction cs as [|c0 t IH]; simpl; intros lo H; [reflexivity|].
  apply andb_true_iff in H. destruct H as [Hlo Ht].
  destruct (cell_at c0 d ch) eqn:E.
  - destruct (cell_at_true _ _ _ E) as [E1 E2]. simpl. rewrite <- E1, <- E2, Hlo. exact Ht.
  - simpl. rewrite Hlo. apply IH. exact Ht.
Qed.

Lemma set_cell_In cs d ch v c : In c (set_cell cs d ch v) -> c = mkcell d ch v \/ In c cs.
Proof.
  induction cs as [|c0 t IH]; simpl; [tauto|].
  destruct (cell_at c0 d ch).
  - intros [<-|H]; [left; reflexivity|right; right; exact H].
  - intros [<-|H]; [right; left; reflexivity|]. destruct (IH H); [left|right; right]; assumption.
Qed.

Lemma set_cell_new cs d ch v c : find_cell cs d ch = Some c -> In (mkcell d ch v) (set_cell cs d ch v).
Proof.
  induction cs as [|c0 t IH]; simpl; [discriminate|].
  destruct (cell_at c0 d ch); [intros _; left; reflexivity|intros H; right; exact (IH H)].
Qed.

Definition cshape (c : cell) : Z * memory_chunk := (cofs c, cchunk c).
Definition rshape (reg : region) : list (Z * memory_chunk) * bool * option Z :=
  (map cshape (rcells reg), rw reg, rfree reg).

Lemma set_cell_shape cs d ch v : map cshape (set_cell cs d ch v) = map cshape cs.
Proof.
  induction cs as [|c0 t IH]; simpl; [reflexivity|].
  destruct (cell_at c0 d ch) eqn:E.
  - destruct (cell_at_true _ _ _ E) as [E1 E2]. simpl. unfold cshape at 1 3. simpl. rewrite E1, E2. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** Pointers held in a cell of region [r] only point into regions [<= r]. *)
Definition xp_le (r : nat) (x : sx) : bool :=
  match x with XP r' _ => Nat.leb r' r | _ => true end.

Definition cell_ok ρ (β : layout) (m : mem) (r : nat) (w : bool) (c : cell) : Prop :=
  bas β r + cofs c + size_chunk (cchunk c) <= Ptrofs.max_unsigned /\
  (align_chunk (cchunk c) | bas β r + cofs c) /\
  Mem.range_perm m (blk β r) (bas β r + cofs c) (bas β r + cofs c + size_chunk (cchunk c)) Cur
    (if w then Writable else Readable) /\
  (forall x, cval c = Some x ->
     Mem.load (cchunk c) m (blk β r) (bas β r + cofs c) = Some (den ρ (lay β) x) /\ xp_le r x = true).

Definition region_ok ρ (β : layout) (m : mem) (r : nat) (reg : region) : Prop :=
  0 <= bas β r /\ Mem.valid_block m (blk β r) /\
  cells_sorted 0 (rcells reg) = true /\
  Forall (cell_ok ρ β m r (rw reg)) (rcells reg) /\
  match rfree reg with
  | Some sz => bas β r = 0 /\ rw reg = true /\ Mem.range_perm m (blk β r) 0 sz Cur Freeable /\
               Forall (fun c => cofs c + size_chunk (cchunk c) <= sz) (rcells reg)
  | None => True
  end.

Definition rep ρ (β : layout) (regs : list region) (m : mem) : Prop :=
  length β = length regs /\ list_norepet (map fst β) /\
  forall r reg, nth_error regs r = Some reg -> region_ok ρ β m r reg.

Definition foot (β : layout) (sh : list (list (Z * memory_chunk) * bool * option Z)) (b : block) (o : Z) : Prop :=
  exists r s d ch, nth_error sh r = Some s /\ In (d, ch) (fst (fst s)) /\
    b = blk β r /\ bas β r + d <= o < bas β r + d + size_chunk ch.

Fixpoint upd {A} (l : list A) (i : nat) (v : A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: t, O => v :: t
  | x :: t, S i => x :: upd t i v
  end.
Lemma upd_length {A} (l : list A) i v : length (upd l i v) = length l.
Proof. revert i; induction l; destruct i; simpl; auto. Qed.
Lemma upd_same {A} (l : list A) i v x : nth_error l i = Some x -> nth_error (upd l i v) i = Some v.
Proof. revert i; induction l; destruct i; simpl; try discriminate; auto. Qed.
Lemma upd_other {A} (l : list A) i j v : i <> j -> nth_error (upd l i v) j = nth_error l j.
Proof. revert i j; induction l; destruct i, j; simpl; try congruence; auto. Qed.
Lemma upd_map_id {A B} (f : A -> B) (l : list A) i v x :
  nth_error l i = Some x -> f v = f x -> map f (upd l i v) = map f l.
Proof.
  revert i; induction l; destruct i; simpl; try discriminate.
  - intros H E; inversion H; subst; rewrite E; reflexivity.
  - intros H E. rewrite (IHl i H E). reflexivity.
Qed.

Lemma blk_inj β r1 r2 :
  list_norepet (map fst β) -> (r1 < length β)%nat -> (r2 < length β)%nat ->
  blk β r1 = blk β r2 -> r1 = r2.
Proof.
  unfold blk, lay. intros Hn. revert r1 r2. induction β as [|p β IH]; simpl; intros r1 r2 H1 H2 E; [lia|].
  inversion Hn as [|? ? Hnotin Hn']; subst.
  destruct r1, r2; simpl in E.
  - reflexivity.
  - exfalso. apply Hnotin. rewrite E. apply in_map. apply nth_In. lia.
  - exfalso. apply Hnotin. rewrite <- E. apply in_map. apply nth_In. lia.
  - f_equal. apply IH; auto; lia.
Qed.

(** ** Stores *)
Definition xstore (regs : list region) (r : nat) (d : Z) (ch : memory_chunk) (x : sx) : option (list region) :=
  match nth_error regs r with
  | Some reg =>
      if rw reg then
        match find_cell (rcells reg) d ch, xnorm ch x with
        | Some _, Some x' =>
            if xp_le r x' then Some (upd regs r (mkreg (set_cell (rcells reg) d ch (Some x')) (rw reg) (rfree reg)))
            else None
        | _, _ => None
        end
      else None
  | None => None
  end.

Lemma xstore_shape regs r d ch x regs' :
  xstore regs r d ch x = Some regs' -> map rshape regs' = map rshape regs.
Proof.
  unfold xstore. destruct (nth_error regs r) as [reg|] eqn:E; [|discriminate].
  destruct (rw reg) eqn:W; [|discriminate].
  destruct (find_cell (rcells reg) d ch); [|discriminate].
  destruct (xnorm ch x) as [x'|]; [|discriminate].
  destruct (xp_le r x'); [|discriminate].
  intros H; inversion H; subst regs'.
  eapply upd_map_id; [exact E|]. unfold rshape; simpl. rewrite set_cell_shape, W. reflexivity.
Qed.

Lemma xstore_sound ρ β regs m r d ch x regs' :
  rep ρ β regs m -> xstore regs r d ch x = Some regs' ->
  exists m',
    Mem.store ch m (blk β r) (bas β r + d) (den ρ (lay β) x) = Some m' /\
    0 <= bas β r + d <= Ptrofs.max_unsigned /\
    rep ρ β regs' m' /\
    Mem.unchanged_on (fun b o => ~ foot β (map rshape regs) b o) m m'.
Proof.
  intros (Hlen & Hnr & Hreg) Hs. unfold xstore in Hs.
  destruct (nth_error regs r) as [reg|] eqn:E; [|discriminate].
  destruct (rw reg) eqn:W; [|discriminate].
  destruct (find_cell (rcells reg) d ch) as [c|] eqn:F; [|discriminate].
  destruct (xnorm ch x) as [x'|] eqn:N; [|discriminate].
  destruct (xp_le r x') eqn:PL; [|discriminate].
  inversion Hs; subst regs'; clear Hs.
  destruct (find_cell_In _ _ _ _ F) as (Hin & Hd & Hch).
  destruct (Hreg r reg E) as (Hb0 & Hvb & Hsort & Hcells & Hfree).
  pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (Hmax & Hal & Hperm & Hval).
  rewrite Hd, Hch, W in *.
  assert (Hc0 : 0 <= d) by (rewrite <- Hd; exact (sorted_lower 0 _ _ Hsort Hin)).
  assert (VA : Mem.valid_access m ch (blk β r) (bas β r + d) Writable) by (split; assumption).
  destruct (Mem.valid_access_store m ch (blk β r) (bas β r + d) (den ρ (lay β) x) VA) as [m' Hst].
  exists m'. split; [exact Hst|]. split; [pose proof (size_chunk_pos' ch); lia|]. split.
  - split; [rewrite upd_length; exact Hlen|]. split; [exact Hnr|].
    intros r2 reg2 E2.
    assert (Hr2 : (r2 < length β)%nat).
    { rewrite Hlen. rewrite <- (upd_length regs r (mkreg (set_cell (rcells reg) d ch (Some x')) (rw reg) (rfree reg))).
      apply nth_error_Some. congruence. }
    assert (Hr : (r < length β)%nat) by (rewrite Hlen; apply nth_error_Some; congruence).
    destruct (Nat.eq_dec r r2) as [<-|Hne].
    + rewrite (upd_same _ _ _ _ E) in E2. inversion E2; subst reg2; clear E2. simpl.
      split; [exact Hb0|]. split; [eapply Mem.store_valid_block_1; eauto|].
      split; [apply set_cell_sorted; exact Hsort|]. split.
      * apply Forall_forall. intros c2 Hc2.
        assert (Hsort' := set_cell_sorted 0 _ d ch (Some x') Hsort).
        assert (Hnew := set_cell_new _ _ _ (Some x') _ F).
        destruct (Z.eq_dec (cofs c2) d) as [Ed|Nd].
        -- assert (c2 = mkcell d ch (Some x')) by (eapply sorted_unique; eauto).
           subst c2. unfold cell_ok; simpl. split; [exact Hmax|]. split; [exact Hal|].
           split; [intros o Ho; eapply Mem.perm_store_1; eauto; rewrite W; apply Hperm; exact Ho|].
           intros x0 Hx0; inversion Hx0; subst x0. split; [|exact PL].
           rewrite (Mem.load_store_same _ _ _ _ _ _ Hst). f_equal. apply xnorm_sound. exact N.
        -- destruct (set_cell_In _ _ _ _ _ Hc2) as [->|Hold]; [simpl in Nd; congruence|].
           pose proof (proj1 (Forall_forall _ _) Hcells c2 Hold) as (Hmax2 & Hal2 & Hperm2 & Hval2).
           split; [exact Hmax2|]. split; [exact Hal2|].
           split; [intros o Ho; eapply Mem.perm_store_1; eauto|].
           intros x0 Hx0. destruct (Hval2 x0 Hx0) as [Hl Hp]. split; [|exact Hp].
           rewrite (Mem.load_store_other _ _ _ _ _ _ Hst); [exact Hl|].
           right. destruct (sorted_disj 0 _ c c2 Hsort Hin Hold) as [->|[Hx|Hx]]; [congruence| |].
           ++ right. rewrite Hd, Hch in Hx. lia.
           ++ left. rewrite Hd in Hx. lia.
      * destruct (rfree reg) as [sz|]; [|exact I].
        destruct Hfree as (Hf1 & Hf2 & Hf3 & Hf4).
        split; [exact Hf1|]. split; [exact Hf2|].
        split; [intros o Ho; eapply Mem.perm_store_1; eauto|].
        apply Forall_forall. intros c2 Hc2.
        destruct (set_cell_In _ _ _ _ _ Hc2) as [->|Hold].
        -- simpl. pose proof (proj1 (Forall_forall _ _) Hf4 c Hin) as Hx. simpl in Hx.
           rewrite Hd, Hch in Hx. exact Hx.
        -- exact (proj1 (Forall_forall _ _) Hf4 c2 Hold).
    + rewrite (upd_other _ _ _ _ Hne) in E2.
      destruct (Hreg r2 reg2 E2) as (Hb02 & Hvb2 & Hsort2 & Hcells2 & Hfree2).
      split; [exact Hb02|]. split; [eapply Mem.store_valid_block_1; eauto|]. split; [exact Hsort2|].
      split.
      * apply Forall_forall. intros c2 Hc2.
        pose proof (proj1 (Forall_forall _ _) Hcells2 c2 Hc2) as (Hmax2 & Hal2 & Hperm2 & Hval2).
        split; [exact Hmax2|]. split; [exact Hal2|].
        split; [intros o Ho; eapply Mem.perm_store_1; eauto|].
        intros x0 Hx0. destruct (Hval2 x0 Hx0) as [Hl Hp]. split; [|exact Hp].
        rewrite (Mem.load_store_other _ _ _ _ _ _ Hst); [exact Hl|].
        left. intros Eb. apply Hne. symmetry. eapply blk_inj; eauto.
      * destruct (rfree reg2) as [sz|]; [|exact I].
        destruct Hfree2 as (Hf1 & Hf2 & Hf3 & Hf4).
        split; [exact Hf1|]. split; [exact Hf2|].
        split; [intros o Ho; eapply Mem.perm_store_1; eauto|exact Hf4].
  - eapply Mem.store_unchanged_on; [exact Hst|].
    intros i Hi Hn. apply Hn.
    exists r, (rshape reg), d, ch. split; [rewrite nth_error_map, E; reflexivity|].
    split; [|split; [reflexivity|exact Hi]].
    simpl. change (d, ch) with (cshape (mkcell d ch (cval c))).
    replace (mkcell d ch (cval c)) with c by (destruct c; simpl in *; congruence).
    apply in_map. exact Hin.
Qed.

(** ** Loads *)
Definition xload (regs : list region) (r : nat) (d : Z) (ty : type) : option sx :=
  match access_mode ty with
  | By_value ch =>
      match nth_error regs r with
      | Some reg => match find_cell (rcells reg) d ch with Some c => cval c | None => None end
      | None => None
      end
  | By_reference | By_copy => Some (XP r d)
  | By_nothing => None
  end.

Lemma xload_sound ρ β regs m r d ch c reg x :
  rep ρ β regs m -> nth_error regs r = Some reg -> find_cell (rcells reg) d ch = Some c -> cval c = Some x ->
  Mem.load ch m (blk β r) (bas β r + d) = Some (den ρ (lay β) x) /\
  0 <= bas β r + d <= Ptrofs.max_unsigned.
Proof.
  intros (Hlen & Hnr & Hreg) E F V.
  destruct (find_cell_In _ _ _ _ F) as (Hin & Hd & Hch).
  destruct (Hreg r reg E) as (Hb0 & Hvb & Hsort & Hcells & Hfree).
  pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (Hmax & Hal & Hperm & Hval).
  rewrite Hd, Hch in *. split; [exact (proj1 (Hval x V))|].
  pose proof (sorted_lower 0 _ _ Hsort Hin). pose proof (size_chunk_pos' ch). lia.
Qed.
