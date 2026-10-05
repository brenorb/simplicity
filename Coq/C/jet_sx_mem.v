(** Symbolic executor: allocation and release of stack regions, parameter
    binding, and stability of the region invariant. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Globalenvs Errors Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

(** ** Independence of the layout *)
Lemma den_proj_indep ρ x β β' :
  ii (den ρ β x) = ii (den ρ β' x) /\ il (den ρ β x) = il (den ρ β' x).
Proof.
  induction x; simpl; try (split; reflexivity);
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with H : ii _ = ii _ |- _ => rewrite H; clear H end;
    repeat match goal with H : il _ = il _ |- _ => rewrite H; clear H end;
    split; reflexivity.
Qed.

Lemma truth_indep ρ β β' c : truth ρ β c = truth ρ β' c.
Proof. unfold truth. rewrite (proj1 (den_proj_indep ρ c β β')). reflexivity. Qed.

Definition xp_lt (n : nat) (x : sx) : bool :=
  match x with XP r _ => Nat.ltb r n | _ => true end.

Lemma den_ext ρ x (β β' : nat -> block * Z) n :
  (forall r, (r < n)%nat -> β' r = β r) -> xp_lt n x = true -> den ρ β' x = den ρ β x.
Proof.
  intros H Hx.
  destruct x; simpl in *;
    try rewrite !(proj1 (den_proj_indep ρ _ β' β));
    try rewrite !(proj2 (den_proj_indep ρ _ β' β)); try reflexivity.
  apply Nat.ltb_lt in Hx. rewrite (H r Hx). reflexivity.
Qed.

Lemma xp_le_lt r x : xp_le r x = true -> xp_lt (S r) x = true.
Proof.
  destruct x; simpl; auto.
Qed.

Lemma lay_app_l β βN r : (r < length β)%nat -> lay (β ++ βN) r = lay β r.
Proof. intros H. unfold lay. apply app_nth1. exact H. Qed.

(** ** Stability of the invariant *)
Lemma region_ok_ext ρ β β' m r reg :
  (forall r', (r' <= r)%nat -> lay β' r' = lay β r') ->
  region_ok ρ β m r reg -> region_ok ρ β' m r reg.
Proof.
  intros H (Hb0 & Hvb & Hsort & Hcells & Hfree).
  assert (Eb : blk β' r = blk β r) by (unfold blk; rewrite H by lia; reflexivity).
  assert (Es : bas β' r = bas β r) by (unfold bas; rewrite H by lia; reflexivity).
  unfold region_ok. rewrite Eb, Es.
  split; [exact Hb0|]. split; [exact Hvb|]. split; [exact Hsort|]. split; [|exact Hfree].
  apply Forall_forall. intros c Hc.
  pose proof (proj1 (Forall_forall _ _) Hcells c Hc) as (Hmax & Hal & Hperm & Hval).
  unfold cell_ok. rewrite Eb, Es.
  split; [exact Hmax|]. split; [exact Hal|]. split; [exact Hperm|].
  intros x Hx. destruct (Hval x Hx) as [Hl Hp]. split; [|exact Hp].
  rewrite Hl. f_equal. symmetry. apply den_ext with (n := S r).
  - intros r' Hr'. apply H. lia.
  - apply xp_le_lt. exact Hp.
Qed.

Lemma region_ok_mem ρ β m m' r reg :
  Mem.unchanged_on (fun b _ => b = blk β r) m m' ->
  region_ok ρ β m r reg -> region_ok ρ β m' r reg.
Proof.
  intros U (Hb0 & Hvb & Hsort & Hcells & Hfree).
  split; [exact Hb0|]. split; [eapply Mem.valid_block_unchanged_on; eauto|].
  split; [exact Hsort|]. split.
  - apply Forall_forall. intros c Hc.
    pose proof (proj1 (Forall_forall _ _) Hcells c Hc) as (Hmax & Hal & Hperm & Hval).
    split; [exact Hmax|]. split; [exact Hal|].
    split; [intros o Ho; eapply Mem.perm_unchanged_on; eauto; reflexivity|].
    intros x Hx. destruct (Hval x Hx) as [Hl Hp]. split; [|exact Hp].
    eapply Mem.load_unchanged_on; eauto. intros; reflexivity.
  - destruct (rfree reg) as [sz|]; [|exact I].
    destruct Hfree as (Hf1 & Hf2 & Hf3 & Hf4).
    split; [exact Hf1|]. split; [exact Hf2|]. split; [|exact Hf4].
    intros o Ho. eapply Mem.perm_unchanged_on; eauto. reflexivity.
Qed.

Lemma rep_mem ρ β regs m m' :
  Mem.unchanged_on (fun b _ => In b (map fst β)) m m' -> rep ρ β regs m -> rep ρ β regs m'.
Proof.
  intros U (Hlen & Hnr & Hreg). split; [exact Hlen|]. split; [exact Hnr|].
  intros r reg E. eapply region_ok_mem; [|exact (Hreg r reg E)].
  eapply Mem.unchanged_on_implies; [exact U|].
  intros b o -> _. unfold blk, lay. apply in_map. apply nth_In.
  rewrite Hlen. apply nth_error_Some. congruence.
Qed.

Lemma rep_prefix ρ β βN regs regsN m :
  rep ρ (β ++ βN) (regs ++ regsN) m -> length β = length regs -> rep ρ β regs m.
Proof.
  intros (Hlen & Hnr & Hreg) Hl. split; [exact Hl|].
  split.
  { intros r1 r2 reg1 reg2 Hne E1 E2.
    assert (H1 : (r1 < length regs)%nat) by (apply nth_error_Some; congruence).
    assert (H2 : (r2 < length regs)%nat) by (apply nth_error_Some; congruence).
    pose proof (Hnr r1 r2 reg1 reg2 Hne ltac:(rewrite nth_error_app1 by exact H1; exact E1)
                  ltac:(rewrite nth_error_app1 by exact H2; exact E2)) as H.
    unfold blk, bas in *. rewrite !lay_app_l in H by lia. exact H. }
  intros r reg E.
  assert (Hr : (r < length regs)%nat) by (apply nth_error_Some; congruence).
  eapply region_ok_ext; [|apply Hreg; rewrite nth_error_app1 by exact Hr; exact E].
  intros r' Hr'. symmetry. apply lay_app_l. lia.
Qed.

Lemma blk_in β r : (r < length β)%nat -> In (blk β r) (map fst β).
Proof. intros H. unfold blk, lay. apply in_map. apply nth_In. exact H. Qed.

Lemma rsep_snoc β regs b base reg :
  length β = length regs -> rsep β regs -> ~ In b (map fst β) ->
  rsep (β ++ [(b, base)]) (regs ++ [reg]).
Proof.
  intros Hlen Hs Hnew r1 r2 reg1 reg2 Hne E1 E2.
  assert (Hl1 : (r1 < length (regs ++ [reg]))%nat) by (apply nth_error_Some; congruence).
  assert (Hl2 : (r2 < length (regs ++ [reg]))%nat) by (apply nth_error_Some; congruence).
  rewrite app_length in Hl1, Hl2. simpl in Hl1, Hl2.
  assert (Hnewb : blk (β ++ [(b, base)]) (length regs) = b).
  { unfold blk, lay. rewrite app_nth2 by lia. rewrite Hlen, Nat.sub_diag. reflexivity. }
  destruct (lt_dec r1 (length regs)) as [H1|H1]; destruct (lt_dec r2 (length regs)) as [H2|H2].
  - rewrite nth_error_app1 in E1, E2 by assumption.
    pose proof (Hs r1 r2 reg1 reg2 Hne E1 E2) as H.
    unfold blk, bas in *. rewrite !lay_app_l by lia. exact H.
  - left. assert (r2 = length regs) by lia. subst r2. rewrite Hnewb.
    intros E. apply Hnew. rewrite <- E. unfold blk. rewrite lay_app_l by lia. apply blk_in. lia.
  - left. assert (r1 = length regs) by lia. subst r1. rewrite Hnewb.
    intros E. apply Hnew. rewrite E. unfold blk. rewrite lay_app_l by lia. apply blk_in. lia.
  - lia.
Qed.

Lemma rep_snoc ρ β regs m b cs sz :
  rep ρ β regs m -> ~ In b (map fst β) -> Mem.valid_block m b ->
  Mem.range_perm m b 0 sz Cur Freeable ->
  cells_sorted 0 cs = true ->
  Forall (fun c => cofs c + size_chunk (cchunk c) <= sz /\ (align_chunk (cchunk c) | cofs c) /\
                   cval c = None) cs ->
  sz <= Ptrofs.max_unsigned ->
  rep ρ (β ++ [(b, 0)]) (regs ++ [mkreg cs true (Some sz)]) m.
Proof.
  intros (Hlen & Hnr & Hreg) Hnew Hvb Hperm Hsort Hcs Hsz.
  split; [rewrite !app_length, Hlen; reflexivity|].
  split.
  { apply rsep_snoc; assumption. }
  intros r reg E.
  destruct (lt_dec r (length regs)) as [Hr|Hr].
  - rewrite nth_error_app1 in E by exact Hr.
    eapply region_ok_ext; [|exact (Hreg r reg E)].
    intros r' Hr'. apply lay_app_l. lia.
  - assert (r = length regs).
    { assert (r < length (regs ++ [mkreg cs true (Some sz)]))%nat by (apply nth_error_Some; congruence).
      rewrite app_length in H; simpl in H. lia. }
    subst r. rewrite nth_error_app2, Nat.sub_diag in E by lia. simpl in E. inversion E; subst reg; clear E.
    assert (Eb : blk (β ++ [(b, 0)]) (length regs) = b).
    { unfold blk, lay. rewrite app_nth2 by lia. rewrite Hlen, Nat.sub_diag. reflexivity. }
    assert (Es : bas (β ++ [(b, 0)]) (length regs) = 0).
    { unfold bas, lay. rewrite app_nth2 by lia. rewrite Hlen, Nat.sub_diag. reflexivity. }
    unfold region_ok. rewrite Eb, Es. simpl.
    split; [lia|]. split; [exact Hvb|]. split; [exact Hsort|]. split.
    + apply Forall_forall. intros c Hc.
      pose proof (proj1 (Forall_forall _ _) Hcs c Hc) as (H1 & H2 & H3).
      unfold cell_ok. rewrite Eb, Es. simpl.
      pose proof (sorted_lower 0 _ _ Hsort Hc).
      split; [lia|]. split; [exact H2|].
      split; [intros o Ho; eapply Mem.perm_implies; [apply Hperm; lia|constructor]|].
      intros x Hx; congruence.
    + split; [reflexivity|]. split; [reflexivity|]. split; [exact Hperm|].
      apply Forall_forall. intros c Hc. exact (proj1 (proj1 (Forall_forall _ _) Hcs c Hc)).
Qed.

(** ** Cells of a C type *)
Fixpoint arr_cells (f : Z -> option (list cell)) (sz : Z) (k : nat) (ofs : Z) : option (list cell) :=
  match k with
  | O => Some []
  | S k =>
      match f ofs, arr_cells f sz k (ofs + sz) with
      | Some a, Some b => Some (a ++ b)
      | _, _ => None
      end
  end.

Fixpoint mem_cells (f : type -> Z -> option (list cell)) (ce : composite_env) (all ms : members) (ofs : Z)
    : option (list cell) :=
  match ms with
  | [] => Some []
  | Member_plain fid t :: rest =>
      match field_offset ce fid all with
      | OK (delta, Full) =>
          match f t (ofs + delta), mem_cells f ce all rest ofs with
          | Some a, Some b => Some (a ++ b)
          | _, _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Fixpoint cells_of (fuel : nat) (ce : composite_env) (ty : type) (ofs : Z) : option (list cell) :=
  match fuel with
  | O => None
  | S fuel =>
      match ty with
      | Tarray t n _ => arr_cells (cells_of fuel ce t) (sizeof ce t) (Z.to_nat n) ofs
      | Tstruct id _ =>
          match ce!id with
          | Some co => mem_cells (cells_of fuel ce) ce (co_members co) (co_members co) ofs
          | None => None
          end
      | _ => match access_mode ty with By_value ch => Some [mkcell ofs ch None] | _ => None end
      end
  end.

Definition std_cells (ce : composite_env) (id : ident) (ty : type) : option (list cell) :=
  cells_of 8 ce ty 0.

Definition cell_allocb (sz : Z) (c : cell) : bool :=
  Z.leb (cofs c + size_chunk (cchunk c)) sz && Z.eqb (cofs c mod align_chunk (cchunk c)) 0 &&
  match cval c with None => true | Some _ => false end.

Lemma align_chunk_pos' ch : 0 < align_chunk ch.
Proof. destruct ch; simpl; lia. Qed.

Lemma cell_allocb_true sz c :
  cell_allocb sz c = true ->
  cofs c + size_chunk (cchunk c) <= sz /\ (align_chunk (cchunk c) | cofs c) /\ cval c = None.
Proof.
  unfold cell_allocb. intros H. apply andb_true_iff in H. destruct H as [H H3].
  apply andb_true_iff in H. destruct H as [H1 H2].
  split; [apply Z.leb_le; exact H1|]. split.
  - apply Z.eqb_eq in H2. apply Z.mod_divide; [pose proof (align_chunk_pos' (cchunk c)); lia|exact H2].
  - destruct (cval c); [discriminate|reflexivity].
Qed.

Fixpoint xalloc (cf : ident -> type -> option (list cell)) (ce : composite_env)
    (vars : list (ident * type)) (n : nat) : option (list region * venv) :=
  match vars with
  | [] => Some ([], [])
  | (id, ty) :: t =>
      match cf id ty, xalloc cf ce t (S n) with
      | Some cs, Some (regs, ve) =>
          let sz := sizeof ce ty in
          if cells_sorted 0 cs && forallb (cell_allocb sz) cs && Z.leb sz Ptrofs.max_unsigned
          then Some (mkreg cs true (Some sz) :: regs, (id, (n, ty)) :: ve)
          else None
      | _, _ => None
      end
  end.

Lemma vlookup_cons id0 v ve id :
  vlookup ((id0, v) :: ve) id = if Pos.eqb id0 id then Some v else vlookup ve id.
Proof. reflexivity. Qed.

Section ALLOC.
Variable ge : genv.
Notation ce := (genv_cenv ge).

Lemma xalloc_sound ρ cf vars : forall n regsN veN β regs m e,
  xalloc cf ce vars n = Some (regsN, veN) -> rep ρ β regs m -> length β = n ->
  list_norepet (var_names vars) ->
  exists e' m' βN,
    alloc_variables ge e m vars e' m' /\
    rep ρ (β ++ βN) (regs ++ regsN) m' /\
    length βN = length regsN /\
    (forall id, e'!id = match vlookup veN id with
                        | Some (r, ty) => Some (blk (β ++ βN) r, ty)
                        | None => e!id end) /\
    (forall id r ty, vlookup veN id = Some (r, ty) ->
        In id (var_names vars) /\ (n <= r)%nat /\ bas (β ++ βN) r = 0 /\
        exists reg, nth_error (regs ++ regsN) r = Some reg /\ rfree reg = Some (sizeof ce ty)) /\
    (forall id1 id2 r ty1 ty2, vlookup veN id1 = Some (r, ty1) -> vlookup veN id2 = Some (r, ty2) -> id1 = id2) /\
    Forall (fun p => ~ Mem.valid_block m (fst p)) βN /\
    Mem.unchanged_on (fun _ _ => True) m m'.
Proof.
  induction vars as [|[id ty] t IH]; intros n regsN veN β regs m e Hx Hrep Hn Hnr; cbn [xalloc] in Hx.
  - inversion Hx; subst. exists e, m, []. rewrite !app_nil_r.
    split; [constructor|]. split; [exact Hrep|]. split; [reflexivity|].
    split; [intros; reflexivity|]. split; [intros; discriminate|]. split; [intros; discriminate|].
    split; [constructor|apply Mem.unchanged_on_refl].
  - destruct (cf id ty) as [cs|] eqn:Ecs; [|discriminate].
    destruct (xalloc cf ce t (S n)) as [[regsT veT]|] eqn:Et; [|discriminate].
    destruct (cells_sorted 0 cs && forallb (cell_allocb (sizeof ce ty)) cs &&
              Z.leb (sizeof ce ty) Ptrofs.max_unsigned) eqn:Chk; [|discriminate].
    inversion Hx; subst regsN veN; clear Hx.
    apply andb_true_iff in Chk. destruct Chk as [Chk C3]. apply andb_true_iff in Chk. destruct Chk as [C1 C2].
    apply Z.leb_le in C3. rewrite forallb_forall in C2.
    assert (Hnotin : ~ In id (var_names t)) by (inversion Hnr; assumption).
    assert (Hnr' : list_norepet (var_names t)) by (inversion Hnr; assumption).
    destruct (Mem.alloc m 0 (sizeof ce ty)) as [m1 b1] eqn:Al.
    assert (Hlen : length β = length regs) by (destruct Hrep as (H & _); exact H).
    assert (Hfresh : ~ In b1 (map fst β)).
    { intros Hin. apply in_map_iff in Hin. destruct Hin as (p & Hp1 & Hp2).
      destruct (In_nth _ _ (1%positive, 0) Hp2) as (r & Hr & Hnth).
      destruct Hrep as (_ & _ & Hreg).
      destruct (nth_error regs r) as [reg|] eqn:E; [|apply nth_error_None in E;
         assert (Hr' : (r < length regs)%nat) by (rewrite <- Hlen; exact Hr);
         exact (proj1 (Nat.lt_nge _ _) Hr' E)].
      destruct (Hreg r reg E) as (_ & Hvb & _).
      assert (Eb : blk β r = b1) by (unfold blk, lay; rewrite <- Hp1; f_equal; exact Hnth).
      rewrite Eb in Hvb.
      exact (Mem.fresh_block_alloc _ _ _ _ _ Al Hvb). }
    assert (Hrep1 : rep ρ (β ++ [(b1, 0)]) (regs ++ [mkreg cs true (Some (sizeof ce ty))]) m1).
    { apply rep_snoc.
      - eapply rep_mem; [|exact Hrep]. eapply Mem.unchanged_on_implies;
          [eapply Mem.alloc_unchanged_on; exact Al|]. intros; exact I.
      - exact Hfresh.
      - eapply Mem.valid_new_block; exact Al.
      - intros o Ho. eapply Mem.perm_alloc_2; eauto.
      - exact C1.
      - apply Forall_forall. intros c Hc. apply cell_allocb_true. apply C2. exact Hc.
      - exact C3. }
    destruct (IH (S n) regsT veT (β ++ [(b1, 0)]) (regs ++ [mkreg cs true (Some (sizeof ce ty))]) m1
                (PTree.set id (b1, ty) e) Et Hrep1 ltac:(rewrite app_length; simpl; lia) Hnr')
      as (e' & m' & βT & Hav & Hrep' & HlenT & He' & Hidx & Hinj & Hnv & Hun).
    repeat rewrite <- app_assoc in Hrep'. repeat rewrite <- app_assoc in He'.
    assert (Hidx' : forall id r ty0, vlookup veT id = Some (r, ty0) ->
        In id (var_names t) /\ (S n <= r)%nat /\ bas (β ++ (b1, 0) :: βT) r = 0 /\
        exists reg, nth_error (regs ++ mkreg cs true (Some (sizeof ce ty)) :: regsT) r = Some reg /\
                    rfree reg = Some (sizeof ce ty0)).
    { intros id0 r ty0 V. pose proof (Hidx id0 r ty0 V) as HH.
      repeat rewrite <- app_assoc in HH. exact HH. }
    clear Hidx. rename Hidx' into Hidx. simpl in Hrep', He'.
    exists e', m', ((b1, 0) :: βT).
    split; [econstructor; [exact Al|exact Hav]|].
    split; [exact Hrep'|]. split; [simpl; rewrite HlenT; reflexivity|].
    assert (HveT : forall id', vlookup veT id' <> None -> In id' (var_names t)).
    { intros id' Hne. destruct (vlookup veT id') as [[r ty']|] eqn:V; [|congruence].
      exact (proj1 (Hidx id' r ty' V)). }
    split.
    { intros id'. rewrite vlookup_cons. destruct (Pos.eqb id id') eqn:Eid.
      - apply Pos.eqb_eq in Eid. subst id'. rewrite He'.
        destruct (vlookup veT id) eqn:V.
        + exfalso. apply Hnotin. apply HveT. congruence.
        + rewrite PTree.gss. unfold blk, lay. rewrite app_nth2 by lia. rewrite Hn, Nat.sub_diag. reflexivity.
      - apply Pos.eqb_neq in Eid. rewrite He'. destruct (vlookup veT id') as [[r ty']|]; [reflexivity|].
        apply PTree.gso. congruence. }
    split.
    { intros id' r ty'. rewrite vlookup_cons. destruct (Pos.eqb id id') eqn:Eid.
      - apply Pos.eqb_eq in Eid. subst id'. intros H; inversion H; subst r ty'.
        split; [left; reflexivity|]. split; [lia|]. split.
        + unfold bas, lay. rewrite app_nth2 by lia. rewrite Hn, Nat.sub_diag. reflexivity.
        + exists (mkreg cs true (Some (sizeof ce ty))). split; [|reflexivity].
          rewrite nth_error_app2 by lia. rewrite <- Hn, Hlen, Nat.sub_diag. reflexivity.
      - intros V. destruct (Hidx id' r ty' V) as (H1 & H2 & H3 & H4).
        split; [right; exact H1|]. split; [lia|]. split; [exact H3|exact H4]. }
    split.
    { intros id1 id2 r ty1 ty2. rewrite !vlookup_cons.
      destruct (Pos.eqb id id1) eqn:E1; destruct (Pos.eqb id id2) eqn:E2; intros V1 V2.
      - apply Pos.eqb_eq in E1, E2. congruence.
      - inversion V1 as [[Hr1 Ht1]]. destruct (Hidx id2 r ty2 V2) as (_ & H2 & _). lia.
      - inversion V2 as [[Hr1 Ht1]]. destruct (Hidx id1 r ty1 V1) as (_ & H2 & _). lia.
      - exact (Hinj id1 id2 r ty1 ty2 V1 V2). }
    split.
    { constructor; [simpl; eapply Mem.fresh_block_alloc; exact Al|].
      eapply Forall_impl; [|exact Hnv]. intros p Hp Hv. apply Hp.
      eapply Mem.valid_block_alloc; eauto. }
    eapply Mem.unchanged_on_trans; [eapply Mem.alloc_unchanged_on; exact Al|exact Hun].
Qed.
End ALLOC.

(** ** Parameter binding *)
Fixpoint xbind (params : list (ident * type)) (xs : list sx) (ts : PTree.t sx) : option (PTree.t sx) :=
  match params, xs with
  | [], [] => Some ts
  | (id, _) :: ps, x :: xs => xbind ps xs (PTree.set id x ts)
  | _, _ => None
  end.

Lemma tmatch_set ρ β ts le id x :
  tmatch ρ β ts le -> tmatch ρ β (PTree.set id x ts) (PTree.set id (den ρ (lay β) x) le).
Proof.
  intros H id' x'. rewrite !PTree.gsspec. destruct (peq id' id); [intros E; inversion E; reflexivity|apply H].
Qed.

Lemma xbind_sound ρ β params : forall xs ts ts' le,
  xbind params xs ts = Some ts' -> tmatch ρ β ts le ->
  exists le', bind_parameter_temps params (map (den ρ (lay β)) xs) le = Some le' /\ tmatch ρ β ts' le'.
Proof.
  induction params as [|[id ty] ps IH]; intros xs ts ts' le H Hm; destruct xs as [|x xs]; simpl in H; try discriminate.
  - inversion H; subst. exists le. split; [reflexivity|exact Hm].
  - simpl. apply (IH xs _ _ _ H). apply tmatch_set. exact Hm.
Qed.

(** ** Releasing stack blocks *)
Lemma free_list_exists l : forall m,
  list_norepet (map (fun x => fst (fst x)) l) ->
  (forall b lo hi, In (b, lo, hi) l -> Mem.range_perm m b lo hi Cur Freeable) ->
  exists m', Mem.free_list m l = Some m' /\
    Mem.unchanged_on (fun b _ => ~ In b (map (fun x => fst (fst x)) l)) m m'.
Proof.
  induction l as [|[[b lo] hi] t IH]; intros m Hnr Hp; simpl.
  - exists m. split; [reflexivity|apply Mem.unchanged_on_refl].
  - inversion Hnr as [|? ? Hnotin Hnr']; subst.
    destruct (Mem.range_perm_free m b lo hi (Hp b lo hi (or_introl eq_refl))) as [m1 Hf].
    rewrite Hf.
    destruct (IH m1 Hnr') as (m' & Hfl & Hun).
    { intros b' lo' hi' Hin o Ho. eapply Mem.perm_free_1; eauto.
      - left. intros ->. apply Hnotin.
        exact (in_map (fun x : block * Z * Z => fst (fst x)) t (b, lo', hi') Hin).
      - apply (Hp b' lo' hi'); [right; exact Hin|exact Ho]. }
    exists m'. split; [exact Hfl|].
    eapply Mem.unchanged_on_trans.
    + eapply Mem.free_unchanged_on; [exact Hf|]. intros i Hi Hn. apply Hn. left; reflexivity.
    + eapply Mem.unchanged_on_implies; [exact Hun|]. intros b' o Hn _ Hin. apply Hn. right; exact Hin.
Qed.

Lemma norepet_map_keys {A B C} (f : A -> B) (g : A -> C) (l : list A) :
  list_norepet (map f l) ->
  (forall x y, In x l -> In y l -> g x = g y -> f x = f y) ->
  list_norepet (map g l).
Proof.
  induction l as [|a t IH]; simpl; intros Hn Hinj; [constructor|].
  inversion Hn as [|? ? Hnotin Hn']; subst. constructor.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as (y & Hy1 & Hy2).
    apply Hnotin. rewrite <- (Hinj y a (or_intror Hy2) (or_introl eq_refl) Hy1). apply in_map. exact Hy2.
  - apply IH; [exact Hn'|]. intros x y Hx Hy. apply Hinj; right; assumption.
Qed.

(** ** Load-level framing
    [lframe P m m']: on blocks valid in [m], loads from locations in [P] and
    permissions there are preserved.  It is implied by [Mem.unchanged_on] and
    is what helper contracts stated on loads provide. *)
Definition lframe (P : block -> Z -> Prop) (m m' : mem) : Prop :=
  (forall chunk b ofs, Mem.valid_block m b ->
     (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
     Mem.load chunk m' b ofs = Mem.load chunk m b ofs) /\
  (forall b ofs k p, Mem.valid_block m b -> P b ofs -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
  (forall b, Mem.valid_block m b -> Mem.valid_block m' b).

Lemma lframe_refl P m : lframe P m m.
Proof. split; [reflexivity|]. split; auto. Qed.

Lemma lframe_unchanged P m m' : Mem.unchanged_on P m m' -> lframe P m m'.
Proof.
  intros U. split.
  - intros chunk b ofs Hv HP. eapply Mem.load_unchanged_on_1; eauto.
  - split.
    + intros b ofs k p Hv HP Hp. eapply Mem.perm_unchanged_on; eauto.
    + intros b Hv. eapply Mem.valid_block_unchanged_on; eauto.
Qed.

Lemma lframe_implies (P Q : block -> Z -> Prop) m m' :
  lframe P m m' -> (forall b ofs, Q b ofs -> Mem.valid_block m b -> P b ofs) -> lframe Q m m'.
Proof.
  intros (L & Pm & V) H. split.
  - intros chunk b ofs Hv HQ. apply L; [exact Hv|]. intros i Hi. apply H; [apply HQ; exact Hi|exact Hv].
  - split; [|exact V]. intros b ofs k p Hv HQ. apply Pm; [exact Hv|]. apply H; assumption.
Qed.

Lemma lframe_trans P m1 m2 m3 : lframe P m1 m2 -> lframe P m2 m3 -> lframe P m1 m3.
Proof.
  intros (L1 & P1 & V1) (L2 & P2 & V2). split.
  - intros chunk b ofs Hv HP. rewrite L2 by (auto). apply L1; assumption.
  - split.
    + intros b ofs k p Hv HP Hp. apply P2; auto.
    + auto.
Qed.
