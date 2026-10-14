(** A checked description of straight-line initialisations of a local
    aggregate (the stores CompCert generates for a compound literal):
    [lv_off] computes the offset of an lvalue rooted at the local, [zrun]
    recognises a run of constant-zero assignments and returns its cells;
    both are computed once and justified by [lv_sound] and [zrun_sound].
    [do_stores] is the resulting memory; disjoint cells are read back by
    [do_stores_get]. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jets_sha C.jet_sha_linkage.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Definition cell : Type := (Z * memory_chunk * val)%type.

Fixpoint do_stores (m : mem) (b : block) (l : list cell) : option mem :=
  match l with
  | [] => Some m
  | (o, ch, v) :: l' =>
      match Mem.store ch m b o v with
      | Some m1 => do_stores m1 b l'
      | None => None
      end
  end.

Lemma do_stores_app m b l1 : forall l2,
  do_stores m b (l1 ++ l2) =
    match do_stores m b l1 with Some m1 => do_stores m1 b l2 | None => None end.
Proof.
  revert m. induction l1 as [|[[o ch] v] l1 IH]; intros m l2; cbn [do_stores app]; [reflexivity|].
  destruct (Mem.store ch m b o v); [apply IH|reflexivity].
Qed.

Definition cell_ok (lo hi : Z) (c : cell) : bool :=
  let '(o, ch, _) := c in (lo <=? o) && (o + size_chunk ch <=? hi) && (o mod align_chunk ch =? 0).

Lemma do_stores_exists b lo hi l : forall m,
  Mem.range_perm m b lo hi Cur Writable -> forallb (cell_ok lo hi) l = true ->
  exists m', do_stores m b l = Some m'.
Proof.
  induction l as [|[[o ch] v] l IH]; intros m HP HOk; cbn [do_stores]; [eexists; reflexivity|].
  cbn [forallb cell_ok] in HOk. apply andb_true_iff in HOk. destruct HOk as [H1 H2].
  apply andb_true_iff in H1. destruct H1 as [H1 H3]. apply andb_true_iff in H1. destruct H1 as [H1 H4].
  apply Z.leb_le in H1, H4. apply Z.eqb_eq in H3.
  assert (VA : Mem.valid_access m ch b o Writable).
  { split; [intros x Hx; apply HP; lia|]. apply Z.mod_divide; [|exact H3].
    pose proof (align_chunk_pos ch). lia. }
  destruct (Mem.valid_access_store m ch b o v VA) as [m1 HS]. rewrite HS.
  apply IH; [|exact H2]. intros x Hx. eapply Mem.perm_store_1; [exact HS|apply HP, Hx].
Qed.

Lemma do_stores_frame b l : forall m m',
  do_stores m b l = Some m' ->
  (forall ch b' o, b' <> b -> Mem.load ch m' b' o = Mem.load ch m b' o) /\
  (forall b' o k p, Mem.perm m b' o k p -> Mem.perm m' b' o k p) /\
  (forall b', Mem.valid_block m b' -> Mem.valid_block m' b').
Proof.
  induction l as [|[[o ch] v] l IH]; intros m m' H; cbn [do_stores] in H.
  - injection H as <-. repeat split; auto.
  - destruct (Mem.store ch m b o v) as [m1|] eqn:HS; [|discriminate].
    destruct (IH _ _ H) as (L & P & V). split; [|split].
    + intros ch' b' o' Nb. rewrite L by exact Nb. apply (Mem.load_store_other _ _ _ _ _ _ HS). left; exact Nb.
    + intros b' o' k p Hp. apply P. eapply Mem.perm_store_1; [exact HS|exact Hp].
    + intros b' Hb. apply V. eapply Mem.store_valid_block_1; [exact HS|exact Hb].
Qed.

Definition cell_away (o : Z) (sz : Z) (c : cell) : bool :=
  let '(o', ch', _) := c in (o' + size_chunk ch' <=? o) || (o + sz <=? o').

Lemma do_stores_away b l : forall m m' ch o,
  do_stores m b l = Some m' -> forallb (cell_away o (size_chunk ch)) l = true ->
  Mem.load ch m' b o = Mem.load ch m b o.
Proof.
  induction l as [|[[o' ch'] v'] l IH]; intros m m' ch o H HA; cbn [do_stores] in H.
  - injection H as <-. reflexivity.
  - destruct (Mem.store ch' m b o' v') as [m1|] eqn:HS; [|discriminate].
    cbn [forallb cell_away] in HA. apply andb_true_iff in HA. destruct HA as [H1 H2].
    rewrite (IH _ _ _ _ H H2). apply (Mem.load_store_other _ _ _ _ _ _ HS). right.
    apply orb_true_iff in H1. destruct H1 as [H1|H1]; apply Z.leb_le in H1; [right|left]; exact H1.
Qed.

Fixpoint cells_disj (l : list cell) : bool :=
  match l with
  | [] => true
  | (o, ch, _) :: l' => forallb (cell_away o (size_chunk ch)) l' && cells_disj l'
  end.

Lemma do_stores_get b l : forall m m',
  do_stores m b l = Some m' -> cells_disj l = true ->
  forall o ch v, In (o, ch, v) l -> Mem.load ch m' b o = Some (Val.load_result ch v).
Proof.
  induction l as [|[[o' ch'] v'] l IH]; intros m m' H HD o ch v HIn; [destruct HIn|].
  cbn [do_stores] in H. destruct (Mem.store ch' m b o' v') as [m1|] eqn:HS; [|discriminate].
  cbn [cells_disj] in HD. apply andb_true_iff in HD. destruct HD as [H1 H2].
  destruct HIn as [E|HIn].
  - injection E as -> -> ->. rewrite (do_stores_away _ _ _ _ _ _ H H1).
    apply (Mem.load_store_same _ _ _ _ _ _ HS).
  - exact (IH _ _ H H2 _ _ _ HIn).
Qed.

Lemma lit_add_repr a b : Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a + b).
Proof.
  unfold Ptrofs.add. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

Lemma lit_index_repr a (k : int) :
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints k)) = Ptrofs.repr (a + 4 * Int.signed k).
Proof.
  unfold Ptrofs.add, Ptrofs.mul, Ptrofs.of_ints. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; [apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr|].
  eapply Ptrofs.eqm_trans; [apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr|].
  apply Ptrofs.eqm_mult; apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

Local Opaque sha_ge.

Ltac nd H := try (cbv beta iota in H; match type of H with None = Some _ => discriminate H end).

Section Lit.
Variables (e : env) (cid : ident) (bK : block) (tyK : type).
Hypothesis HeK : e!cid = Some (bK, tyK).
Variable ce : composite_env.
Hypothesis Hce : ce = Clight.genv_cenv sha_ge.

Fixpoint lv_off (a : expr) : option Z :=
  match a with
  | Evar id ty => if ident_eq id cid then if type_eq ty tyK then Some 0 else None else None
  | Efield a' f _ =>
      match lv_off a' with
      | Some d =>
          match typeof a' with
          | Tstruct sid _ =>
              match ce!sid with
              | Some co =>
                  match field_offset ce f (co_members co) with
                  | OK (delta, Full) => Some (d + delta)
                  | _ => None
                  end
              | None => None
              end
          | Tunion uid _ =>
              match ce!uid with
              | Some co =>
                  match union_field_offset ce f (co_members co) with
                  | OK (delta, Full) => Some (d + delta)
                  | _ => None
                  end
              | None => None
              end
          | _ => None
          end
      | None => None
      end
  | Ederef (Ebinop Oadd a' (Econst_int k (Tint I32 Signed _)) _) _ =>
      match lv_off a' with
      | Some d =>
          match typeof a' with
          | Tarray (Tint I32 _ _) _ _ => Some (d + 4 * Int.signed k)
          | _ => None
          end
      | None => None
      end
  | _ => None
  end.

Lemma lv_sound le m : forall a d,
  lv_off a = Some d -> eval_lvalue sha_ge e le m a bK (Ptrofs.repr d) Full.
Proof.
  fix F 1. intros a d H. destruct a; cbn [lv_off] in H; nd H.
  - destruct (ident_eq i cid) as [->|]; [|nd H]. destruct (type_eq t tyK) as [->|]; [|nd H].
    injection H as <-. apply eval_Evar_local. exact HeK.
  - destruct a; nd H. destruct b; nd H. destruct a2; nd H.
    destruct t1; nd H. destruct i0; nd H. destruct s; nd H.
    destruct (lv_off a1) as [d1|] eqn:E1; [|nd H].
    destruct (typeof a1) as [| | | | |telt n att| | | ] eqn:ET; nd H.
    destruct telt; nd H. destruct i0; nd H. injection H as <-.
    apply eval_Ederef. eapply eval_Ebinop.
    + eapply eval_Elvalue; [exact (F a1 _ E1)|]. apply deref_loc_reference. rewrite ET. reflexivity.
    + apply eval_Econst_int.
    + rewrite ET. cbn. rewrite lit_index_repr. reflexivity.
  - destruct (lv_off a) as [d1|] eqn:E1; [|nd H].
    destruct (typeof a) as [| | | | | | |sid att|uid att] eqn:ET; nd H.
    + destruct (ce!sid) as [co|] eqn:EC; [|nd H].
      destruct (field_offset ce i (co_members co)) as [[delta bf]|] eqn:EF; [|nd H].
      destruct bf; nd H. injection H as <-. rewrite <- lit_add_repr.
      rewrite Hce in EC, EF. eapply eval_Efield_struct; [|exact ET|exact EC|exact EF].
      eapply eval_Elvalue; [exact (F a _ E1)|]. apply deref_loc_copy. rewrite ET. reflexivity.
    + destruct (ce!uid) as [co|] eqn:EC; [|nd H].
      destruct (union_field_offset ce i (co_members co)) as [[delta bf]|] eqn:EF; [|nd H].
      destruct bf; nd H. injection H as <-. rewrite <- lit_add_repr.
      rewrite Hce in EC, EF. eapply eval_Efield_union; [|exact ET|exact EC|exact EF].
      eapply eval_Elvalue; [exact (F a _ E1)|]. apply deref_loc_copy. rewrite ET. reflexivity.
Qed.

(** The cell of a constant zero stored at a scalar type. *)
Definition zcell (ty : type) : option (memory_chunk * val) :=
  match ty with
  | Tint I32 _ _ => Some (Mint32, Vint Int.zero)
  | Tint IBool _ _ => Some (Mint8unsigned, Vint Int.zero)
  | Tlong _ _ => Some (Mint64, Vlong Int64.zero)
  | Tpointer _ _ => Some (Mptr, Vlong Int64.zero)
  | _ => None
  end.

Lemma zcell_sound ty ch v att m :
  zcell ty = Some (ch, v) ->
  access_mode ty = By_value ch /\ sem_cast (Vint Int.zero) (Tint I32 Signed att) ty m = Some v.
Proof.
  intros H. destruct ty as [|sz sg a|sg a| | | | | |]; cbn [zcell] in H; nd H.
  - destruct sz; nd H; injection H as <- <-; destruct sg; split; reflexivity.
  - injection H as <- <-. destruct sg; split; reflexivity.
  - injection H as <- <-. split; reflexivity.
Qed.

(** [zrun n s]: the last [n] statements of the left-nested sequence [s] are
    zero assignments into the local; the result is the remaining prefix
    (if any) and the cells in execution order. *)
Fixpoint zrun (n : nat) (s : statement) : option (option statement * list cell) :=
  match n with
  | O => Some (Some s, [])
  | S k =>
      match s with
      | Ssequence s' (Sassign lv (Econst_int z (Tint I32 Signed _))) =>
          match zrun k s', lv_off lv, zcell (typeof lv) with
          | Some (acc, cs), Some d, Some (ch, v) =>
              if Int.eq z Int.zero && (0 <=? d) && (d <=? 1000000) then Some (acc, cs ++ [(d, ch, v)]) else None
          | _, _, _ => None
          end
      | Sassign lv (Econst_int z (Tint I32 Signed _)) =>
          match k, lv_off lv, zcell (typeof lv) with
          | O, Some d, Some (ch, v) =>
              if Int.eq z Int.zero && (0 <=? d) && (d <=? 1000000) then Some (None, [(d, ch, v)]) else None
          | _, _, _ => None
          end
      | _ => None
      end
  end.

Lemma zassign_exec le m m' lv z att d ch v :
  lv_off lv = Some d -> zcell (typeof lv) = Some (ch, v) ->
  Int.eq z Int.zero && (0 <=? d) && (d <=? 1000000) = true ->
  Mem.store ch m bK d v = Some m' ->
  Clight2.exec_stmt sha_ge e le m (Sassign lv (Econst_int z (Tint I32 Signed att))) E0 le m' Out_normal.
Proof.
  intros HL HZ HC HS. apply andb_true_iff in HC. destruct HC as [HC H2]. apply andb_true_iff in HC.
  destruct HC as [H0 H1]. apply Z.leb_le in H1, H2.
  pose proof (Int.eq_spec z Int.zero) as HE. rewrite H0 in HE. subst z.
  destruct (zcell_sound _ _ _ att m HZ) as [HA HCast].
  eapply exec_Sassign with (v2 := Vint Int.zero) (v := v).
  - apply lv_sound. exact HL.
  - apply eval_Econst_int.
  - exact HCast.
  - eapply assign_loc_value; [exact HA|]. unfold Mem.storev.
    rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615; lia). exact HS.
Qed.

Lemma zrun_sound n : forall s acc cs,
  zrun n s = Some (acc, cs) ->
  forall le0 le m0 m1 m2,
  match acc with
  | Some a => Clight2.exec_stmt sha_ge e le0 m0 a E0 le m1 Out_normal
  | None => le = le0 /\ m1 = m0
  end ->
  do_stores m1 bK cs = Some m2 ->
  Clight2.exec_stmt sha_ge e le0 m0 s E0 le m2 Out_normal.
Proof.
  induction n as [|n IH]; intros s acc cs H le0 le m0 m1 m2 HA HS.
  - cbn in H. injection H as <- <-. cbn in HS. injection HS as <-. exact HA.
  - cbn [zrun] in H. destruct s; nd H.
    + (* a single assignment *)
      destruct e1; nd H. destruct t; nd H. destruct i0; nd H.
      destruct s; nd H. destruct n; nd H.
      destruct (lv_off e0) as [d|] eqn:EL; [|nd H].
      destruct (zcell (typeof e0)) as [[ch v]|] eqn:EZ; [|nd H].
      destruct (Int.eq i Int.zero && (0 <=? d) && (d <=? 1000000)) eqn:EC; [|nd H].
      injection H as <- <-. destruct HA as [-> ->]. cbn [do_stores] in HS.
      destruct (Mem.store ch m0 bK d v) as [mx|] eqn:HSt; [|discriminate]. injection HS as <-.
      eapply zassign_exec; eassumption.
    + destruct s2; nd H. destruct e1; nd H. destruct t; nd H.
      destruct i0; nd H. destruct s; nd H.
      destruct (zrun n s1) as [[acc' cs']|] eqn:ER; [|nd H].
      destruct (lv_off e0) as [d|] eqn:EL; [|nd H].
      destruct (zcell (typeof e0)) as [[ch v]|] eqn:EZ; [|nd H].
      destruct (Int.eq i Int.zero && (0 <=? d) && (d <=? 1000000)) eqn:EC; [|nd H].
      injection H as <- <-. rewrite do_stores_app in HS.
      destruct (do_stores m1 bK cs') as [mm|] eqn:HS1; [|discriminate]. cbn [do_stores] in HS.
      destruct (Mem.store ch mm bK d v) as [mx|] eqn:HSt; [|discriminate]. injection HS as <-.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact (IH _ _ _ ER _ _ _ _ _ HA HS1)|].
      eapply zassign_exec; eassumption.
Qed.
End Lit.
