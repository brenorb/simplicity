(** [secp256k1_fe_normalize_var] computes the canonical limbs of its
    argument modulo the field prime. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_exec C.jet_sx_pure.
Require Import C.jet_sx_zval C.jet_sx_rep C.jet_sx_zrep.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns C.jet_secp_fe_math.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 600.

(** A field element in memory: five 64-bit limbs. *)
Definition fe_at (m : mem) (b : block) (ofs : Z) (l : list int64) : Prop :=
  0 <= ofs /\ (8 | ofs) /\ ofs + 40 <= Ptrofs.max_unsigned /\
  Mem.range_perm m b ofs (ofs + 40) Cur Writable /\
  forall i x, nth_error l i = Some x -> Mem.load Mint64 m b (ofs + 8 * Z.of_nat i) = Some (Vlong x).

Definition fe_reg (xs : list sx) : region := mkreg (u64_cells 0 xs) true None.
Definition vars5 (n : nat) : list sx := [XLv n; XLv (n + 1); XLv (n + 2); XLv (n + 3); XLv (n + 4)].
Definition rho5 (t0 t1 t2 t3 t4 : int64) (n : nat) : int64 := nth n [t0; t1; t2; t3; t4] Int64.zero.

Lemma fe_at_rep m b ofs t0 t1 t2 t3 t4 :
  fe_at m b ofs [t0; t1; t2; t3; t4] ->
  rep (rho5 t0 t1 t2 t3 t4) [(b, ofs)] [fe_reg (vars5 0)] m.
Proof.
  intros (H0 & Hal & Hmax & Hperm & Hl).
  apply (rep_add _ [] [] m b ofs); [apply rep_nil|simpl; tauto|].
  apply region_u64; unfold blk, bas, lay; simpl; try assumption; try lia.
  - eapply Mem.perm_valid_block. apply (Hperm ofs). lia.
  - intros i x Hn.
    destruct i as [|i]; [inversion Hn; subst x; split; [exact (Hl 0%nat _ eq_refl)|reflexivity]|].
    destruct i as [|i]; [inversion Hn; subst x; split; [exact (Hl 1%nat _ eq_refl)|reflexivity]|].
    destruct i as [|i]; [inversion Hn; subst x; split; [exact (Hl 2%nat _ eq_refl)|reflexivity]|].
    destruct i as [|i]; [inversion Hn; subst x; split; [exact (Hl 3%nat _ eq_refl)|reflexivity]|].
    destruct i as [|i]; [inversion Hn; subst x; split; [exact (Hl 4%nat _ eq_refl)|reflexivity]|].
    destruct i; discriminate.
Qed.

Definition nv_run : option res :=
  xfun (genv_cenv secp_ge) [] (int_table secp_pure) 400 f_secp256k1_fe_normalize_var
    [XP 0 0] [fe_reg (vars5 0)] [] 5.
Definition nv_tree : option res := Eval vm_compute in nv_run.
Definition nv_c : sx :=
  Eval vm_compute in match nv_tree with Some (RIf c _ _) => c | _ => XIc Int.zero end.
Definition nv_a : sstate :=
  Eval vm_compute in match nv_tree with Some (RIf _ (RDone a _) _) => a | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition nv_b : sstate :=
  Eval vm_compute in match nv_tree with Some (RIf _ _ (RDone b _)) => b | _ => mkst (PTree.empty sx) [] [] 0 end.

Lemma nv_run_eq : nv_run = Some (RIf nv_c (RDone nv_a ONormal) (RDone nv_b ONormal)).
Proof. vm_cast_no_check (eq_refl (Some (RIf nv_c (RDone nv_a ONormal) (RDone nv_b ONormal)))). Qed.

Definition nvz_list (z0 z1 z2 z3 z4 : Z) : list Z :=
  match nvz z0 z1 z2 z3 z4 with (r0, r1, r2, r3, r4) => [r0; r1; r2; r3; r4] end.
Definition cells0 (Σ : sstate) : list cell := rcells (hd (mkreg [] true None) (sregs Σ)).
Definition zrho5 (z0 z1 z2 z3 z4 : Z) (n : nat) : Z := nth n [z0; z1; z2; z3; z4] 0.

Lemma nv_bridge z0 z1 z2 z3 z4 :
  nvz_list z0 z1 z2 z3 z4 =
  if negb (Z.eqb (zval (zrho5 z0 z1 z2 z3 z4) nv_c) 0)
  then zcells (zrho5 z0 z1 z2 z3 z4) (cells0 nv_a)
  else zcells (zrho5 z0 z1 z2 z3 z4) (cells0 nv_b).
Proof.
  destruct (negb (Z.eqb (zval (zrho5 z0 z1 z2 z3 z4) nv_c) 0)) eqn:E.
  - cbv beta iota zeta delta [nvz_list nvz nv_pass].
    match goal with |- context[if ?c then _ else _] =>
      change c with (negb (Z.eqb (zval (zrho5 z0 z1 z2 z3 z4) nv_c) 0)) end.
    rewrite E. reflexivity.
  - cbv beta iota zeta delta [nvz_list nvz nv_pass].
    match goal with |- context[if ?c then _ else _] =>
      change c with (negb (Z.eqb (zval (zrho5 z0 z1 z2 z3 z4) nv_c) 0)) end.
    rewrite E. reflexivity.
Qed.

Lemma zrho_rho5 t0 t1 t2 t3 t4 n :
  zrho (rho5 t0 t1 t2 t3 t4) n =
  zrho5 (Int64.unsigned t0) (Int64.unsigned t1) (Int64.unsigned t2) (Int64.unsigned t3) (Int64.unsigned t4) n.
Proof. unfold zrho, rho5, zrho5. do 5 (destruct n as [|n]; [reflexivity|]). destruct n; reflexivity. Qed.

Lemma zcells_ext (z1 z2 : nat -> Z) cs : (forall n, z1 n = z2 n) -> zcells z1 cs = zcells z2 cs.
Proof.
  intros H. unfold zcells. apply map_ext. intros c. destruct (cval c); [apply zval_ext; exact H|reflexivity].
Qed.

Lemma fe_foot b ofs xs b' o :
  length xs = 5%nat ->
  foot [(b, ofs)] (map rshape [fe_reg xs]) b' o -> b' = b /\ ofs <= o < ofs + 40.
Proof.
  intros Hlen (r & s & d & ch & Hs & Hin & -> & Hr).
  destruct r; [|destruct r; discriminate]. simpl in Hs. inversion Hs; subst s; clear Hs.
  unfold blk, bas, lay in *. simpl in *.
  do 6 (destruct xs as [|? xs]; try discriminate). simpl in Hin.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; try contradiction;
    inversion Hin; subst; simpl in Hr; split; try reflexivity; lia.
Qed.

Theorem eval_fe_normalize_var m b ofs t0 t1 t2 t3 t4 :
  fe_at m b ofs [t0; t1; t2; t3; t4] ->
  Int64.unsigned t0 <= 2 ^ 60 -> Int64.unsigned t1 <= 2 ^ 60 -> Int64.unsigned t2 <= 2 ^ 60 ->
  Int64.unsigned t3 <= 2 ^ 60 -> Int64.unsigned t4 <= 2 ^ 60 ->
  exists m',
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_var)
      [Vptr b (Ptrofs.repr ofs)] E0 m' Vundef /\
    fe_at m' b ofs (map Int64.repr (nvz_list (Int64.unsigned t0) (Int64.unsigned t1) (Int64.unsigned t2)
                                      (Int64.unsigned t3) (Int64.unsigned t4))) /\
    lframe (fun b' o => ~ (b' = b /\ ofs <= o < ofs + 40)) m m'.
Proof.
  intros Hfe B0 B1 B2 B3 B4.
  set (ρ := rho5 t0 t1 t2 t3 t4). set (bnd := fun _ : nat => (0, 2 ^ 60)).
  assert (Hb : forall n, fst (bnd n) <= Int64.unsigned (ρ n) <= snd (bnd n)).
  { intros n. unfold bnd, ρ, rho5. simpl fst; simpl snd.
    do 5 (destruct n as [|n]; [simpl; split; [apply Int64.unsigned_range|assumption]|]).
    destruct n; simpl; change (Int64.unsigned Int64.zero) with 0; lia. }
  pose proof (fe_at_rep m b ofs t0 t1 t2 t3 t4 Hfe) as Hrep. fold ρ in Hrep.
  destruct (xfun_pure secp_ge secp_pure secp_pure_ok 400 f_secp256k1_fe_normalize_var [XP 0 0]
              [fe_reg (vars5 0)] 5 _ nv_run_eq eq_refl ρ [(b, ofs)] m Hrep)
    as (m' & vres & Hev & Hrep' & Hret & Hsh & Hun).
  change (map (den ρ (lay [(b, ofs)])) [XP 0 0]) with [Vptr b (Ptrofs.repr (ofs + 0))] in Hev.
  rewrite Z.add_0_r in Hev.
  cbn [rsel] in Hrep', Hret.
  assert (Htr : truth ρ (lay [(b, ofs)]) nv_c = negb (Z.eqb (zval (zrho ρ) nv_c) 0)).
  { eapply truth_zval; [exact Hb|vm_compute; reflexivity|reflexivity]. }
  rewrite Htr in Hrep', Hret.
  assert (Ez : zval (zrho ρ) nv_c =
    zval (zrho5 (Int64.unsigned t0) (Int64.unsigned t1) (Int64.unsigned t2) (Int64.unsigned t3) (Int64.unsigned t4)) nv_c)
    by (apply zval_ext; exact (zrho_rho5 t0 t1 t2 t3 t4)).
  rewrite Ez in Hrep', Hret.
  rewrite nv_bridge.
  destruct Hfe as (H0 & Hal & Hmax & Hperm & Hl).
  assert (Hfin : forall Σ, zreg_okb bnd 0 (cells0 Σ) = true -> length (cells0 Σ) = 5%nat ->
            (exists reg, nth_error (sregs Σ) 0 = Some reg /\ rcells reg = cells0 Σ /\ rw reg = true) ->
            rep ρ [(b, ofs)] (sregs Σ) m' ->
            fe_at m' b ofs (map Int64.repr (zcells
              (zrho5 (Int64.unsigned t0) (Int64.unsigned t1) (Int64.unsigned t2) (Int64.unsigned t3) (Int64.unsigned t4))
              (cells0 Σ)))).
  { intros Σ Hok Hlen (reg & Hreg & Hcs & Hw) HrepΣ.
    destruct (rep_region _ _ _ _ _ _ HrepΣ Hreg) as (_ & _ & _ & Hcells & _).
    rewrite Hcs, Hw in Hcells.
    destruct (zreg_load ρ bnd [(b, ofs)] Hb m' 0%nat true (cells0 Σ) 0 Hok Hcells) as [Hld Hpm].
    unfold blk, bas, lay in Hld, Hpm. cbn [nth fst snd] in Hld, Hpm. rewrite Hlen in Hpm.
    split; [exact H0|]. split; [exact Hal|]. split; [exact Hmax|]. split.
    - intros o Ho. apply Hpm. lia.
    - intros i x Hn. rewrite nth_error_map in Hn.
      rewrite <- (zcells_ext _ _ (cells0 Σ) (zrho_rho5 t0 t1 t2 t3 t4)) in Hn. fold ρ in Hn.
      destruct (nth_error (zcells (zrho ρ) (cells0 Σ)) i) as [z|] eqn:Ezi; [|discriminate].
      inversion Hn; subst x. rewrite <- (Hld i z Ezi). f_equal; lia. }
  assert (Hvres : forall Σ, (stemps Σ)!1%positive = None ->
            match (stemps Σ)!1%positive with Some x => vres = den ρ (lay [(b, ofs)]) x | None => vres = Vundef end ->
            vres = Vundef) by (intros Σ E H; rewrite E in H; exact H).
  assert (Hunch : lframe (fun b' o => ~ (b' = b /\ ofs <= o < ofs + 40)) m m').
  { eapply lframe_implies; [exact Hun|]. intros b' o Hn Hv Hf.
    apply Hn. exact (fe_foot b ofs (vars5 0) b' o eq_refl Hf). }
  destruct (negb (Z.eqb (zval _ nv_c) 0)).
  - exists m'. cbn [fst] in Hrep', Hret.
    rewrite (Hvres nv_a eq_refl Hret) in Hev. split; [exact Hev|]. split; [|exact Hunch].
    apply Hfin; [vm_compute; reflexivity|reflexivity| |exact Hrep'].
    eexists. split; [reflexivity|]. split; reflexivity.
  - exists m'. cbn [fst] in Hrep', Hret.
    rewrite (Hvres nv_b eq_refl Hret) in Hev. split; [exact Hev|]. split; [|exact Hunch].
    apply Hfin; [vm_compute; reflexivity|reflexivity| |exact Hrep'].
    eexists. split; [reflexivity|]. split; reflexivity.
Qed.
