(** Symbolic values for a verified symbolic executor of straight-line Clight
    code: a small expression language over machine integers and pointers
    into named memory regions, its denotation as CompCert values, and the
    agreement of its operators with the C operator semantics of [Cop]. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Maps Values Memory.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Inductive kind := KI | KL | KP | KA | KV.
Inductive bop := Badd | Bsub | Bmul | Band | Bor | Bxor.
Inductive shop := Hshl | Hshr | Hshru.

Inductive sx : Type :=
| XI (i : int) | XIc (i : int)
| XL (l : int64) | XLc (l : int64)
| XLv (n : nat)
| XV (v : val)
| XA (b : block) (o : ptrofs)
| XP (r : nat) (d : Z)
| XIb (o : bop) (a b : sx)
| XLb (o : bop) (a b : sx)
| XIsh (o : shop) (a : sx) (k : Z)
| XLsh (o : shop) (a : sx) (k : Z)
| XIcmp (c : comparison) (sg : signedness) (a b : sx)
| XLcmp (c : comparison) (sg : signedness) (a b : sx)
| XI2L (sg : signedness) (a : sx)
| XL2I (a : sx)
| XIcast (sz : intsize) (sg : signedness) (a : sx)
| XInz (a : sx) | XLnz (a : sx)
| XIz (a : sx) | XLz (a : sx)
| XIneg (a : sx) | XLneg (a : sx)
| XInot (a : sx) | XLnot (a : sx).

Definition ii (v : val) : int := match v with Vint i => i | _ => Int.zero end.
Definition il (v : val) : int64 := match v with Vlong l => l | _ => Int64.zero end.
Definition b2i (b : bool) : int := if b then Int.one else Int.zero.

Definition iop (o : bop) : int -> int -> int :=
  match o with Badd => Int.add | Bsub => Int.sub | Bmul => Int.mul
             | Band => Int.and | Bor => Int.or | Bxor => Int.xor end.
Definition lop (o : bop) : int64 -> int64 -> int64 :=
  match o with Badd => Int64.add | Bsub => Int64.sub | Bmul => Int64.mul
             | Band => Int64.and | Bor => Int64.or | Bxor => Int64.xor end.
Definition ish (o : shop) (a : int) (k : Z) : int :=
  match o with Hshl => Int.shl a (Int.repr k) | Hshr => Int.shr a (Int.repr k)
             | Hshru => Int.shru a (Int.repr k) end.
Definition lsh (o : shop) (a : int64) (k : Z) : int64 :=
  match o with Hshl => Int64.shl a (Int64.repr k) | Hshr => Int64.shr a (Int64.repr k)
             | Hshru => Int64.shru a (Int64.repr k) end.
Definition icmp (c : comparison) (sg : signedness) (a b : int) : bool :=
  match sg with Signed => Int.cmp c a b | Unsigned => Int.cmpu c a b end.
Definition lcmp (c : comparison) (sg : signedness) (a b : int64) : bool :=
  match sg with Signed => Int64.cmp c a b | Unsigned => Int64.cmpu c a b end.
Definition i2l (sg : signedness) (a : int) : int64 :=
  match sg with Signed => Int64.repr (Int.signed a) | Unsigned => Int64.repr (Int.unsigned a) end.

(** The layout [β] gives the block and base offset of each region, the
    valuation [ρ] the value of each symbolic variable. *)
Fixpoint den (ρ : nat -> int64) (β : nat -> block * Z) (x : sx) : val :=
  match x with
  | XI i | XIc i => Vint i
  | XL l | XLc l => Vlong l
  | XLv n => Vlong (ρ n)
  | XV v => v
  | XA b o => Vptr b o
  | XP r d => Vptr (fst (β r)) (Ptrofs.repr (snd (β r) + d))
  | XIb o a b => Vint (iop o (ii (den ρ β a)) (ii (den ρ β b)))
  | XLb o a b => Vlong (lop o (il (den ρ β a)) (il (den ρ β b)))
  | XIsh o a k => Vint (ish o (ii (den ρ β a)) k)
  | XLsh o a k => Vlong (lsh o (il (den ρ β a)) k)
  | XIcmp c sg a b => Vint (b2i (icmp c sg (ii (den ρ β a)) (ii (den ρ β b))))
  | XLcmp c sg a b => Vint (b2i (lcmp c sg (il (den ρ β a)) (il (den ρ β b))))
  | XI2L sg a => Vlong (i2l sg (ii (den ρ β a)))
  | XL2I a => Vint (Int64.loword (il (den ρ β a)))
  | XIcast sz sg a => Vint (cast_int_int sz sg (ii (den ρ β a)))
  | XInz a => Vint (b2i (negb (Int.eq (ii (den ρ β a)) Int.zero)))
  | XLnz a => Vint (b2i (negb (Int64.eq (il (den ρ β a)) Int64.zero)))
  | XIz a => Vint (b2i (Int.eq (ii (den ρ β a)) Int.zero))
  | XLz a => Vint (b2i (Int64.eq (il (den ρ β a)) Int64.zero))
  | XIneg a => Vint (Int.neg (ii (den ρ β a)))
  | XLneg a => Vlong (Int64.neg (il (den ρ β a)))
  | XInot a => Vint (Int.not (ii (den ρ β a)))
  | XLnot a => Vlong (Int64.not (il (den ρ β a)))
  end.

Definition ktop (x : sx) : kind :=
  match x with
  | XI _ | XIc _ | XIb _ _ _ | XIsh _ _ _ | XIcmp _ _ _ _ | XLcmp _ _ _ _ | XL2I _
  | XIcast _ _ _ | XInz _ | XLnz _ | XIz _ | XLz _ | XIneg _ | XInot _ => KI
  | XL _ | XLc _ | XLv _ | XLb _ _ _ | XLsh _ _ _ | XI2L _ _ | XLneg _ | XLnot _ => KL
  | XP _ _ => KP
  | XV _ => KV
  | XA _ _ => KA
  end.

Definition kind_eqb (a b : kind) : bool :=
  match a, b with KI, KI | KL, KL | KP, KP | KV, KV | KA, KA => true | _, _ => false end.
Lemma kind_eqb_eq a b : kind_eqb a b = true -> a = b.
Proof. destruct a, b; simpl; congruence. Qed.
Definition isk (k : kind) (x : sx) : bool := kind_eqb (ktop x) k.

Lemma den_KI ρ β x : isk KI x = true -> den ρ β x = Vint (ii (den ρ β x)).
Proof. destruct x; simpl; intros H; try discriminate; reflexivity. Qed.
Lemma den_KL ρ β x : isk KL x = true -> den ρ β x = Vlong (il (den ρ β x)).
Proof. destruct x; simpl; intros H; try discriminate; reflexivity. Qed.
Lemma den_KP x : isk KP x = true -> exists r d, x = XP r d.
Proof. destruct x; simpl; intros H; try discriminate; eauto. Qed.
Lemma den_KA x : isk KA x = true -> exists b o, x = XA b o.
Proof. destruct x; simpl; intros H; try discriminate; eauto. Qed.

(** ** Casts *)
Definition xcast (x : sx) (t1 t2 : type) : option sx :=
  match t2, t1 with
  | Tint IBool _ _, Tint _ _ _ => if isk KI x then Some (XInz x) else None
  | Tint IBool _ _, Tlong _ _ => if isk KL x then Some (XLnz x) else None
  | Tint sz2 sg2 _, Tint _ _ _ =>
      if isk KI x then Some (match sz2 with I32 => x | _ => XIcast sz2 sg2 x end) else None
  | Tint sz2 sg2 _, Tlong _ _ =>
      if isk KL x then Some (match sz2 with I32 => XL2I x | _ => XIcast sz2 sg2 (XL2I x) end) else None
  | Tlong _ _, Tlong _ _ => if isk KL x then Some x else None
  | Tlong _ _, Tint _ sg1 _ => if isk KI x then Some (XI2L sg1 x) else None
  | Tpointer _ _, (Tpointer _ _ | Tarray _ _ _) => if isk KP x || isk KA x then Some x else None
  | _, _ => None
  end.

Lemma xcast_sound ρ β x t1 t2 x' m :
  xcast x t1 t2 = Some x' -> sem_cast (den ρ β x) t1 t2 m = Some (den ρ β x').
Proof.
  unfold xcast. intros H.
  destruct t2 as [| sz2 sg2 a2 | sg2 a2 | f2 a2 | t2' a2 | t2' n2 a2 | targs2 tres2 cc2 | id2 a2 | id2 a2];
    try discriminate;
  destruct t1 as [| sz1 sg1 a1 | sg1 a1 | f1 a1 | t1' a1 | t1' n1 a1 | targs1 tres1 cc1 | id1 a1 | id1 a1];
    try discriminate; try (destruct sz2; discriminate).
  - (* int <- int *)
    destruct sz2; destruct (isk KI x) eqn:K; try discriminate; inversion H; subst x';
      rewrite (den_KI ρ β x K); try reflexivity;
      try (unfold sem_cast; simpl; destruct sg2; reflexivity);
      unfold sem_cast; simpl; destruct (Int.eq (ii (den ρ β x)) Int.zero); reflexivity.
  - (* int <- long *)
    destruct sz2; destruct (isk KL x) eqn:K; try discriminate; inversion H; subst x';
      rewrite (den_KL ρ β x K); try reflexivity;
      try (unfold sem_cast; simpl; destruct sg2; reflexivity);
      unfold sem_cast; simpl; destruct (Int64.eq (il (den ρ β x)) Int64.zero); reflexivity.
  - (* long <- int *)
    destruct (isk KI x) eqn:K; try discriminate; inversion H; subst x'.
    rewrite (den_KI ρ β x K). unfold sem_cast; simpl. destruct sg1; reflexivity.
  - (* long <- long *)
    destruct (isk KL x) eqn:K; try discriminate; inversion H; subst x'.
    rewrite (den_KL ρ β x K). reflexivity.
  - destruct (isk KP x) eqn:K; simpl in H.
    + inversion H; subst x'. destruct (den_KP x K) as (r & d & ->). reflexivity.
    + destruct (isk KA x) eqn:K2; try discriminate; inversion H; subst x'.
      destruct (den_KA x K2) as (b & o & ->). reflexivity.
  - destruct (isk KP x) eqn:K; simpl in H.
    + inversion H; subst x'. destruct (den_KP x K) as (r & d & ->). reflexivity.
    + destruct (isk KA x) eqn:K2; try discriminate; inversion H; subst x'.
      destruct (den_KA x K2) as (b & o & ->). reflexivity.
Qed.

(** ** Binary arithmetic *)
Definition isg (t : type) : signedness :=
  match t with Tint I32 Unsigned _ => Unsigned | _ => Signed end.
Definition sgjoin (a b : signedness) : signedness :=
  match a, b with Signed, Signed => Signed | _, _ => Unsigned end.

Definition xbinarith (mki mkl : signedness -> sx -> sx -> sx)
    (xa : sx) (ta : type) (xb : sx) (tb : type) : option sx :=
  match ta, tb with
  | Tint _ _ _, Tint _ _ _ =>
      if isk KI xa && isk KI xb then Some (mki (sgjoin (isg ta) (isg tb)) xa xb) else None
  | Tlong sga _, Tlong sgb _ =>
      if isk KL xa && isk KL xb then Some (mkl (sgjoin sga sgb) xa xb) else None
  | Tlong sga _, Tint _ sgb _ =>
      if isk KL xa && isk KI xb then Some (mkl sga xa (XI2L sgb xb)) else None
  | Tint _ sga _, Tlong sgb _ =>
      if isk KI xa && isk KL xb then Some (mkl sgb (XI2L sga xa) xb) else None
  | _, _ => None
  end.

Section BINARITH.
Variables (ρ : nat -> int64) (β : nat -> block * Z).
Variables (fi : signedness -> int -> int -> option val) (fl : signedness -> int64 -> int64 -> option val).
Variables (ff : Floats.float -> Floats.float -> option val) (fs : Floats.float32 -> Floats.float32 -> option val).
Variables (mki mkl : signedness -> sx -> sx -> sx).
Hypothesis Hi : forall sg a b, fi sg (ii (den ρ β a)) (ii (den ρ β b)) = Some (den ρ β (mki sg a b)).
Hypothesis Hl : forall sg a b, fl sg (il (den ρ β a)) (il (den ρ β b)) = Some (den ρ β (mkl sg a b)).

Lemma xbinarith_sound xa ta xb tb x m :
  xbinarith mki mkl xa ta xb tb = Some x ->
  sem_binarith fi fl ff fs (den ρ β xa) ta (den ρ β xb) tb m = Some (den ρ β x).
Proof.
  unfold xbinarith. intros H.
  destruct ta as [| sza sga aa | sga aa | fa aa | ta' aa | ta' na aa | targsa tresa cca | ida aa | ida aa];
    try discriminate;
  destruct tb as [| szb sgb ab | sgb ab | fb ab | tb' ab | tb' nb ab | targsb tresb ccb | idb ab | idb ab];
    try discriminate.
  - destruct (isk KI xa) eqn:Ka; [|discriminate]. destruct (isk KI xb) eqn:Kb; [|discriminate].
    inversion H; subst x. rewrite <- Hi.
    rewrite (den_KI ρ β xa Ka), (den_KI ρ β xb Kb).
    destruct sza, sga, szb, sgb; reflexivity.
  - destruct (isk KI xa) eqn:Ka; [|discriminate]. destruct (isk KL xb) eqn:Kb; [|discriminate].
    inversion H; subst x. rewrite <- Hl.
    rewrite (den_KI ρ β xa Ka), (den_KL ρ β xb Kb).
    destruct sza, sga, sgb; reflexivity.
  - destruct (isk KL xa) eqn:Ka; [|discriminate]. destruct (isk KI xb) eqn:Kb; [|discriminate].
    inversion H; subst x. rewrite <- Hl.
    rewrite (den_KL ρ β xa Ka), (den_KI ρ β xb Kb).
    destruct sga, szb, sgb; reflexivity.
  - destruct (isk KL xa) eqn:Ka; [|discriminate]. destruct (isk KL xb) eqn:Kb; [|discriminate].
    inversion H; subst x. rewrite <- Hl.
    rewrite (den_KL ρ β xa Ka), (den_KL ρ β xb Kb).
    destruct sga, sgb; reflexivity.
Qed.
End BINARITH.

Lemma xbinarith_arith mki mkl xa ta xb tb x :
  xbinarith mki mkl xa ta xb tb = Some x ->
  (exists sz sg a, ta = Tint sz sg a) \/ (exists sg a, ta = Tlong sg a).
Proof.
  unfold xbinarith. destruct ta; try discriminate; eauto.
Qed.
Lemma xbinarith_arith_r mki mkl xa ta xb tb x :
  xbinarith mki mkl xa ta xb tb = Some x ->
  (exists sz sg a, tb = Tint sz sg a) \/ (exists sg a, tb = Tlong sg a).
Proof.
  unfold xbinarith. destruct ta; try discriminate; destruct tb; try discriminate; eauto.
Qed.

(** ** Shifts by a constant amount *)
Definition xshift (left : bool) (xa : sx) (ta : type) (xb : sx) (tb : type) : option sx :=
  match xb with
  | XIc n =>
      match ta, tb with
      | Tint _ _ _, Tint _ _ _ =>
          if isk KI xa && Int.ltu n Int.iwordsize
          then Some (XIsh (if left then Hshl else match isg ta with Signed => Hshr | Unsigned => Hshru end)
                          xa (Int.unsigned n))
          else None
      | Tlong sg _, Tint _ _ _ =>
          if isk KL xa && Int.ltu n Int64.iwordsize'
          then Some (XLsh (if left then Hshl else match sg with Signed => Hshr | Unsigned => Hshru end)
                          xa (Int.unsigned n))
          else None
      | _, _ => None
      end
  | XLc n =>
      match ta, tb with
      | Tint _ _ _, Tlong _ _ =>
          if isk KI xa && Int64.ltu n (Int64.repr 32)
          then Some (XIsh (if left then Hshl else match isg ta with Signed => Hshr | Unsigned => Hshru end)
                          xa (Int64.unsigned n))
          else None
      | Tlong sg _, Tlong _ _ =>
          if isk KL xa && Int64.ltu n Int64.iwordsize
          then Some (XLsh (if left then Hshl else match sg with Signed => Hshr | Unsigned => Hshru end)
                          xa (Int64.unsigned n))
          else None
      | _, _ => None
      end
  | _ => None
  end.

Lemma xshift_sound ρ β left xa ta xb tb x :
  xshift left xa ta xb tb = Some x ->
  (if left then sem_shl else sem_shr) (den ρ β xa) ta (den ρ β xb) tb = Some (den ρ β x).
Proof.
  unfold xshift. intros H.
  destruct xb; try discriminate;
  destruct ta as [| sza sga aa | sga aa | fa aa | ta' aa | ta' na aa | targsa tresa cca | ida aa | ida aa];
    try discriminate;
  destruct tb as [| szb sgb ab | sgb ab | fb ab | tb' ab | tb' nb ab | targsb tresb ccb | idb ab | idb ab];
    try discriminate.
  - destruct (isk KI xa) eqn:Ka; [|discriminate].
    destruct (Int.ltu i Int.iwordsize) eqn:L; [|discriminate].
    inversion H; subst x. rewrite (den_KI ρ β xa Ka).
    destruct left; unfold sem_shl, sem_shr, sem_shift;
      destruct sza, sga, szb, sgb; simpl; rewrite L, ?Int.repr_unsigned; reflexivity.
  - destruct (isk KL xa) eqn:Ka; [|discriminate].
    destruct (Int.ltu i Int64.iwordsize') eqn:L; [|discriminate].
    inversion H; subst x. rewrite (den_KL ρ β xa Ka).
    destruct left; unfold sem_shl, sem_shr, sem_shift;
      destruct sga, szb, sgb; simpl; rewrite L; reflexivity.
  - destruct (isk KI xa) eqn:Ka; [|discriminate].
    destruct (Int64.ltu l (Int64.repr 32)) eqn:L; [|discriminate].
    inversion H; subst x. rewrite (den_KI ρ β xa Ka).
    destruct left; unfold sem_shl, sem_shr, sem_shift;
      destruct sza, sga, sgb; simpl; rewrite L; reflexivity.
  - destruct (isk KL xa) eqn:Ka; [|discriminate].
    destruct (Int64.ltu l Int64.iwordsize) eqn:L; [|discriminate].
    inversion H; subst x. rewrite (den_KL ρ β xa Ka).
    destruct left; unfold sem_shl, sem_shr, sem_shift;
      destruct sga, sgb; simpl; rewrite L, ?Int64.repr_unsigned; reflexivity.
Qed.

(** ** Binary operators on arithmetic operands *)
Definition xbin (op : binary_operation) (xa : sx) (ta : type) (xb : sx) (tb : type) : option sx :=
  match op with
  | Oadd => xbinarith (fun _ => XIb Badd) (fun _ => XLb Badd) xa ta xb tb
  | Osub => xbinarith (fun _ => XIb Bsub) (fun _ => XLb Bsub) xa ta xb tb
  | Omul => xbinarith (fun _ => XIb Bmul) (fun _ => XLb Bmul) xa ta xb tb
  | Oand => xbinarith (fun _ => XIb Band) (fun _ => XLb Band) xa ta xb tb
  | Oor => xbinarith (fun _ => XIb Bor) (fun _ => XLb Bor) xa ta xb tb
  | Oxor => xbinarith (fun _ => XIb Bxor) (fun _ => XLb Bxor) xa ta xb tb
  | Oshl => xshift true xa ta xb tb
  | Oshr => xshift false xa ta xb tb
  | Oeq => xbinarith (XIcmp Ceq) (XLcmp Ceq) xa ta xb tb
  | One => xbinarith (XIcmp Cne) (XLcmp Cne) xa ta xb tb
  | Olt => xbinarith (XIcmp Clt) (XLcmp Clt) xa ta xb tb
  | Ogt => xbinarith (XIcmp Cgt) (XLcmp Cgt) xa ta xb tb
  | Ole => xbinarith (XIcmp Cle) (XLcmp Cle) xa ta xb tb
  | Oge => xbinarith (XIcmp Cge) (XLcmp Cge) xa ta xb tb
  | _ => None
  end.

Lemma of_bool_b2i b : Val.of_bool b = Vint (b2i b).
Proof. destruct b; reflexivity. Qed.

Ltac arith_shapes H :=
  let H1 := fresh in let H2 := fresh in
  pose proof (xbinarith_arith _ _ _ _ _ _ _ H) as H1;
  pose proof (xbinarith_arith_r _ _ _ _ _ _ _ H) as H2;
  destruct H1 as [(?sz & ?sg & ?a & ->)|(?sg & ?a & ->)];
  destruct H2 as [(?sz & ?sg & ?a & ->)|(?sg & ?a & ->)].

Lemma xbin_sound ce ρ β op xa ta xb tb x m :
  xbin op xa ta xb tb = Some x ->
  sem_binary_operation ce op (den ρ β xa) ta (den ρ β xb) tb m = Some (den ρ β x).
Proof.
  intros H. destruct op; simpl in H; try discriminate; unfold sem_binary_operation.
  - (* add *)
    assert (C : classify_add ta tb = add_default).
    { arith_shapes H; unfold classify_add; simpl;
        repeat match goal with s : intsize |- _ => destruct s end; reflexivity. }
    unfold sem_add. rewrite C.
    eapply xbinarith_sound; [| |exact H]; intros; reflexivity.
  - (* sub *)
    assert (C : classify_sub ta tb = sub_default).
    { arith_shapes H; unfold classify_sub; simpl;
        repeat match goal with s : intsize |- _ => destruct s end; reflexivity. }
    unfold sem_sub. rewrite C.
    eapply xbinarith_sound; [| |exact H]; intros; reflexivity.
  - unfold sem_mul. eapply xbinarith_sound; [| |exact H]; intros; reflexivity.
  - unfold sem_and. eapply xbinarith_sound; [| |exact H]; intros; reflexivity.
  - unfold sem_or. eapply xbinarith_sound; [| |exact H]; intros; reflexivity.
  - unfold sem_xor. eapply xbinarith_sound; [| |exact H]; intros; reflexivity.
  - exact (xshift_sound ρ β true xa ta xb tb x H).
  - exact (xshift_sound ρ β false xa ta xb tb x H).
  - assert (C : classify_cmp ta tb = cmp_default).
    { arith_shapes H; unfold classify_cmp; simpl;
        repeat match goal with s : intsize |- _ => destruct s end; reflexivity. }
    unfold sem_cmp. rewrite C.
    eapply xbinarith_sound; [| |exact H]; intros; simpl; rewrite of_bool_b2i; reflexivity.
  - assert (C : classify_cmp ta tb = cmp_default).
    { arith_shapes H; unfold classify_cmp; simpl;
        repeat match goal with s : intsize |- _ => destruct s end; reflexivity. }
    unfold sem_cmp. rewrite C.
    eapply xbinarith_sound; [| |exact H]; intros; simpl; rewrite of_bool_b2i; reflexivity.
  - assert (C : classify_cmp ta tb = cmp_default).
    { arith_shapes H; unfold classify_cmp; simpl;
        repeat match goal with s : intsize |- _ => destruct s end; reflexivity. }
    unfold sem_cmp. rewrite C.
    eapply xbinarith_sound; [| |exact H]; intros; simpl; rewrite of_bool_b2i; reflexivity.
  - assert (C : classify_cmp ta tb = cmp_default).
    { arith_shapes H; unfold classify_cmp; simpl;
        repeat match goal with s : intsize |- _ => destruct s end; reflexivity. }
    unfold sem_cmp. rewrite C.
    eapply xbinarith_sound; [| |exact H]; intros; simpl; rewrite of_bool_b2i; reflexivity.
  - assert (C : classify_cmp ta tb = cmp_default).
    { arith_shapes H; unfold classify_cmp; simpl;
        repeat match goal with s : intsize |- _ => destruct s end; reflexivity. }
    unfold sem_cmp. rewrite C.
    eapply xbinarith_sound; [| |exact H]; intros; simpl; rewrite of_bool_b2i; reflexivity.
  - assert (C : classify_cmp ta tb = cmp_default).
    { arith_shapes H; unfold classify_cmp; simpl;
        repeat match goal with s : intsize |- _ => destruct s end; reflexivity. }
    unfold sem_cmp. rewrite C.
    eapply xbinarith_sound; [| |exact H]; intros; simpl; rewrite of_bool_b2i; reflexivity.
Qed.

(** ** Unary operators *)
Definition xun (op : unary_operation) (xa : sx) (ta : type) : option sx :=
  match op, ta with
  | Onotbool, Tint _ _ _ => if isk KI xa then Some (XIz xa) else None
  | Onotbool, Tlong _ _ => if isk KL xa then Some (XLz xa) else None
  | Onotint, Tint _ _ _ => if isk KI xa then Some (XInot xa) else None
  | Onotint, Tlong _ _ => if isk KL xa then Some (XLnot xa) else None
  | Oneg, Tint _ _ _ => if isk KI xa then Some (XIneg xa) else None
  | Oneg, Tlong _ _ => if isk KL xa then Some (XLneg xa) else None
  | _, _ => None
  end.

Lemma xun_sound ρ β op xa ta x m :
  xun op xa ta = Some x -> sem_unary_operation op (den ρ β xa) ta m = Some (den ρ β x).
Proof.
  unfold xun. intros H.
  destruct op; try discriminate;
  destruct ta as [| sza sga aa | sga aa | fa aa | ta' aa | ta' na aa | targsa tresa cca | ida aa | ida aa];
    try discriminate.
  - destruct (isk KI xa) eqn:K; [|discriminate]. inversion H; subst x. rewrite (den_KI ρ β xa K).
    simpl. unfold sem_notbool, bool_val. destruct sza, sga; simpl;
      destruct (Int.eq (ii (den ρ β xa)) Int.zero); reflexivity.
  - destruct (isk KL xa) eqn:K; [|discriminate]. inversion H; subst x. rewrite (den_KL ρ β xa K).
    simpl. unfold sem_notbool, bool_val. simpl.
    destruct (Int64.eq (il (den ρ β xa)) Int64.zero); reflexivity.
  - destruct (isk KI xa) eqn:K; [|discriminate]. inversion H; subst x. rewrite (den_KI ρ β xa K).
    simpl. unfold sem_notint. destruct sza, sga; reflexivity.
  - destruct (isk KL xa) eqn:K; [|discriminate]. inversion H; subst x. rewrite (den_KL ρ β xa K).
    reflexivity.
  - destruct (isk KI xa) eqn:K; [|discriminate]. inversion H; subst x. rewrite (den_KI ρ β xa K).
    simpl. unfold sem_neg. destruct sza, sga; reflexivity.
  - destruct (isk KL xa) eqn:K; [|discriminate]. inversion H; subst x. rewrite (den_KL ρ β xa K).
    reflexivity.
Qed.

(** ** Truth value of a condition *)
Definition xbool (xa : sx) (ta : type) : option sx :=
  match ta with
  | Tint _ _ _ => if isk KI xa then Some xa else None
  | Tlong _ _ => if isk KL xa then Some (XLnz xa) else None
  | _ => None
  end.
Definition truth (ρ : nat -> int64) (β : nat -> block * Z) (c : sx) : bool := negb (Int.eq (ii (den ρ β c)) Int.zero).

Lemma xbool_sound ρ β xa ta c m :
  xbool xa ta = Some c -> bool_val (den ρ β xa) ta m = Some (truth ρ β c).
Proof.
  unfold xbool, truth. intros H.
  destruct ta as [| sza sga aa | sga aa | fa aa | ta' aa | ta' na aa | targsa tresa cca | ida aa | ida aa];
    try discriminate.
  - destruct (isk KI xa) eqn:K; [|discriminate]. inversion H; subst c. rewrite (den_KI ρ β xa K) at 1.
    unfold bool_val. destruct sza, sga; reflexivity.
  - destruct (isk KL xa) eqn:K; [|discriminate]. inversion H; subst c. rewrite (den_KL ρ β xa K).
    unfold bool_val. simpl. destruct (Int64.eq (il (den ρ β xa)) Int64.zero); reflexivity.
Qed.

(** ** Normalization of a value stored through a memory chunk *)
Definition xnorm (chunk : memory_chunk) (x : sx) : option sx :=
  match chunk with
  | Mint8unsigned => if isk KI x then Some (XIcast I8 Unsigned x) else None
  | Mint8signed => if isk KI x then Some (XIcast I8 Signed x) else None
  | Mint16unsigned => if isk KI x then Some (XIcast I16 Unsigned x) else None
  | Mint16signed => if isk KI x then Some (XIcast I16 Signed x) else None
  | Mint32 => if isk KI x then Some x else None
  | Mint64 => if isk KL x || isk KP x || isk KA x then Some x else None
  | _ => None
  end.

Lemma xnorm_sound ρ β chunk x x' :
  xnorm chunk x = Some x' -> Val.load_result chunk (den ρ β x) = den ρ β x'.
Proof.
  unfold xnorm. intros H. destruct chunk; try discriminate.
  - destruct (isk KI x) eqn:K; [|discriminate]. inversion H; subst x'. rewrite (den_KI ρ β x K); reflexivity.
  - destruct (isk KI x) eqn:K; [|discriminate]. inversion H; subst x'. rewrite (den_KI ρ β x K); reflexivity.
  - destruct (isk KI x) eqn:K; [|discriminate]. inversion H; subst x'. rewrite (den_KI ρ β x K); reflexivity.
  - destruct (isk KI x) eqn:K; [|discriminate]. inversion H; subst x'. rewrite (den_KI ρ β x K); reflexivity.
  - destruct (isk KI x) eqn:K; [|discriminate]. inversion H; subst x'. rewrite (den_KI ρ β x K) at 1; simpl; symmetry; exact (den_KI ρ β x K).
  - destruct (isk KL x) eqn:K.
    + inversion H; subst x'. rewrite (den_KL ρ β x K) at 1; simpl; symmetry; exact (den_KL ρ β x K).
    + destruct (isk KP x) eqn:K2; simpl in H.
      * inversion H; subst x'. destruct (den_KP x K2) as (r & d & ->). reflexivity.
      * destruct (isk KA x) eqn:K3; [|discriminate]. inversion H; subst x'.
        destruct (den_KA x K3) as (b & o & ->). reflexivity.
Qed.
