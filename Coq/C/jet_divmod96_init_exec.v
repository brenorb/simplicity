(** Execute the actual helper initialization, retaining its LP64 casts and
    multiply-by-one expressions. The whole helper derives the store/tail premises. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_readBit_layout C.jet_divmod96_init.
Require Import C.jet_divmod96_value C.jet_divmod96_expr C.jet_divmod96_step.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divmod96_clamp_stmt :=
  Sifthenelse (Ebinop Ole (Etempvar _estQ tulong) (Econst_int Int.mone tuint) tint)
    (Sset _t'1 (Ecast (Ecast (Etempvar _estQ tulong) tulong) tulong))
    (Sset _t'1 (Ecast (Econst_int Int.mone tuint) tulong)).
Definition divmod96_scaled_expr idq idpart :=
  Ebinop Omul
    (Ebinop Omul (Econst_int Int.one tuint) (Etempvar idq tulong) tulong)
    (Etempvar idpart tulong) tulong.
Definition divmod96_work suffix :=
  Ssequence (Sset _bh (Ebinop Oshr (Etempvar _b tulong) (Econst_int (Int.repr 32) tint) tulong))
    (Ssequence (Sset _bl (Ebinop Oand (Etempvar _b tulong) (Econst_int Int.mone tuint) tulong))
      (Ssequence (Sset _estQ (Ebinop Odiv (Etempvar _ah tulong) (Etempvar _bh tulong) tulong))
        (Ssequence
          (Ssequence divmod96_clamp_stmt
            (Sassign (Ederef (Etempvar _q (tptr tulong)) tulong) (Etempvar _t'1 tulong)))
          (Ssequence
            (Ssequence (Sset _t'5 (Ederef (Etempvar _q (tptr tulong)) tulong))
              (Sset _rh (Ebinop Osub (Etempvar _ah tulong) (divmod96_scaled_expr _t'5 _bh) tulong)))
            (Ssequence
              (Ssequence (Sset _t'4 (Ederef (Etempvar _q (tptr tulong)) tulong))
                (Sset _d (divmod96_scaled_expr _t'4 _bl)))
              suffix))))).

Definition divmod96_initial_rh ah b :=
  let q := divmod96_clamp ah (divmod96_high b) in
  Int64.sub ah (Int64.mul (Int64.mul Int64.one q) (divmod96_high b)).
Definition divmod96_initial_d ah b :=
  let q := divmod96_clamp ah (divmod96_high b) in
  Int64.mul (Int64.mul Int64.one q) (divmod96_low b).
Definition divmod96_init_env le ah b :=
  let bh := divmod96_high b in let bl := divmod96_low b in
  let q := divmod96_clamp ah bh in
  PTree.set _d (Vlong (divmod96_initial_d ah b))
    (PTree.set _t'4 (Vlong q)
      (PTree.set _rh (Vlong (divmod96_initial_rh ah b))
        (PTree.set _t'5 (Vlong q)
          (PTree.set _t'1 (Vlong q)
            (PTree.set _estQ (Vlong (Int64.divu ah bh))
              (PTree.set _bl (Vlong bl) (PTree.set _bh (Vlong bh) le))))))).

Lemma eval_divmod96_estimate_expr e le m ah bh :
  le!_ah = Some (Vlong ah) -> le!_bh = Some (Vlong bh) -> Int64.eq bh Int64.zero = Datatypes.false ->
  eval_expr ge0 e le m (Ebinop Odiv (Etempvar _ah tulong) (Etempvar _bh tulong) tulong)
    (Vlong (Int64.divu ah bh)).
Proof.
  intros HA HB HNZ. eapply eval_Ebinop with (v1 := Vlong ah) (v2 := Vlong bh).
  - apply eval_Etempvar; exact HA.
  - apply eval_Etempvar; exact HB.
  - change ((if Int64.eq bh Int64.zero then None else Some (Vlong (Int64.divu ah bh))) =
      Some (Vlong (Int64.divu ah bh))). rewrite HNZ. reflexivity.
Qed.

Lemma exec_divmod96_clamp_stmt e le m ah bh :
  le!_estQ = Some (Vlong (Int64.divu ah bh)) ->
  Clight2.exec_stmt ge0 e le m divmod96_clamp_stmt E0
    (PTree.set _t'1 (Vlong (divmod96_clamp ah bh)) le) m Out_normal.
Proof.
  intros HE. set (est := Int64.divu ah bh).
  assert (HC : eval_expr ge0 e le m
    (Ebinop Ole (Etempvar _estQ tulong) (Econst_int Int.mone tuint) tint)
    (Vint (bit_int (negb (Int64.ltu (Int64.repr (divmod96_radix - 1)) est))))).
  { eapply eval_Ebinop with (v1 := Vlong est) (v2 := Vint Int.mone).
    - apply eval_Etempvar; exact HE.
    - apply eval_Econst_int.
    - change (Some (Val.of_bool (negb (Int64.ltu (Int64.repr (divmod96_radix - 1)) est))) =
        Some (Vint (bit_int (negb (Int64.ltu (Int64.repr (divmod96_radix - 1)) est))))).
      destruct (Int64.ltu (Int64.repr (divmod96_radix - 1)) est); reflexivity. }
  unfold divmod96_clamp. fold est.
  destruct (Int64.ltu (Int64.repr (divmod96_radix - 1)) est); cbn [negb].
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + exact HC.
    + reflexivity.
    + apply exec_set. eapply eval_Ecast with (v1 := Vint Int.mone); [apply eval_Econst_int|reflexivity].
  - eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
    + exact HC.
    + reflexivity.
    + apply exec_set. eapply eval_Ecast with (v1 := Vlong est); [|reflexivity].
      eapply eval_Ecast with (v1 := Vlong est); [apply eval_Etempvar; exact HE|reflexivity].
Qed.

Lemma eval_divmod96_scaled_expr idq idpart e le m q part :
  le!idq = Some (Vlong q) -> le!idpart = Some (Vlong part) ->
  eval_expr ge0 e le m (divmod96_scaled_expr idq idpart)
    (Vlong (Int64.mul (Int64.mul Int64.one q) part)).
Proof.
  intros HQ HP. eapply eval_Ebinop with (v1 := Vlong (Int64.mul Int64.one q)) (v2 := Vlong part).
  - eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vlong q).
    + apply eval_Econst_int.
    + apply eval_Etempvar; exact HQ.
    + reflexivity.
  - apply eval_Etempvar; exact HP.
  - reflexivity.
Qed.

Ltac divmod96_init_lookup :=
  repeat first [rewrite PTree.gss | rewrite PTree.gso by discriminate]; first [reflexivity | assumption].

Lemma exec_divmod96_initialization e le m mi mf lef suffix out bq ofs ah b :
  le!_q = Some (Vptr bq ofs) -> le!_ah = Some (Vlong ah) -> le!_b = Some (Vlong b) ->
  Int64.eq (divmod96_high b) Int64.zero = Datatypes.false ->
  Mem.store Mint64 m bq (Ptrofs.unsigned ofs) (Vlong (divmod96_clamp ah (divmod96_high b))) = Some mi ->
  Clight2.exec_stmt ge0 e (divmod96_init_env le ah b) mi suffix E0 lef mf out ->
  Clight2.exec_stmt ge0 e le m (divmod96_work suffix) E0 lef mf out.
Proof.
  intros HQ HA HB HNZ HS Htail.
  set (bh := divmod96_high b). set (bl := divmod96_low b).
  set (est := Int64.divu ah bh). set (q := divmod96_clamp ah bh).
  set (lebh := PTree.set _bh (Vlong bh) le).
  set (lebl := PTree.set _bl (Vlong bl) lebh).
  set (leest := PTree.set _estQ (Vlong est) lebl).
  set (leq := PTree.set _t'1 (Vlong q) leest).
  set (lerh := PTree.set _rh (Vlong (divmod96_initial_rh ah b)) (PTree.set _t'5 (Vlong q) leq)).
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := lebh) (m1 := m).
  - apply exec_set. apply eval_divmod96_high_expr; exact HB.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := lebl) (m1 := m).
    + apply exec_set. apply eval_divmod96_low_expr. unfold lebh. divmod96_init_lookup.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leest) (m1 := m).
      * apply exec_set. apply eval_divmod96_estimate_expr.
        -- unfold lebl, lebh. divmod96_init_lookup.
        -- unfold lebl, lebh. divmod96_init_lookup.
        -- exact HNZ.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leq) (m1 := mi).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := leq) (m1 := m).
           ++ apply exec_divmod96_clamp_stmt. unfold leest. divmod96_init_lookup.
           ++ eapply exec_Sassign with (loc := bq) (ofs := ofs) (bf := Full) (v2 := Vlong q) (v := Vlong q).
              ** apply eval_Ederef. apply eval_Etempvar. unfold leq, leest, lebl, lebh. divmod96_init_lookup.
              ** apply eval_Etempvar. unfold leq. divmod96_init_lookup.
              ** reflexivity.
              ** apply assign_loc_value with (chunk := Mint64); [reflexivity|exact HS].
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := lerh) (m1 := mi).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'5 (Vlong q) leq) (m1 := mi).
              ** apply exec_set. eapply eval_divmod96_quotient with (bq := bq) (ofs := ofs).
                 --- unfold leq, leest, lebl, lebh. divmod96_init_lookup.
                 --- rewrite (Mem.load_store_same Mint64 m bq (Ptrofs.unsigned ofs) (Vlong q) mi HS). reflexivity.
              ** apply exec_set. eapply eval_Ebinop with (v1 := Vlong ah)
                   (v2 := Vlong (Int64.mul (Int64.mul Int64.one q) bh)).
                 --- apply eval_Etempvar. unfold leq, leest, lebl, lebh. divmod96_init_lookup.
                 --- apply eval_divmod96_scaled_expr.
                     +++ divmod96_init_lookup.
                     +++ unfold leq, leest, lebl, lebh. divmod96_init_lookup.
                 --- reflexivity.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := divmod96_init_env le ah b) (m1 := mi).
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'4 (Vlong q) lerh) (m1 := mi).
                 --- apply exec_set. eapply eval_divmod96_quotient with (bq := bq) (ofs := ofs).
                     +++ unfold lerh, leq, leest, lebl, lebh. divmod96_init_lookup.
                     +++ rewrite (Mem.load_store_same Mint64 m bq (Ptrofs.unsigned ofs) (Vlong q) mi HS). reflexivity.
                 --- apply exec_set. apply eval_divmod96_scaled_expr.
                     +++ divmod96_init_lookup.
                     +++ unfold lerh, leq, leest, lebl, lebh. divmod96_init_lookup.
              ** exact Htail.
Qed.
