(** Actual limit/mask calculation in each variable divstep branch. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix C.jet_secp_div62_cancel.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition div62_limit_temp (neg : bool) := if neg then _t'2 else _t'3.
Definition div62_limit_parts (neg : bool) := skipn (if neg then 10 else 0) (fst (div62_eta_parts neg)).
Definition div62_limit_prefix neg := statement_sequence (firstn 3 (div62_limit_parts neg)) Sskip.
Definition div62_limit eta i := Z.min i (eta+1).
Definition div62_mask (neg : bool) eta i := Int64.and
  (Int64.shru Int64.mone (Int64.repr (64-div62_limit eta i)))
  (Int64.repr (if neg then 63 else 15)).
Definition div62_limit_temps le neg eta i :=
  PTree.set _m (Vlong (div62_mask neg eta i))
    (PTree.set _limit (Vint (Int.repr (div62_limit eta i)))
      (PTree.set (div62_limit_temp neg) (Vint (Int.repr (div62_limit eta i))) le)).
Definition div62_eta_plus := Ebinop Oadd (Ecast (Etempvar _eta tlong) tint)
  (Econst_int Int.one tint) tint.

Lemma div62_limit_source neg : div62_limit_prefix neg =
  Ssequence
    (Ssequence (Sifthenelse (Ebinop Ogt div62_eta_plus (Etempvar _i tint) tint)
      (Sset (div62_limit_temp neg) (Ecast (Etempvar _i tint) tint))
      (Sset (div62_limit_temp neg) (Ecast div62_eta_plus tint)))
      (Sset _limit (Etempvar (div62_limit_temp neg) tint)))
    (Ssequence (Sloop (Sifthenelse (Ebinop Ogt (Etempvar _limit tint)
      (Econst_int Int.zero tint) tint) Sskip Sskip) Sbreak)
      (Ssequence (Sset _m (Ebinop Oand
        (Ebinop Oshr (Econst_long Int64.mone tulong)
          (Ebinop Osub (Econst_int (Int.repr 64) tint) (Etempvar _limit tint) tint) tulong)
        (Econst_int (Int.repr (if neg then 63 else 15)) tuint) tulong)) Sskip)).
Proof. destruct neg;reflexivity. Qed.

Lemma div62_limit_bounds eta i : 0<=eta<=745 -> 1<=i<=62 -> 1<=div62_limit eta i<=62.
Proof. unfold div62_limit;intros;lia. Qed.

Lemma eval_div62_eta_plus e le m eta : 0<=eta<=745 -> le!_eta=Some(Vlong (Int64.repr eta)) ->
  eval_expr secp_ge e le m div62_eta_plus (Vint (Int.repr (eta+1))).
Proof.
  intros Bound Eta;unfold div62_eta_plus;eapply eval_Ebinop with
    (v1:=Vint (Int.repr eta)) (v2:=Vint Int.one).
  - eapply eval_Ecast;[apply eval_Etempvar;exact Eta|].
    change (Some(Vint (Int64.loword (Int64.repr eta)))=Some(Vint (Int.repr eta))).
    unfold Int64.loword;rewrite Int64.unsigned_repr by
      (change (0<=eta<=18446744073709551615);lia);reflexivity.
  - apply eval_Econst_int.
  - change (Some(Vint(Int.add (Int.repr eta) Int.one))=Some(Vint(Int.repr(eta+1)))).
    change Int.one with (Int.repr 1);rewrite Int.add_signed,Int.signed_repr by
      (change (-2147483648<=eta<=2147483647);lia);reflexivity.
Qed.

Lemma eval_div62_limit_test e le m eta i : 0<=eta<=745 -> 1<=i<=62 ->
  le!_eta=Some(Vlong(Int64.repr eta)) -> le!_i=Some(Vint(Int.repr i)) ->
  eval_expr secp_ge e le m (Ebinop Ogt div62_eta_plus (Etempvar _i tint) tint)
    (Vint(if zlt i (eta+1) then Int.one else Int.zero)).
Proof.
  intros B I Eta Index;eapply eval_Ebinop.
  - now apply eval_div62_eta_plus.
  - apply eval_Etempvar;exact Index.
  - change (Some (Val.of_bool (Int.lt (Int.repr i) (Int.repr (eta+1))))=
      Some(Vint(if zlt i (eta+1) then Int.one else Int.zero))).
    unfold Int.lt;rewrite !Int.signed_repr by
      (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
    destruct (zlt i (eta+1));reflexivity.
Qed.

Lemma eval_div62_mask e le m (neg : bool) eta i : 0<=eta<=745 -> 1<=i<=62 ->
  le!_limit=Some(Vint(Int.repr(div62_limit eta i))) ->
  eval_expr secp_ge e le m
    (Ebinop Oand (Ebinop Oshr (Econst_long Int64.mone tulong)
      (Ebinop Osub (Econst_int (Int.repr 64) tint) (Etempvar _limit tint) tint) tulong)
      (Econst_int (Int.repr (if neg then 63 else 15)) tuint) tulong)
    (Vlong (div62_mask neg eta i)).
Proof.
  intros B I Limit;pose proof (div62_limit_bounds eta i B I) as L.
  eapply eval_Ebinop with
    (v1:=Vlong(Int64.shru Int64.mone (Int64.repr(64-div62_limit eta i)))).
  - eapply eval_Ebinop with (v2:=Vint(Int.repr(64-div62_limit eta i))).
    + apply eval_Econst_long.
    + eapply eval_Ebinop;[apply eval_Econst_int|apply eval_Etempvar;exact Limit|].
      change (Some(Vint(Int.sub (Int.repr 64) (Int.repr(div62_limit eta i))))=
        Some(Vint(Int.repr(64-div62_limit eta i)))).
      rewrite Int.sub_signed,!Int.signed_repr by
        (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia);reflexivity.
    + change ((if Int.ltu (Int.repr (64-div62_limit eta i)) Int64.iwordsize' then
        Some (Vlong (Int64.shru Int64.mone (Int64.repr (Int.unsigned (Int.repr (64-div62_limit eta i))))))
        else None)=Some(Vlong(Int64.shru Int64.mone (Int64.repr(64-div62_limit eta i))))).
      unfold Int.ltu;rewrite Int.unsigned_repr by
        (change (0<=64-div62_limit eta i<=4294967295);lia).
      change (Int.unsigned Int64.iwordsize') with 64.
      destruct (zlt (64-div62_limit eta i) 64);[reflexivity|lia].
  - apply eval_Econst_int.
  - unfold div62_mask;destruct neg;reflexivity.
Qed.

Theorem exec_div62_limit e le m neg eta i : 0<=eta<=745 -> 1<=i<=62 ->
  le!_eta=Some(Vlong(Int64.repr eta)) -> le!_i=Some(Vint(Int.repr i)) ->
  Clight2.exec_stmt secp_ge e le m (div62_limit_prefix neg) E0
    (div62_limit_temps le neg eta i) m Out_normal.
Proof.
  intros B I Eta Index;rewrite div62_limit_source.
  set (lim:=div62_limit eta i).
  set (le1:=PTree.set (div62_limit_temp neg) (Vint(Int.repr lim)) le).
  set (le2:=PTree.set _limit (Vint(Int.repr lim)) le1).
  pose proof (eval_div62_limit_test e le m eta i B I Eta Index) as Test.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le2).
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le1).
    + unfold le1,lim;destruct (zlt i (eta+1)) as [LT|GE].
      * unfold div62_limit;rewrite Z.min_l by lia.
        eapply exec_Sifthenelse;[exact Test|reflexivity|].
        apply exec_Sset;eapply eval_Ecast;[apply eval_Etempvar;exact Index|reflexivity].
      * unfold div62_limit;rewrite Z.min_r by lia.
        eapply exec_Sifthenelse;[exact Test|reflexivity|].
        apply exec_Sset;eapply eval_Ecast;[now apply eval_div62_eta_plus|reflexivity].
    + unfold le2;apply exec_Sset;apply eval_Etempvar;unfold le1;apply PTree.gss.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le2).
    + eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le2)
        (out1:=Out_normal) (out2:=Out_break);[|constructor|constructor|constructor].
      eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|constructor].
      eapply eval_Ebinop;[apply eval_Etempvar;unfold le2;apply PTree.gss|apply eval_Econst_int|].
      change (Some(Val.of_bool(Int.lt Int.zero (Int.repr lim)))=Some(Vint Int.one)).
      unfold Int.lt;change (Int.signed Int.zero) with 0;rewrite Int.signed_repr by
        (pose proof (div62_limit_bounds eta i B I);unfold lim;change (-2147483648<=div62_limit eta i<=2147483647);lia).
      destruct (zlt 0 lim);[reflexivity|pose proof (div62_limit_bounds eta i B I);unfold lim in *;lia].
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m).
      * apply exec_Sset;apply eval_div62_mask;[exact B|exact I|unfold le2,lim;apply PTree.gss].
      * constructor.
Qed.

Lemma div62_limit_temps_outside le neg eta i id :
  ~In id [_m;_limit;div62_limit_temp neg] -> (div62_limit_temps le neg eta i)!id=le!id.
Proof.
  intro Outside;unfold div62_limit_temps;rewrite !PTree.gso;[reflexivity| | |];
    intro Eq;subst id;apply Outside;cbn [In];tauto.
Qed.

Definition div62_after_swap neg := statement_sequence (div62_limit_parts neg) (snd (div62_eta_parts neg)).
Definition div62_prepared_temps le neg eta i f g :=
  PTree.set _w (Vint (div62_w_word neg f g (div62_mask neg eta i)))
    (div62_limit_temps le neg eta i).

Lemma div62_after_swap_source neg : div62_after_swap neg =
  statement_sequence (firstn 3 (div62_limit_parts neg)) (div62_w_statement neg).
Proof. destruct neg;reflexivity. Qed.

Theorem exec_div62_after_swap e le m neg eta i f g :
  0<=eta<=745 -> 1<=i<=62 ->
  le!_eta=Some(Vlong(Int64.repr eta)) -> le!_i=Some(Vint(Int.repr i)) ->
  le!_f=Some(Vlong f) -> le!_g=Some(Vlong g) ->
  Clight2.exec_stmt secp_ge e le m (div62_after_swap neg) E0
    (div62_prepared_temps le neg eta i f g) m Out_normal.
Proof.
  intros B I Eta Index F G;rewrite div62_after_swap_source.
  unfold div62_prepared_temps;eapply exec_statement_prefix_then_last with
    (le1:=div62_limit_temps le neg eta i) (m1:=m).
  - now apply exec_div62_limit.
  - apply exec_div62_w.
    + rewrite div62_limit_temps_outside;[exact F|destruct neg;cbn [div62_limit_temp In];intuition discriminate].
    + rewrite div62_limit_temps_outside;[exact G|destruct neg;cbn [div62_limit_temp In];intuition discriminate].
    + unfold div62_limit_temps;apply PTree.gss.
Qed.
