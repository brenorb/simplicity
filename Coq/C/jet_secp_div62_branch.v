(** Original eta branch, including the negative-eta swaps. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix C.jet_secp_div62_count C.jet_secp_div62_cancel C.jet_secp_div62_limit.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition div62_swap_prefix := statement_sequence (firstn 10 (fst (div62_eta_parts true))) Sskip.
Definition div62_swap_temps le eta f g u v q r :=
  PTree.set _r (Vlong (Int64.neg v)) (PTree.set _v (Vlong r) (PTree.set _tmp (Vlong v)
  (PTree.set _q (Vlong (Int64.neg u)) (PTree.set _u (Vlong q) (PTree.set _tmp (Vlong u)
  (PTree.set _g (Vlong (Int64.neg f)) (PTree.set _f (Vlong g) (PTree.set _tmp (Vlong f)
  (PTree.set _eta (Vlong (Int64.neg eta)) le))))))))).

Lemma div62_swap_source : div62_swap_prefix =
  Ssequence (Sset _eta (Eunop Oneg (Etempvar _eta tlong) tlong))
  (Ssequence (Sset _tmp (Etempvar _f tulong))
  (Ssequence (Sset _f (Etempvar _g tulong))
  (Ssequence (Sset _g (Eunop Oneg (Etempvar _tmp tulong) tulong))
  (Ssequence (Sset _tmp (Etempvar _u tulong))
  (Ssequence (Sset _u (Etempvar _q tulong))
  (Ssequence (Sset _q (Eunop Oneg (Etempvar _tmp tulong) tulong))
  (Ssequence (Sset _tmp (Etempvar _v tulong))
  (Ssequence (Sset _v (Etempvar _r tulong))
  (Ssequence (Sset _r (Eunop Oneg (Etempvar _tmp tulong) tulong)) Sskip))))))))).
Proof. reflexivity. Qed.

Local Ltac branch_lookup := first [eassumption|apply PTree.gss|rewrite PTree.gso by discriminate;branch_lookup].
Local Ltac branch_expr := first [apply eval_Etempvar;branch_lookup|apply eval_Econst_int|apply eval_Econst_long|
  eapply eval_Ecast;[branch_expr|reflexivity]|
  eapply eval_Eunop;[branch_expr|reflexivity]|
  eapply eval_Ebinop;[branch_expr|branch_expr|reflexivity]].

Theorem exec_div62_swap e le m eta f g u v q r :
  le!_eta=Some(Vlong eta) -> le!_f=Some(Vlong f) -> le!_g=Some(Vlong g) ->
  le!_u=Some(Vlong u) -> le!_v=Some(Vlong v) -> le!_q=Some(Vlong q) -> le!_r=Some(Vlong r) ->
  Clight2.exec_stmt secp_ge e le m div62_swap_prefix E0
    (div62_swap_temps le eta f g u v q r) m Out_normal.
Proof.
  intros Eta F G U V Q R;rewrite div62_swap_source;unfold div62_swap_temps.
  repeat (eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m);[apply exec_Sset;branch_expr|]).
  constructor.
Qed.

Lemma div62_swap_temps_outside le eta f g u v q r id :
  ~In id [_eta;_tmp;_f;_g;_u;_v;_q;_r] ->
  (div62_swap_temps le eta f g u v q r)!id=le!id.
Proof.
  intro Outside;unfold div62_swap_temps;rewrite !PTree.gso;[reflexivity| | | | | | | | | |];
    intro Eq;subst id;apply Outside;cbn [In];tauto.
Qed.

Definition div62_branch_entry le (neg : bool) eta f g u v q r :=
  if neg then div62_swap_temps le (Int64.repr eta) f g u v q r else le.
Definition div62_branch_temps le neg eta i f g u v q r :=
  div62_prepared_temps (div62_branch_entry le neg eta f g u v q r) neg
    (if neg then -eta else eta) i (if neg then g else f) (if neg then Int64.neg f else g).

Lemma div62_eta_body_source neg : div62_eta_body neg =
  statement_sequence (firstn (if neg then 10 else 0) (fst (div62_eta_parts neg))) (div62_after_swap neg).
Proof. destruct neg;reflexivity. Qed.

Theorem exec_div62_eta_body e le m (neg : bool) eta i f g u v q r :
  (if neg then -745<=eta<0 else 0<=eta<=745) -> 1<=i<=62 ->
  le!_eta=Some(Vlong(Int64.repr eta)) -> le!_i=Some(Vint(Int.repr i)) ->
  le!_f=Some(Vlong f) -> le!_g=Some(Vlong g) -> le!_u=Some(Vlong u) -> le!_v=Some(Vlong v) ->
  le!_q=Some(Vlong q) -> le!_r=Some(Vlong r) ->
  Clight2.exec_stmt secp_ge e le m (div62_eta_body neg) E0
    (div62_branch_temps le neg eta i f g u v q r) m Out_normal.
Proof.
  intros Bound I Eta Index F G U V Q R;rewrite div62_eta_body_source;destruct neg.
  - unfold div62_branch_temps,div62_branch_entry.
    eapply exec_statement_prefix_then_last with
      (le1:=div62_swap_temps le (Int64.repr eta) f g u v q r) (m1:=m).
    + now apply exec_div62_swap.
    + apply exec_div62_after_swap;try lia.
      * unfold div62_swap_temps;repeat rewrite PTree.gso by discriminate.
        rewrite PTree.gss,Int64.neg_repr;reflexivity.
      * rewrite div62_swap_temps_outside;[exact Index|cbn [In];intuition discriminate].
      * unfold div62_swap_temps;branch_lookup.
      * unfold div62_swap_temps;branch_lookup.
  - change (Clight2.exec_stmt secp_ge e le m (div62_after_swap false) E0
      (div62_prepared_temps le false eta i f g) m Out_normal).
    now apply exec_div62_after_swap.
Qed.

Lemma div62_eta_branch_source : div62_eta_branch =
  Sifthenelse (Ebinop Olt (Etempvar _eta tlong) (Econst_int Int.zero tint) tint)
    (div62_eta_body true) (div62_eta_body false).
Proof. reflexivity. Qed.

Theorem exec_div62_eta_branch e le m eta i f g u v q r :
  -745<=eta<=745 -> 1<=i<=62 ->
  le!_eta=Some(Vlong(Int64.repr eta)) -> le!_i=Some(Vint(Int.repr i)) ->
  le!_f=Some(Vlong f) -> le!_g=Some(Vlong g) -> le!_u=Some(Vlong u) -> le!_v=Some(Vlong v) ->
  le!_q=Some(Vlong q) -> le!_r=Some(Vlong r) ->
  Clight2.exec_stmt secp_ge e le m div62_eta_branch E0
    (div62_branch_temps le (if zlt eta 0 then true else false) eta i f g u v q r) m Out_normal.
Proof.
  intros Bound I Eta Index F G U V Q R;rewrite div62_eta_branch_source.
  assert (Test : eval_expr secp_ge e le m
    (Ebinop Olt (Etempvar _eta tlong) (Econst_int Int.zero tint) tint)
    (Vint(if zlt eta 0 then Int.one else Int.zero))).
  { eapply eval_Ebinop;[apply eval_Etempvar;exact Eta|apply eval_Econst_int|].
    change (Some(Val.of_bool(Int64.lt (Int64.repr eta) Int64.zero))=
      Some(Vint(if zlt eta 0 then Int.one else Int.zero))).
    unfold Int64.lt;change (Int64.signed Int64.zero) with 0.
    rewrite Int64.signed_repr by (change (-9223372036854775808<=eta<=9223372036854775807);lia).
    destruct (zlt eta 0);reflexivity. }
  destruct (zlt eta 0) as [LT|GE];
    eapply exec_Sifthenelse;[exact Test|reflexivity| |exact Test|reflexivity|];
    apply exec_div62_eta_body;assumption || lia.
Qed.

Definition div62_continued_temps le (neg : bool) eta i f g u v q r :=
  div62_cancel_temps
    (div62_limit_temps (div62_branch_entry le neg eta f g u v q r) neg (if neg then -eta else eta) i)
    neg (if neg then g else f) (if neg then Int64.neg f else g)
    (if neg then q else u) (if neg then r else v)
    (if neg then Int64.neg u else q) (if neg then Int64.neg v else r)
    (div62_mask neg (if neg then -eta else eta) i).

Theorem exec_div62_branch_updates e le m eta i f g u v q r :
  -745<=eta<=745 -> 1<=i<=62 ->
  le!_eta=Some(Vlong(Int64.repr eta)) -> le!_i=Some(Vint(Int.repr i)) ->
  le!_f=Some(Vlong f) -> le!_g=Some(Vlong g) -> le!_u=Some(Vlong u) -> le!_v=Some(Vlong v) ->
  le!_q=Some(Vlong q) -> le!_r=Some(Vlong r) ->
  Clight2.exec_stmt secp_ge e le m (Ssequence div62_eta_branch div62_cancel_updates) E0
    (div62_continued_temps le (if zlt eta 0 then true else false) eta i f g u v q r) m Out_normal.
Proof.
  intros Bound I Eta Index F G U V Q R.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=div62_branch_temps le (if zlt eta 0 then true else false) eta i f g u v q r).
  - now apply exec_div62_eta_branch.
  - unfold div62_continued_temps,div62_cancel_temps,div62_w_long;destruct (zlt eta 0);
      apply exec_div62_updates;
      unfold div62_branch_temps,div62_prepared_temps,div62_limit_temps,div62_branch_entry,
        div62_swap_temps,div62_limit_temp;branch_lookup.
Qed.

Definition div62_guard_prefix := statement_sequence (firstn 5 (fst div62_cont_parts)) Sskip.
Lemma div62_nonexit_source : div62_after_count_prefix =
  statement_sequence (firstn 5 (fst div62_cont_parts))
    (Ssequence div62_eta_branch div62_cancel_updates).
Proof. reflexivity. Qed.
Lemma div62_guard_source : div62_guard_prefix =
  Ssequence (Sloop Sskip Sbreak) (Ssequence (Sloop Sskip Sbreak)
  (Ssequence (Sloop Sskip Sbreak) (Ssequence (Sloop Sskip Sbreak)
  (Ssequence (Sloop (Sifthenelse (Ebinop Oge (Etempvar _eta tlong)
    (Eunop Oneg (Econst_int (Int.repr 745) tint) tint) tint) Sskip Sskip) Sbreak) Sskip)))).
Proof. reflexivity. Qed.

Lemma exec_div62_guard e le m eta : le!_eta=Some(Vlong eta) ->
  Clight2.exec_stmt secp_ge e le m div62_guard_prefix E0 le m Out_normal.
Proof.
  intro Eta;rewrite div62_guard_source.
  do 4 (eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le);[apply exec_div62_noop|]).
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le);[|constructor].
  eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le)
    (out1:=Out_normal) (out2:=Out_break);[|constructor|constructor|constructor].
  eapply exec_Sifthenelse with (v1:=Val.of_bool(Int64.cmp Cge eta (Int64.repr (-745))))
    (b:=Int64.cmp Cge eta (Int64.repr (-745))).
  - branch_expr.
  - destruct (Int64.cmp Cge eta (Int64.repr (-745)));reflexivity.
  - destruct (Int64.cmp Cge eta (Int64.repr (-745)));constructor.
Qed.

Theorem exec_div62_nonexit e le m eta i f g u v q r :
  -745<=eta<=745 -> 1<=i<=62 ->
  le!_eta=Some(Vlong(Int64.repr eta)) -> le!_i=Some(Vint(Int.repr i)) ->
  le!_f=Some(Vlong f) -> le!_g=Some(Vlong g) -> le!_u=Some(Vlong u) -> le!_v=Some(Vlong v) ->
  le!_q=Some(Vlong q) -> le!_r=Some(Vlong r) ->
  Clight2.exec_stmt secp_ge e le m div62_after_count_prefix E0
    (div62_continued_temps le (if zlt eta 0 then true else false) eta i f g u v q r) m Out_normal.
Proof.
  intros Bound I Eta Index F G U V Q R;rewrite div62_nonexit_source.
  eapply exec_statement_prefix_then_last with (le1:=le) (m1:=m).
  - now apply exec_div62_guard with (eta:=Int64.repr eta).
  - now apply exec_div62_branch_updates.
Qed.

Lemma div62_continued_temps_outside le neg eta i f g u v q r id :
  ~In id [_eta;_tmp;_f;_g;_u;_v;_q;_r;_m;_limit;_w;_t'2;_t'3] ->
  (div62_continued_temps le neg eta i f g u v q r)!id=le!id.
Proof.
  intro Outside;unfold div62_continued_temps,div62_cancel_temps,div62_limit_temps,
    div62_branch_entry,div62_swap_temps,div62_limit_temp;destruct neg;
    rewrite !PTree.gso;try reflexivity;
    intro Eq;subst id;apply Outside;cbn [In];tauto.
Qed.

Theorem exec_div62_count_nonexit e le m eta i z f g u v q r :
  0<=z<i -> i<=62 -> -745<=eta-z<=745 ->
  le!_eta=Some(Vlong(Int64.repr eta)) -> le!_i=Some(Vint(Int.repr i)) ->
  le!_zeros=Some(Vint(Int.repr z)) ->
  le!_f=Some(Vlong f) -> le!_g=Some(Vlong g) -> le!_u=Some(Vlong u) -> le!_v=Some(Vlong v) ->
  le!_q=Some(Vlong q) -> le!_r=Some(Vlong r) ->
  Clight2.exec_stmt secp_ge e le m div62_after_count E0
    (div62_continued_temps (div62_count_temps le g u v eta i z)
      (if zlt (eta-z) 0 then true else false) (eta-z) (i-z)
      f (Int64.shru g (Int64.repr z)) (Int64.shl u (Int64.repr z)) (Int64.shl v (Int64.repr z)) q r)
    m Out_normal.
Proof.
  intros Range I Bound Eta Index Zeros F G U V Q R.
  pose proof (exec_div62_count_prefix e le m g u v eta i z ltac:(lia) I G U V Eta Index Zeros) as Count.
  unfold div62_count_outcome in Count;destruct (Z.eqb_spec i z) as [Eq|NE];[lia|].
  rewrite div62_count_source;eapply exec_statement_prefix_then_last with
    (le1:=div62_count_temps le g u v eta i z) (m1:=m);[exact Count|].
  apply exec_div62_nonexit;[exact Bound|lia| | | | | | | | ];
    unfold div62_count_temps;branch_lookup.
Qed.


