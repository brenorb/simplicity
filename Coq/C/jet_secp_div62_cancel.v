(** Original CTZ-free cancellation arithmetic. The four-bit path retains
    the actual uint32_t truncation before negation and widening. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix C.jet_secp_div62_count.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition div62_cont_parts := split_statement_last div62_after_count_prefix.
Definition div62_eta_branch := nth 5 (fst div62_cont_parts) Sskip.
Definition div62_eta_body (neg : bool) := match div62_eta_branch with
  | Sifthenelse _ a b=>if neg then a else b | _=>Sskip end.
Definition div62_eta_parts neg := split_statement_last (div62_eta_body neg).
Definition div62_cancel_updates := statement_sequence (skipn 6 (fst div62_cont_parts)) (snd div62_cont_parts).
Definition div62_w_statement (neg : bool) := statement_sequence
  (skipn (if neg then 13 else 3) (fst (div62_eta_parts neg))) (snd (div62_eta_parts neg)).
Definition div62_cancel_statement (neg : bool) := statement_sequence
  (skipn (if neg then 13 else 3) (fst (div62_eta_parts neg)))
  (Ssequence (snd (div62_eta_parts neg)) div62_cancel_updates).

Definition div62_w6 f g mask := Int64.loword
  (Int64.and (Int64.mul (Int64.mul f g) (Int64.sub (Int64.mul f f) (Int64.repr 2))) mask).
Definition div62_w4_first f := Int64.loword
  (Int64.add f (Int64.shl (Int64.and (Int64.add f Int64.one) (Int64.repr 4)) Int64.one)).
Definition div62_w4 f g mask := Int64.loword
  (Int64.and (Int64.mul (Int64.repr (Int.unsigned (Int.neg (div62_w4_first f)))) g) mask).
Definition div62_w_word (neg : bool) f g mask := if neg then div62_w6 f g mask else div62_w4 f g mask.
Definition div62_w_long neg f g mask := Int64.repr (Int.unsigned (div62_w_word neg f g mask)).
Definition div62_cancel_temps le neg f g u v q r mask :=
  let w:=div62_w_long neg f g mask in
  PTree.set _r (Vlong (Int64.add r (Int64.mul v w)))
    (PTree.set _q (Vlong (Int64.add q (Int64.mul u w)))
      (PTree.set _g (Vlong (Int64.add g (Int64.mul f w)))
        (PTree.set _w (Vint (div62_w_word neg f g mask)) le))).

Lemma div62_updates_source : div62_cancel_updates =
  Ssequence (Sset _g (Ebinop Oadd (Etempvar _g tulong)
    (Ebinop Omul (Etempvar _f tulong) (Etempvar _w tuint) tulong) tulong))
  (Ssequence (Sset _q (Ebinop Oadd (Etempvar _q tulong)
    (Ebinop Omul (Etempvar _u tulong) (Etempvar _w tuint) tulong) tulong))
  (Ssequence (Sset _r (Ebinop Oadd (Etempvar _r tulong)
    (Ebinop Omul (Etempvar _v tulong) (Etempvar _w tuint) tulong) tulong)) (Sloop Sskip Sbreak))).
Proof. reflexivity. Qed.

Local Ltac cancel_lookup := first [eassumption|apply PTree.gss|rewrite PTree.gso by discriminate;cancel_lookup].
Local Ltac cancel_expr := first [apply eval_Etempvar;cancel_lookup|apply eval_Econst_int|apply eval_Econst_long|
  eapply eval_Ecast;[cancel_expr|reflexivity]|
  eapply eval_Eunop;[cancel_expr|reflexivity]|
  eapply eval_Ebinop;[cancel_expr|cancel_expr|reflexivity]].

Lemma exec_div62_noop e le m : Clight2.exec_stmt secp_ge e le m (Sloop Sskip Sbreak) E0 le m Out_normal.
Proof.
  eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le)
    (out1:=Out_normal) (out2:=Out_break);constructor.
Qed.

Lemma div62_w6_source : div62_w_statement true =
  Sset _w (Ecast (Ebinop Oand
    (Ebinop Omul (Ebinop Omul (Etempvar _f tulong) (Etempvar _g tulong) tulong)
      (Ebinop Osub (Ebinop Omul (Etempvar _f tulong) (Etempvar _f tulong) tulong)
        (Econst_int (Int.repr 2) tint) tulong) tulong)
    (Etempvar _m tulong) tulong) tuint).
Proof. reflexivity. Qed.

Lemma div62_w4_source : div62_w_statement false =
  Ssequence (Sset _w (Ecast (Ebinop Oadd (Etempvar _f tulong)
    (Ebinop Oshl (Ebinop Oand (Ebinop Oadd (Etempvar _f tulong)
      (Econst_int (Int.repr 1) tint) tulong) (Econst_int (Int.repr 4) tint) tulong)
      (Econst_int (Int.repr 1) tint) tulong) tulong) tuint))
  (Sset _w (Ecast (Ebinop Oand
    (Ebinop Omul (Eunop Oneg (Etempvar _w tuint) tuint) (Etempvar _g tulong) tulong)
    (Etempvar _m tulong) tulong) tuint)).
Proof. reflexivity. Qed.

Theorem exec_div62_w e le m neg f g mask :
  le!_f=Some(Vlong f) -> le!_g=Some(Vlong g) -> le!_m=Some(Vlong mask) ->
  Clight2.exec_stmt secp_ge e le m (div62_w_statement neg) E0
    (PTree.set _w (Vint (div62_w_word neg f g mask)) le) m Out_normal.
Proof.
  intros F G M;destruct neg.
  - rewrite div62_w6_source;unfold div62_w_word,div62_w6.
    apply exec_Sset;cancel_expr.
  - rewrite div62_w4_source;unfold div62_w_word,div62_w4.
    replace (PTree.set _w (Vint (Int64.loword
      (Int64.and (Int64.mul (Int64.repr (Int.unsigned (Int.neg (div62_w4_first f)))) g) mask))) le)
      with (PTree.set _w (Vint (Int64.loword
        (Int64.and (Int64.mul (Int64.repr (Int.unsigned (Int.neg (div62_w4_first f)))) g) mask)))
        (PTree.set _w (Vint (div62_w4_first f)) le)) by apply PTree.set2.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
      (le1:=PTree.set _w (Vint (div62_w4_first f)) le).
    + apply exec_Sset;unfold div62_w4_first;cancel_expr.
    + apply exec_Sset;cancel_expr.
Qed.

Theorem exec_div62_updates e le m f g u v q r w :
  le!_f=Some(Vlong f) -> le!_g=Some(Vlong g) -> le!_u=Some(Vlong u) -> le!_v=Some(Vlong v) ->
  le!_q=Some(Vlong q) -> le!_r=Some(Vlong r) -> le!_w=Some(Vint w) ->
  Clight2.exec_stmt secp_ge e le m div62_cancel_updates E0
    (PTree.set _r (Vlong (Int64.add r (Int64.mul v (Int64.repr (Int.unsigned w)))))
      (PTree.set _q (Vlong (Int64.add q (Int64.mul u (Int64.repr (Int.unsigned w)))))
        (PTree.set _g (Vlong (Int64.add g (Int64.mul f (Int64.repr (Int.unsigned w))))) le))) m Out_normal.
Proof.
  intros F G U V Q R W;rewrite div62_updates_source.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _g (Vlong (Int64.add g (Int64.mul f (Int64.repr (Int.unsigned w))))) le).
  - apply exec_Sset;cancel_expr.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
      (le1:=PTree.set _q (Vlong (Int64.add q (Int64.mul u (Int64.repr (Int.unsigned w)))))
        (PTree.set _g (Vlong (Int64.add g (Int64.mul f (Int64.repr (Int.unsigned w))))) le)).
    + apply exec_Sset;cancel_expr.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m).
      * apply exec_Sset;cancel_expr.
      * apply exec_div62_noop.
Qed.

Lemma div62_cancel_source neg : div62_cancel_statement neg =
  if neg then Ssequence (div62_w_statement true) div62_cancel_updates
  else match div62_w_statement false with
    | Ssequence a b=>Ssequence a (Ssequence b div62_cancel_updates)
    | _=>Sskip end.
Proof. destruct neg;reflexivity. Qed.

Theorem exec_div62_cancel e le m neg f g u v q r mask :
  le!_f=Some(Vlong f) -> le!_g=Some(Vlong g) -> le!_u=Some(Vlong u) -> le!_v=Some(Vlong v) ->
  le!_q=Some(Vlong q) -> le!_r=Some(Vlong r) -> le!_m=Some(Vlong mask) ->
  Clight2.exec_stmt secp_ge e le m (div62_cancel_statement neg) E0
    (div62_cancel_temps le neg f g u v q r mask) m Out_normal.
Proof.
  intros F G U V Q R M;rewrite div62_cancel_source.
  pose proof (exec_div62_w e le m neg f g mask F G M) as W.
  unfold div62_cancel_temps,div62_w_long;destruct neg.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
      (le1:=PTree.set _w (Vint (div62_w_word true f g mask)) le).
    + exact W.
    + apply exec_div62_updates;cancel_lookup.
  - rewrite div62_w4_source in W |- *;cbn beta iota.
    inversion W;subst.
    + match goal with H : ?t1 ** ?t2=E0 |- _=>
        destruct (Eapp_E0_inv t1 t2 H) as [-> ->] end.
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[eassumption|].
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[eassumption|].
      apply exec_div62_updates;cancel_lookup.
    + contradiction.
Qed.

Lemma div62_cancel_temps_outside le neg f g u v q r mask id :
  ~In id [_w;_g;_q;_r] -> (div62_cancel_temps le neg f g u v q r mask)!id=le!id.
Proof.
  intro Outside;unfold div62_cancel_temps;rewrite !PTree.gso;[reflexivity| | | |];
    intro Eq;subst id;apply Outside;cbn [In];tauto.
Qed.
