(** Actual CTZ-free portion of the variable divstep loop. The caller must
    still derive the returned count; no counting model is introduced here. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix C.jet_sx_mem.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition div62_parts := split_statement_last (fn_body f_secp256k1_modinv64_divsteps_62_var).
Definition div62_loop := nth 7 (fst div62_parts) Sskip.
Definition div62_loop_body := match div62_loop with Sloop body _=>body | _=>Sskip end.
Definition div62_after_count := match div62_loop_body with
  | Ssequence _ (Ssequence _ rest)=>rest | _=>Sskip end.
Definition div62_count_parts := split_statement_last div62_after_count.
Definition div62_count_prefix := statement_sequence (firstn 6 (fst div62_count_parts)) Sskip.
Definition div62_after_count_prefix := statement_sequence (skipn 6 (fst div62_count_parts)) (snd div62_count_parts).
Definition div62_copy_count := Sset _zeros (Etempvar _t'1 tint).
Definition div62_count_test := Ebinop Oeq (Etempvar _i tint) (Econst_int Int.zero tint) tint.
Lemma div62_count_source : div62_after_count =
  statement_sequence (firstn 6 (fst div62_count_parts)) div62_after_count_prefix.
Proof. reflexivity. Qed.
Lemma div62_count_prefix_source : div62_count_prefix =
  Ssequence (Sset _g (Ebinop Oshr (Etempvar _g tulong) (Etempvar _zeros tint) tulong))
  (Ssequence (Sset _u (Ebinop Oshl (Etempvar _u tulong) (Etempvar _zeros tint) tulong))
  (Ssequence (Sset _v (Ebinop Oshl (Etempvar _v tulong) (Etempvar _zeros tint) tulong))
  (Ssequence (Sset _eta (Ebinop Osub (Etempvar _eta tlong) (Etempvar _zeros tint) tlong))
  (Ssequence (Sset _i (Ebinop Osub (Etempvar _i tint) (Etempvar _zeros tint) tint))
  (Ssequence (Sifthenelse div62_count_test Sbreak Sskip) Sskip))))).
Proof. reflexivity. Qed.
Lemma div62_loop_body_source : div62_loop_body =
  match div62_loop_body with
  | Ssequence first (Ssequence (Ssequence call _) _) =>
    Ssequence first (Ssequence (Ssequence call div62_copy_count) div62_after_count)
  | _=>Sskip end.
Proof. reflexivity. Qed.

Definition div62_count_temps le g u v eta i z :=
  PTree.set _i (Vint (Int.repr (i-z)))
    (PTree.set _eta (Vlong (Int64.repr (eta-z)))
      (PTree.set _v (Vlong (Int64.shl v (Int64.repr z)))
        (PTree.set _u (Vlong (Int64.shl u (Int64.repr z)))
          (PTree.set _g (Vlong (Int64.shru g (Int64.repr z))) le)))).
Definition div62_count_outcome i z := if Z.eqb i z then Out_break else Out_normal.
Lemma exec_div62_copy_count e le m z : le!_t'1=Some(Vint (Int.repr z)) ->
  Clight2.exec_stmt secp_ge e le m div62_copy_count E0
    (PTree.set _zeros (Vint (Int.repr z)) le) m Out_normal.
Proof. intro Count;apply exec_Sset;apply eval_Etempvar;exact Count. Qed.
Lemma div62_count_temps_outside le g u v eta i z id : ~In id [_g;_u;_v;_eta;_i] ->
  (div62_count_temps le g u v eta i z)!id=le!id.
Proof.
  intro Outside;unfold div62_count_temps;rewrite !PTree.gso;[reflexivity| | | | |];
    intro Eq;subst id;apply Outside;cbn [In];tauto.
Qed.
Lemma div62_count_shift_guard z : 0<=z<=62 -> Int.ltu (Int.repr z) Int64.iwordsize'=true.
Proof.
  intro Z;unfold Int.ltu;rewrite Int.unsigned_repr by (change (0<=z<=4294967295);lia).
  change ((if zlt z 64 then true else false)=true);destruct (zlt z 64);[reflexivity|lia].
Qed.
Lemma eval_div62_shift e le m id w z (left : bool) : 0<=z<=62 ->
  le!id=Some(Vlong w) -> le!_zeros=Some(Vint (Int.repr z)) ->
  eval_expr secp_ge e le m
    (Ebinop (if left then Oshl else Oshr) (Etempvar id tulong) (Etempvar _zeros tint) tulong)
    (Vlong (if left then Int64.shl w (Int64.repr z) else Int64.shru w (Int64.repr z))).
Proof.
  intros Range W Z;destruct left;eapply eval_Ebinop;
    [apply eval_Etempvar;exact W|apply eval_Etempvar;exact Z| |
     apply eval_Etempvar;exact W|apply eval_Etempvar;exact Z|].
  all: first [
    change ((if Int.ltu (Int.repr z) Int64.iwordsize' then
      Some(Vlong (Int64.shl w (Int64.repr (Int.unsigned (Int.repr z))))) else None)=
      Some(Vlong (Int64.shl w (Int64.repr z)))) |
    change ((if Int.ltu (Int.repr z) Int64.iwordsize' then
      Some(Vlong (Int64.shru w (Int64.repr (Int.unsigned (Int.repr z))))) else None)=
      Some(Vlong (Int64.shru w (Int64.repr z))))];
    rewrite div62_count_shift_guard by exact Range;
    rewrite Int.unsigned_repr by (change (0<=z<=4294967295);lia);reflexivity.
Qed.
Lemma div62_count_equal i z : 0<=z<=i -> i<=62 ->
  Int.eq (Int.repr (i-z)) Int.zero=Z.eqb i z.
Proof.
  intros Range I;destruct (Z.eqb_spec i z) as [Eq|NE].
  - subst i;rewrite Z.sub_diag;reflexivity.
  - destruct (Int.eq (Int.repr (i-z)) Int.zero) eqn:Test;[|reflexivity].
    pose proof (Int.eq_spec (Int.repr (i-z)) Int.zero) as Eq;rewrite Test in Eq.
    apply (f_equal Int.signed) in Eq;rewrite Int.signed_repr in Eq by
      (change (-2147483648<=i-z<=2147483647);lia).
    change (i-z=0) in Eq;lia.
Qed.

Theorem exec_div62_count_prefix e le m g u v eta i z :
  0<=z<=i -> i<=62 ->
  le!_g=Some(Vlong g) -> le!_u=Some(Vlong u) -> le!_v=Some(Vlong v) ->
  le!_eta=Some(Vlong (Int64.repr eta)) -> le!_i=Some(Vint (Int.repr i)) ->
  le!_zeros=Some(Vint (Int.repr z)) ->
  Clight2.exec_stmt secp_ge e le m div62_count_prefix E0
    (div62_count_temps le g u v eta i z) m (div62_count_outcome i z).
Proof.
  intros Range I G U V Eta Index Zeros.
  rewrite div62_count_prefix_source;unfold div62_count_temps.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _g (Vlong (Int64.shru g (Int64.repr z))) le).
  - apply exec_Sset;exact (eval_div62_shift e le m _g g z false ltac:(lia) G Zeros).
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
      (le1:=PTree.set _u (Vlong (Int64.shl u (Int64.repr z)))
        (PTree.set _g (Vlong (Int64.shru g (Int64.repr z))) le)).
    + apply exec_Sset;apply (eval_div62_shift e _ m _u u z true ltac:(lia));
        rewrite PTree.gso by discriminate;assumption.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
        (le1:=PTree.set _v (Vlong (Int64.shl v (Int64.repr z)))
          (PTree.set _u (Vlong (Int64.shl u (Int64.repr z)))
            (PTree.set _g (Vlong (Int64.shru g (Int64.repr z))) le))).
      * apply exec_Sset;apply (eval_div62_shift e _ m _v v z true ltac:(lia));
          rewrite !PTree.gso by discriminate;assumption.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
          (le1:=PTree.set _eta (Vlong (Int64.repr (eta-z)))
            (PTree.set _v (Vlong (Int64.shl v (Int64.repr z)))
              (PTree.set _u (Vlong (Int64.shl u (Int64.repr z)))
                (PTree.set _g (Vlong (Int64.shru g (Int64.repr z))) le)))).
        -- apply exec_Sset;eapply eval_Ebinop.
           ++ apply eval_Etempvar;rewrite !PTree.gso by discriminate;exact Eta.
           ++ apply eval_Etempvar;rewrite !PTree.gso by discriminate;exact Zeros.
           ++ change (Some (Vlong (Int64.sub (Int64.repr eta)
                (Int64.repr (Int.signed (Int.repr z))))) = Some (Vlong (Int64.repr (eta-z)))).
              rewrite Int.signed_repr by (change (-2147483648<=z<=2147483647);lia).
              f_equal;f_equal;rewrite Int64.sub_signed;apply Int64.eqm_samerepr.
              apply Int64.eqm_sub;eapply Int64.eqm_trans;
                [apply Int64.eqm_signed_unsigned|apply Int64.eqm_sym,Int64.eqm_unsigned_repr|
                 apply Int64.eqm_signed_unsigned|apply Int64.eqm_sym,Int64.eqm_unsigned_repr].
        -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
             (le1:=div62_count_temps le g u v eta i z).
           ++ apply exec_Sset;eapply eval_Ebinop.
              ** apply eval_Etempvar;rewrite !PTree.gso by discriminate;exact Index.
              ** apply eval_Etempvar;rewrite !PTree.gso by discriminate;exact Zeros.
              ** change (Some (Vint (Int.sub (Int.repr i) (Int.repr z)))=Some(Vint (Int.repr (i-z)))).
                 rewrite Int.sub_signed,(Int.signed_repr i),(Int.signed_repr z) by
                   (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia);reflexivity.
           ++ unfold div62_count_outcome.
              destruct (Z.eqb i z) eqn:Eq.
              ** eapply exec_Sseq_2;[|discriminate].
                 eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
                 --- unfold div62_count_test;eapply eval_Ebinop;[apply eval_Etempvar;apply PTree.gss|constructor|].
                     change (Some(Val.of_bool (Int.eq (Int.repr (i-z)) Int.zero))=Some(Vint Int.one)).
                     rewrite div62_count_equal by lia;rewrite Eq;reflexivity.
                 --- reflexivity.
                 --- constructor.
              ** eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m).
                 --- eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
                     +++ unfold div62_count_test;eapply eval_Ebinop;[apply eval_Etempvar;apply PTree.gss|constructor|].
                         change (Some(Val.of_bool (Int.eq (Int.repr (i-z)) Int.zero))=Some(Vint Int.zero)).
                         rewrite div62_count_equal by lia;rewrite Eq;reflexivity.
                     +++ reflexivity.
                     +++ constructor.
                 --- constructor.
Qed.
