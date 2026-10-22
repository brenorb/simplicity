(** Bounded in-place squaring loops used by the original square-root helper. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns C.jet_secp_square_numeric
 C.jet_secp_square_inplace_storage C.jet_secp_curve_statements C.jet_secp_fns.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words.
Definition root_square_guard limit := Ebinop Olt (Etempvar _j tint) (Econst_int (Int.repr limit) tint) tint.
Definition root_square_step := Sset _j (Ebinop Oadd (Etempvar _j tint) (Econst_int Int.one tint) tint).
Definition root_square_call id := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
 [curve_local_address id;curve_local_address id].
Definition root_square_loop id limit :=
 Sloop (Ssequence (Sifthenelse (root_square_guard limit) Sskip Sbreak) (root_square_call id)) root_square_step.
Definition root_square_for id limit := Ssequence (Sset _j (Econst_int Int.zero tint)) (root_square_loop id limit).
Fixpoint root_body_spine (s : statement) : list statement :=
 match s with Ssequence a b => a::root_body_spine b | _ => [s] end.
Lemma root_square_all_sources :
 map (fun n => nth n (root_body_spine (fn_body f_secp256k1_fe_sqrt_var)) Sskip)
   [6;9;12;15;18;21;24;27;30;33;35]%nat =
 [root_square_for _x6 3;root_square_for _x9 3;root_square_for _x11 2;
  root_square_for _x22 11;root_square_for _x44 22;root_square_for _x88 44;
  root_square_for _x176 88;root_square_for _x220 44;root_square_for _x223 3;
  root_square_for _t1 23;root_square_for _t1 6].
Proof. reflexivity. Qed.
Lemma root_square_first_source :
 (match fn_body f_secp256k1_fe_sqrt_var with
 | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence loop _)))))) => loop
 | _ => Sskip end)=root_square_for _x6 3.
Proof. reflexivity. Qed.
Fixpoint root_square_words (n : nat) w := match n with
 | O => w | S k => root_square_words k (square_words w) end.

Lemma eval_root_square_guard e le m limit j :
 0<=j<=limit -> limit<=88 -> le!_j=Some (Vint (Int.repr j)) ->
 eval_expr secp_ge e le m (root_square_guard limit) (Vint (if Z.ltb j limit then Int.one else Int.zero)).
Proof.
 intros HJ HL HT;unfold root_square_guard.
 eapply eval_Ebinop with (v1:=Vint (Int.repr j)) (v2:=Vint (Int.repr limit));
   [apply eval_Etempvar;exact HT|constructor|].
 change (Some (Val.of_bool (Int.lt (Int.repr j) (Int.repr limit)))=
   Some (Vint (if Z.ltb j limit then Int.one else Int.zero))).
 unfold Int.lt;rewrite !Int.signed_repr by
   (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
 destruct (zlt j limit),(Z.ltb_spec j limit);try lia;reflexivity.
Qed.
Lemma exec_root_square_step e le m j : 0<=j<88 -> le!_j=Some (Vint (Int.repr j)) ->
 Clight2.exec_stmt secp_ge e le m root_square_step E0 (PTree.set _j (Vint (Int.repr (j+1))) le) m Out_normal.
Proof.
 intros HJ HT;apply exec_Sset;eapply eval_Ebinop with (v1:=Vint (Int.repr j)) (v2:=Vint Int.one);
   [apply eval_Etempvar;exact HT|constructor|].
 change (Some (Vint (Int.add (Int.repr j) Int.one))=Some (Vint (Int.repr (j+1)))).
 unfold Int.add;rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia);reflexivity.
Qed.

Lemma exec_root_square_owned e le m id b w :
 e!id=Some (b,curve_fe_type) -> e!_secp256k1_fe_sqr=None -> square_input_bounds w ->
 fe_at m b 0 (words5 w) -> Mem.range_perm m b 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (root_square_call id) E0 le mf Out_normal /\
 fe_at mf b 0 (words5 (square_words w)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
 square_input_bounds (square_words w) /\ lframe (fun bx _=>bx<>b) m mf.
Proof.
 intros EL EG BW W F.
 destruct (eval_square_inplace_from_storage w m b BW W F)
   as (mf & HC & WF & FF & Val & Bound & Tight & Frame).
 exists mf;split.
 - unfold root_square_call;eapply exec_curve_call with (vargs:=[Vptr b Ptrofs.zero;Vptr b Ptrofs.zero]) (v:=Vundef).
   + unfold secp_pure;repeat (first [left;reflexivity|right]).
   + exact EG.
   + eapply eval_Econs;[apply eval_curve_local;exact EL|reflexivity|].
     eapply eval_Econs;[apply eval_curve_local;exact EL|reflexivity|constructor].
   + exact HC.
 - split;[exact WF|];split;[exact FF|];split;assumption.
Qed.

Theorem exec_root_square_loop_owned n id limit e b : forall j le m w,
 0<=j -> j+Z.of_nat n=limit -> limit<=88 ->
 le!_j=Some (Vint (Int.repr j)) -> e!id=Some (b,curve_fe_type) -> e!_secp256k1_fe_sqr=None ->
 square_input_bounds w -> fe_at m b 0 (words5 w) -> Mem.range_perm m b 0 40 Cur Freeable ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m (root_square_loop id limit) E0 lef mf Out_normal /\
 fe_at mf b 0 (words5 (root_square_words n w)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
 square_input_bounds (root_square_words n w) /\ lef!_j=Some (Vint (Int.repr limit)) /\
 (forall k, k<>_j -> lef!k=le!k) /\ lframe (fun bx _=>bx<>b) m mf.
Proof.
 induction n as [|n IH];intros j le m w HJ HEnd HL HT EL EG BW W F.
 - assert (j=limit) by (cbn in HEnd;lia);subst j.
   exists m,le;split.
   + unfold root_square_loop;eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
     apply exec_Sseq_2;[|discriminate].
     eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
     * pose proof (eval_root_square_guard e le m limit limit ltac:(lia) HL HT) as G.
       rewrite Z.ltb_irrefl in G;exact G.
     * reflexivity.
     * constructor.
   + cbn [root_square_words];split;[exact W|];split;[exact F|];split;[exact BW|];split;[exact HT|].
     split;[intros;reflexivity|apply lframe_refl].
 - assert (HB : 0<=j<limit) by (rewrite Nat2Z.inj_succ in HEnd;pose proof (Nat2Z.is_nonneg n);lia).
   destruct (exec_root_square_owned e le m id b w EL EG BW W F) as (mi & CS & WI & FI & BI & FrameI).
   set (next:=PTree.set _j (Vint (Int.repr (j+1))) le).
   destruct (IH (j+1) next mi (square_words w) ltac:(lia)
     ltac:(rewrite Nat2Z.inj_succ in HEnd;lia) HL ltac:(unfold next;apply PTree.gss) EL EG BI WI FI)
     as (mf & lef & Rest & WF & FF & BF & JF & Temps & FrameF).
   exists mf,lef;split.
   + unfold root_square_loop in Rest |- *.
     eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0)
       (le1:=le) (m1:=mi) (out1:=Out_normal) (le2:=next) (m2:=mi).
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m).
       -- eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
          ++ pose proof (eval_root_square_guard e le m limit j ltac:(lia) HL HT) as G.
             rewrite (proj2 (Z.ltb_lt j limit) ltac:(lia)) in G;exact G.
          ++ reflexivity.
          ++ constructor.
       -- exact CS.
     * constructor.
     * apply exec_root_square_step;[lia|exact HT].
     * exact Rest.
   + cbn [root_square_words];split;[exact WF|];split;[exact FF|];split;[exact BF|];split;[exact JF|].
     split.
     * intros k HK;rewrite Temps by exact HK;unfold next;rewrite PTree.gso by exact HK;reflexivity.
     * eapply lframe_trans;eassumption.
Qed.

Theorem exec_root_square_for_owned n id e le m b w :
 Z.of_nat n<=88 -> e!id=Some (b,curve_fe_type) -> e!_secp256k1_fe_sqr=None ->
 square_input_bounds w -> fe_at m b 0 (words5 w) -> Mem.range_perm m b 0 40 Cur Freeable ->
 exists mf lef,
 Clight2.exec_stmt secp_ge e le m (root_square_for id (Z.of_nat n)) E0 lef mf Out_normal /\
 fe_at mf b 0 (words5 (root_square_words n w)) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
 square_input_bounds (root_square_words n w) /\ lef!_j=Some (Vint (Int.repr (Z.of_nat n))) /\
 (forall k, k<>_j -> lef!k=le!k) /\ lframe (fun bx _=>bx<>b) m mf.
Proof.
 intros HN EL EG BW W F.
 set (start:=PTree.set _j (Vint Int.zero) le).
 destruct (exec_root_square_loop_owned n id (Z.of_nat n) e b 0 start m w ltac:(lia) ltac:(lia) HN
   ltac:(unfold start;apply PTree.gss) EL EG BW W F)
   as (mf & lef & Loop & WF & FF & BF & JF & Temps & Frame).
 exists mf,lef;split.
 - unfold root_square_for;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=start) (m1:=m).
   + apply exec_Sset;constructor.
   + exact Loop.
 - split;[exact WF|];split;[exact FF|];split;[exact BF|];split;[exact JF|];split.
   + intros k HK;rewrite Temps by exact HK;unfold start;rewrite PTree.gso by exact HK;reflexivity.
   + exact Frame.
Qed.
