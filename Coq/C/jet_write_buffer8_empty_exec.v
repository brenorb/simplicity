(** Execute an actual write_buffer8 empty-buffer loop iteration, retaining
    the comparison, false-tag return, skip call and unsigned halving update.
    Full loop/initial-state/public consumers are separate obligations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_arith8_layout_exec C.jet_umul128_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition buffer8_actual_loop := match f_simplicity_write_buffer8.(fn_body) with
  | Ssequence _ (Ssequence _ (Ssequence _ loop)) => loop | _ => Sskip end.
Definition buffer8_loop_body := match buffer8_actual_loop with Sloop body _ => body | _ => Sskip end.
Definition buffer8_loop_update := match buffer8_actual_loop with Sloop _ update => update | _ => Sskip end.
Definition buffer8_present_branch := match buffer8_loop_body with
  | Ssequence _ (Ssequence _ (Sifthenelse _ yes _)) => yes | _ => Sskip end.
Definition buffer8_guard_expr := Ebinop Olt (Econst_int Int.zero tint) (Etempvar _i tulong) tint.
Definition buffer8_tag_expr := Ebinop Ole (Etempvar _i tulong) (Etempvar _len tulong) tint.
Definition buffer8_skip_expr := Ebinop Omul (Etempvar _i tulong) (Econst_int (Int.repr 8) tint) tulong.
Definition buffer8_tag_call := Scall (Some _t'2)
  (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
  [Etempvar _dst (tptr (Tstruct _frameItem noattr)); buffer8_tag_expr].
Definition buffer8_skip_call := Scall None
  (Evar _skipBits (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
  [Etempvar _dst (tptr (Tstruct _frameItem noattr)); buffer8_skip_expr].

Lemma buffer8_actual_loop_shape : buffer8_actual_loop = Sloop
  (Ssequence (Sifthenelse buffer8_guard_expr Sskip Sbreak)
    (Ssequence buffer8_tag_call (Sifthenelse (Etempvar _t'2 tbool) buffer8_present_branch buffer8_skip_call)))
  (Sset _i (Ebinop Odiv (Etempvar _i tulong) (Econst_int (Int.repr 2) tint) tulong)).
Proof. reflexivity. Qed.

Lemma buffer8_writeBit_symbol : Genv.find_symbol (Clight.genv_genv ge0) _writeBit = Some (jet_symbol_block _writeBit).
Proof. vm_compute; reflexivity. Qed.
Lemma buffer8_writeBit_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _writeBit) Ptrofs.zero) = Some (Internal f_writeBit).
Proof. vm_compute; reflexivity. Qed.
Lemma buffer8_skipBits_symbol : Genv.find_symbol (Clight.genv_genv ge0) _skipBits = Some (jet_symbol_block _skipBits).
Proof. vm_compute; reflexivity. Qed.
Lemma buffer8_skipBits_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _skipBits) Ptrofs.zero) = Some (Internal f_skipBits).
Proof. vm_compute; reflexivity. Qed.

Lemma eval_buffer8_guard e le m j : 0 <= j <= Int64.max_unsigned ->
  le!_i = Some (Vlong (Int64.repr j)) ->
  eval_expr ge0 e le m buffer8_guard_expr (Vint (if 0 <? j then Int.one else Int.zero)).
Proof.
  intros HJ HI. eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vlong (Int64.repr j)).
  - apply eval_Econst_int.
  - apply eval_Etempvar; exact HI.
  - change (Some (Val.of_bool (Int64.ltu Int64.zero (Int64.repr j))) =
      Some (Vint (if 0 <? j then Int.one else Int.zero))).
    unfold Int64.ltu. rewrite Int64.unsigned_zero, Int64.unsigned_repr by exact HJ.
    destruct (0 <? j) eqn:HC.
    + apply Z.ltb_lt in HC. rewrite zlt_true by lia; reflexivity.
    + apply Z.ltb_ge in HC. rewrite zlt_false by lia; reflexivity.
Qed.

(** Both leading PRODUCTION assertion loops have this exact false guard;
    the assertion body is unreachable, regardless of its statement. *)
Lemma exec_buffer8_disabled_assert e le m assertion :
  Clight2.exec_stmt ge0 e le m
    (Sloop (Sifthenelse (Eunop Onotbool (Econst_int Int.one tint) tint) assertion Sskip) Sbreak)
    E0 le m Out_normal.
Proof.
  eapply exec_Sloop_stop2 with (t1 := E0) (t2 := E0)
    (le1 := le) (m1 := m) (out1 := Out_normal) (out2 := Out_break).
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
    + eapply eval_Eunop with (v1 := Vint Int.one); [apply eval_Econst_int|reflexivity].
    + reflexivity.
    + apply exec_Sskip.
  - constructor.
  - apply exec_Sbreak.
  - constructor.
Qed.
Lemma eval_buffer8_empty_tag e le m j : 0 < j <= Int64.max_unsigned ->
  le!_i = Some (Vlong (Int64.repr j)) -> le!_len = Some (Vlong Int64.zero) ->
  eval_expr ge0 e le m buffer8_tag_expr (Vint Int.zero).
Proof.
  intros HJ HI HL. eapply eval_Ebinop with (v1 := Vlong (Int64.repr j)) (v2 := Vlong Int64.zero).
  - apply eval_Etempvar; exact HI.
  - apply eval_Etempvar; exact HL.
  - change (Some (Val.of_bool (negb (Int64.ltu Int64.zero (Int64.repr j)))) = Some (Vint Int.zero)).
    unfold Int64.ltu. rewrite Int64.unsigned_zero, Int64.unsigned_repr by lia.
    rewrite zlt_true by lia; reflexivity.
Qed.
Lemma eval_buffer8_skip_expr e le m j : 0 <= j <= Int64.max_unsigned ->
  le!_i = Some (Vlong (Int64.repr j)) ->
  eval_expr ge0 e le m buffer8_skip_expr (Vlong (Int64.repr (8 * j))).
Proof.
  intros HJ HI. eapply eval_Ebinop with (v1 := Vlong (Int64.repr j)) (v2 := Vint (Int.repr 8)).
  - apply eval_Etempvar; exact HI.
  - apply eval_Econst_int.
  - change (Some (Vlong (Int64.mul (Int64.repr j) (Int64.repr 8))) = Some (Vlong (Int64.repr (8 * j)))).
    unfold Int64.mul. rewrite (Int64.unsigned_repr j HJ).
    change (Int64.unsigned (Int64.repr 8)) with 8.
    rewrite Z.mul_comm; reflexivity.
Qed.

Lemma exec_buffer8_empty_iteration e le m mb mf bf base j :
  e!_writeBit = None -> e!_skipBits = None ->
  le!_dst = Some (Vptr bf (Ptrofs.repr base)) -> le!_len = Some (Vlong Int64.zero) ->
  le!_i = Some (Vlong (Int64.repr j)) -> 0 < j <= Int64.max_unsigned ->
  Clight2.eval_funcall ge0 m (Internal f_writeBit) [Vptr bf (Ptrofs.repr base); Vint Int.zero] E0 mb (Vint Int.zero) ->
  Clight2.eval_funcall ge0 mb (Internal f_skipBits) [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr (8 * j))] E0 mf Vundef ->
  Clight2.exec_stmt ge0 e le m (Ssequence buffer8_loop_body buffer8_loop_update) E0
    (PTree.set _i (Vlong (Int64.repr (j / 2))) (PTree.set _t'2 (Vint Int.zero) le)) mf Out_normal.
Proof.
  intros EB ES HD HL HI HJ HBit HSkip.
  set (le1 := PTree.set _t'2 (Vint Int.zero) le).
  unfold buffer8_loop_body, buffer8_loop_update. rewrite buffer8_actual_loop_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mf).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m).
    + eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
      * pose proof (eval_buffer8_guard e le m j ltac:(lia) HI) as HG.
        assert (Hpos : (0 <? j) = Datatypes.true) by (apply Z.ltb_lt; lia).
        rewrite Hpos in HG; exact HG.
      * reflexivity.
      * apply exec_Sskip.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mb).
      * eapply exec_Scall with (vf := Vptr (jet_symbol_block _writeBit) Ptrofs.zero)
          (vargs := [Vptr bf (Ptrofs.repr base); Vint Int.zero]) (f := Internal f_writeBit) (vres := Vint Int.zero).
        -- reflexivity.
        -- eapply eval_Elvalue; [apply eval_Evar_global; [exact EB|exact buffer8_writeBit_symbol]|apply deref_loc_reference; reflexivity].
        -- eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
           eapply eval_Econs; [eapply eval_buffer8_empty_tag; eauto|reflexivity|apply eval_Enil].
        -- exact buffer8_writeBit_funct.
        -- reflexivity.
        -- exact HBit.
      * eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
        -- apply eval_Etempvar. unfold le1; apply PTree.gss.
        -- reflexivity.
        -- eapply call_frame_writer with (f := f_skipBits) (b := jet_symbol_block _skipBits)
             (v := Vlong (Int64.repr (8 * j))) (vret := Vundef).
           ++ exact ES.
           ++ unfold le1. rewrite PTree.gso by discriminate; exact HD.
           ++ reflexivity.
           ++ exact buffer8_skipBits_symbol.
           ++ exact buffer8_skipBits_funct.
           ++ apply eval_buffer8_skip_expr; [lia|unfold le1; rewrite PTree.gso by discriminate; exact HI].
           ++ reflexivity.
           ++ exact HSkip.
  - apply exec_set. eapply eval_Ebinop with (v1 := Vlong (Int64.repr j)) (v2 := Vint (Int.repr 2)).
    + apply eval_Etempvar. unfold le1; rewrite PTree.gso by discriminate; exact HI.
    + apply eval_Econst_int.
    + change (Some (Vlong (Int64.divu (Int64.repr j) (Int64.repr 2))) = Some (Vlong (Int64.repr (j / 2)))).
      unfold Int64.divu. rewrite (Int64.unsigned_repr j ltac:(lia)).
      change (Int64.unsigned (Int64.repr 2)) with 2.
      reflexivity.
Qed.

Lemma exec_buffer8_empty_stop e le m : le!_i = Some (Vlong Int64.zero) ->
  Clight2.exec_stmt ge0 e le m buffer8_actual_loop E0 le m Out_normal.
Proof.
  intros HI. rewrite buffer8_actual_loop_shape.
  eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
  apply exec_Sseq_2; [|discriminate].
  eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
  - exact (eval_buffer8_guard e le m 0 ltac:(change (0 <= 0 <= 18446744073709551615); lia) HI).
  - reflexivity.
  - apply exec_Sbreak.
Qed.
