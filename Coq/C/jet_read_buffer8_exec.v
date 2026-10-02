(** Exact actual read_buffer8 loop branches. These INTERNAL adapters retain
    all calls, byte-pointer arithmetic and length stores. Initial-memory and
    canonical-buffer consumers must derive their execution premises. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_readBit_layout C.jet_write_buffer8_empty_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition buffer8_read_loop := match f_simplicity_read_buffer8.(fn_body) with
  | Ssequence _ (Ssequence _ (Ssequence _ loop)) => loop | _ => Sskip end.
Definition buffer8_read_body := match buffer8_read_loop with Sloop body _ => body | _ => Sskip end.
Definition buffer8_read_update := match buffer8_read_loop with Sloop _ update => update | _ => Sskip end.
Definition buffer8_read_present := match buffer8_read_body with
  | Ssequence _ (Ssequence _ (Sifthenelse _ yes _)) => yes | _ => Sskip end.
Definition buffer8_read_absent := Scall None
  (Evar _forwardBits (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
  [Etempvar _src (tptr (Tstruct _frameItem noattr)); buffer8_skip_expr].
Definition buffer8_read_tag := Scall (Some _t'2)
  (Evar _readBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tbool cc_default))
  [Etempvar _src (tptr (Tstruct _frameItem noattr))].
Lemma buffer8_read_loop_shape : buffer8_read_loop = Sloop
  (Ssequence (Sifthenelse buffer8_guard_expr Sskip Sbreak)
    (Ssequence buffer8_read_tag (Sifthenelse (Etempvar _t'2 tbool) buffer8_read_present buffer8_read_absent)))
  (Sset _i (Ebinop Odiv (Etempvar _i tulong) (Econst_int (Int.repr 2) tint) tulong)).
Proof. reflexivity. Qed.
Lemma buffer8_read_forward_symbol : Genv.find_symbol (Clight.genv_genv ge0) _forwardBits =
  Some (jet_symbol_block _forwardBits).
Proof. vm_compute; reflexivity. Qed.
Lemma buffer8_read_forward_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _forwardBits) Ptrofs.zero) = Some (Internal f_forwardBits).
Proof. vm_compute; reflexivity. Qed.
Lemma buffer8_read_array_symbol : Genv.find_symbol (Clight.genv_genv ge0) _read8s =
  Some (jet_symbol_block _read8s).
Proof. vm_compute; reflexivity. Qed.
Lemma buffer8_read_array_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _read8s) Ptrofs.zero) = Some (Internal f_read8s).
Proof. vm_compute; reflexivity. Qed.

Lemma call_buffer8_read_tag e le m mr bf base bit :
  e!_readBit = None -> le!_src = Some (Vptr bf (Ptrofs.repr base)) ->
  Clight2.eval_funcall ge0 m (Internal f_readBit) [Vptr bf (Ptrofs.repr base)] E0 mr (Vint (bit_int bit)) ->
  Clight2.exec_stmt ge0 e le m buffer8_read_tag E0 (PTree.set _t'2 (Vint (bit_int bit)) le) mr Out_normal.
Proof.
  intros HE HF HR. eapply exec_Scall with (vf := Vptr (jet_symbol_block _readBit) Ptrofs.zero)
    (vargs := [Vptr bf (Ptrofs.repr base)]) (f := Internal f_readBit) (vres := Vint (bit_int bit)).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact HE|exact symbol_readBit]|apply deref_loc_reference; reflexivity].
  - eapply eval_Econs; [apply eval_Etempvar; exact HF|reflexivity|apply eval_Enil].
  - exact funct_readBit.
  - reflexivity.
  - exact HR.
Qed.

Lemma exec_buffer8_read_absent e le m mf bf base j :
  e!_forwardBits = None -> le!_src = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_i = Some (Vlong (Int64.repr j)) -> 0 <= j <= Int64.max_unsigned ->
  Clight2.eval_funcall ge0 m (Internal f_forwardBits)
    [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr (8 * j))] E0 mf Vundef ->
  Clight2.exec_stmt ge0 e le m buffer8_read_absent E0 le mf Out_normal.
Proof.
  intros HE HF HI HJ HR. eapply exec_Scall with (vf := Vptr (jet_symbol_block _forwardBits) Ptrofs.zero)
    (vargs := [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr (8 * j))]) (f := Internal f_forwardBits) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact HE|exact buffer8_read_forward_symbol]|apply deref_loc_reference; reflexivity].
  - eapply eval_Econs; [apply eval_Etempvar; exact HF|reflexivity|].
    eapply eval_Econs; [exact (eval_buffer8_skip_expr e le m j HJ HI)|reflexivity|apply eval_Enil].
  - exact buffer8_read_forward_funct.
  - reflexivity.
  - exact HR.
Qed.

Definition buffer8_read_present_temps le bo output count :=
  PTree.set _t'3 (Vlong (Int64.repr count)) (PTree.set _buf (Vptr bo (Ptrofs.repr output)) le).
Lemma exec_buffer8_read_present e le m mr mf bf base bo output bl slot j count :
  e!_read8s = None -> le!_src = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_buf = Some (Vptr bo (Ptrofs.repr output)) -> le!_len = Some (Vptr bl (Ptrofs.repr slot)) ->
  le!_i = Some (Vlong (Int64.repr j)) ->
  0 <= output -> output + j <= Ptrofs.max_unsigned -> 0 <= slot <= Ptrofs.max_unsigned ->
  0 <= j <= Int64.max_unsigned -> 0 <= count <= Int64.max_unsigned ->
  Clight2.eval_funcall ge0 m (Internal f_read8s)
    [Vptr bo (Ptrofs.repr output); Vlong (Int64.repr j); Vptr bf (Ptrofs.repr base)] E0 mr Vundef ->
  Mem.load Mint64 mr bl slot = Some (Vlong (Int64.repr count)) ->
  Mem.store Mint64 mr bl slot (Vlong (Int64.repr (count + j))) = Some mf ->
  Clight2.exec_stmt ge0 e le m buffer8_read_present E0
    (buffer8_read_present_temps le bo (output + j) count) mf Out_normal.
Proof.
  intros HE HF HB HL HI HO HM HS HJ HC HR Hload Hstore.
  set (next := PTree.set _buf (Vptr bo (Ptrofs.repr (output + j))) le).
  assert (Haddr : Ptrofs.add (Ptrofs.repr output)
    (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr j))) = Ptrofs.repr (output + j)).
  { unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by exact HJ.
    unfold Ptrofs.mul, Ptrofs.add. change (Ptrofs.unsigned (Ptrofs.repr 1)) with 1.
    rewrite (Ptrofs.unsigned_repr j) by lia. rewrite Z.mul_1_l.
    rewrite !Ptrofs.unsigned_repr by lia. reflexivity. }
  unfold buffer8_read_present, buffer8_read_body, buffer8_read_loop; cbn [f_simplicity_read_buffer8 fn_body].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le).
  - eapply exec_Scall with (vf := Vptr (jet_symbol_block _read8s) Ptrofs.zero)
      (vargs := [Vptr bo (Ptrofs.repr output); Vlong (Int64.repr j); Vptr bf (Ptrofs.repr base)])
      (f := Internal f_read8s) (vres := Vundef).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [exact HE|exact buffer8_read_array_symbol]|apply deref_loc_reference; reflexivity].
    + eapply eval_Econs; [apply eval_Etempvar; exact HB|reflexivity|].
      eapply eval_Econs; [apply eval_Etempvar; exact HI|reflexivity|].
      eapply eval_Econs; [apply eval_Etempvar; exact HF|reflexivity|apply eval_Enil].
    + exact buffer8_read_array_funct.
    + reflexivity.
    + exact HR.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := next).
    + apply exec_set. eapply eval_Ebinop with (v1 := Vptr bo (Ptrofs.repr output)) (v2 := Vlong (Int64.repr j)).
      * apply eval_Etempvar; exact HB.
      * apply eval_Etempvar; exact HI.
      * change (Some (Vptr bo (Ptrofs.add (Ptrofs.repr output)
          (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr j))))) = Some (Vptr bo (Ptrofs.repr (output + j)))).
        rewrite Haddr; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := buffer8_read_present_temps le bo (output + j) count).
      * apply exec_set. eapply eval_Elvalue.
        -- eapply eval_Ederef. apply eval_Etempvar. unfold next; rewrite PTree.gso by discriminate; exact HL.
        -- apply deref_loc_value with (chunk := Mint64); [reflexivity|].
           unfold Mem.loadv. rewrite Ptrofs.unsigned_repr by exact HS. exact Hload.
      * eapply exec_Sassign_value with (v := Vlong (Int64.repr (count + j)))
          (v2 := Vlong (Int64.repr (count + j))) (b := bl) (ofs := Ptrofs.repr slot).
        -- eapply eval_Ederef. apply eval_Etempvar. unfold buffer8_read_present_temps.
           repeat rewrite PTree.gso by discriminate; exact HL.
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.repr count)) (v2 := Vlong (Int64.repr j)).
           ++ apply eval_Etempvar; apply PTree.gss.
           ++ apply eval_Etempvar. unfold buffer8_read_present_temps.
              repeat rewrite PTree.gso by discriminate; exact HI.
           ++ change (Some (Vlong (Int64.add (Int64.repr count) (Int64.repr j))) =
                Some (Vlong (Int64.repr (count + j)))).
              unfold Int64.add. rewrite !Int64.unsigned_repr by lia. reflexivity.
        -- reflexivity.
        -- apply assign_loc_value with (chunk := Mint64); [reflexivity|].
           unfold Mem.storev. rewrite Ptrofs.unsigned_repr by exact HS. exact Hstore.
Qed.

Lemma exec_buffer8_read_body e le m mr mf lef bf base j bit :
  e!_readBit = None -> le!_src = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_i = Some (Vlong (Int64.repr j)) -> 0 < j <= Int64.max_unsigned ->
  Clight2.eval_funcall ge0 m (Internal f_readBit) [Vptr bf (Ptrofs.repr base)] E0 mr (Vint (bit_int bit)) ->
  Clight2.exec_stmt ge0 e (PTree.set _t'2 (Vint (bit_int bit)) le) mr
    (if bit then buffer8_read_present else buffer8_read_absent) E0 lef mf Out_normal ->
  Clight2.exec_stmt ge0 e le m buffer8_read_body E0 lef mf Out_normal.
Proof.
  intros HE HF HI HJ HR Hbranch. unfold buffer8_read_body. rewrite buffer8_read_loop_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le).
  - eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
    + pose proof (eval_buffer8_guard e le m j ltac:(lia) HI) as HG.
      rewrite (proj2 (Z.ltb_lt 0 j) ltac:(lia)) in HG; exact HG.
    + reflexivity.
    + apply exec_Sskip.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
      (le1 := PTree.set _t'2 (Vint (bit_int bit)) le).
    + eapply call_buffer8_read_tag; eauto.
    + eapply exec_Sifthenelse with (v1 := Vint (bit_int bit)) (b := bit).
      * apply eval_Etempvar; apply PTree.gss.
      * destruct bit; reflexivity.
      * exact Hbranch.
Qed.

Lemma exec_buffer8_read_halve e le m j :
  le!_i = Some (Vlong (Int64.repr j)) -> 0 <= j <= Int64.max_unsigned ->
  Clight2.exec_stmt ge0 e le m buffer8_read_update E0 (PTree.set _i (Vlong (Int64.repr (j / 2))) le) m Out_normal.
Proof.
  intros HI HJ. unfold buffer8_read_update. rewrite buffer8_read_loop_shape. apply exec_set.
  eapply eval_Ebinop with (v1 := Vlong (Int64.repr j)) (v2 := Vint (Int.repr 2)).
  - apply eval_Etempvar; exact HI.
  - apply eval_Econst_int.
  - change (Some (Vlong (Int64.divu (Int64.repr j) (Int64.repr 2))) = Some (Vlong (Int64.repr (j / 2)))).
    unfold Int64.divu. rewrite Int64.unsigned_repr by exact HJ. reflexivity.
Qed.
Lemma exec_buffer8_read_stop e le m : le!_i = Some (Vlong Int64.zero) ->
  Clight2.exec_stmt ge0 e le m buffer8_read_loop E0 le m Out_normal.
Proof.
  intros HI. rewrite buffer8_read_loop_shape.
  eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
  apply exec_Sseq_2; [|discriminate].
  eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
  - exact (eval_buffer8_guard e le m 0 ltac:(change (0 <= 0 <= 18446744073709551615); lia) HI).
  - reflexivity.
  - apply exec_Sbreak.
Qed.
