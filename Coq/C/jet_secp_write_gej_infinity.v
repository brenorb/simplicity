(** The real original point writer, including entry and all three actual calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight ClightBigstep Integers Values Memory Events Maps.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_public_body C.jet_exec.
Require Import C.jet_secp_public_copy.
Require Import C.jet_secp_gej_infinity_layout C.jet_secp_point_three_writes C.jet_secp_literal_infinity.
Require Import C.jet_secp_fe_nv C.jet_secp_frame C.jet_sx_exec C.jet_sx_mem C.jet_frame_inv C.jet_output_layout.
Require Simplicity.Alg Simplicity.Translate.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition write_gej_field_stmt fid : statement :=
  Scall None (Evar _write_fe (Tfunction
    (Tcons (tptr (Tstruct _frameItem noattr))
      (Tcons (tptr (Tstruct __5467 noattr)) Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr));
     Eaddrof (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
       (Tstruct __6123 noattr)) fid (Tstruct __5467 noattr))
       (tptr (Tstruct __5467 noattr))].
Lemma write_gej_body : fn_body f_write_gej =
  Ssequence (write_gej_field_stmt _x)
    (Ssequence (write_gej_field_stmt _y) (write_gej_field_stmt _z)).
Proof. reflexivity. Qed.

Lemma exec_write_gej_field le m mf b bd dbase fid delta :
  In (fid,delta) [(_x,0);(_y,40);(_z,80)] ->
  le!_r = Some (Vptr b (Ptrofs.repr 0)) ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_write_fe)
    [Vptr bd (Ptrofs.repr dbase); Vptr b (Ptrofs.repr delta)] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge empty_env le m (write_gej_field_stmt fid) E0 le mf Out_normal.
Proof.
  intros HF HR HD HC.
  destruct secp_public_helper_symbols as (HRS & HRF & HWS & HWF).
  unfold write_gej_field_stmt.
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block _write_fe) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr b (Ptrofs.repr delta)])
    (f := Internal f_write_fe) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HWS].
    + apply deref_loc_reference;reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar;exact HD.
    + reflexivity.
    + eapply eval_Econs.
      * exact (eval_gej_infinity_field_address le m b 0 fid delta HF
          ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia) HR).
      * reflexivity.
      * apply eval_Enil.
  - exact HWF.
  - reflexivity.
  - exact HC.
Qed.

Definition write_gej_env b bd dbase : temp_env :=
  PTree.set _r (Vptr b (Ptrofs.repr 0))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase)) (create_undef_temps (fn_temps f_write_gej))).
Lemma write_gej_entry m b bd dbase :
  function_entry2 secp_ge f_write_gej
    [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 0)] m empty_env (write_gej_env b bd dbase) m.
Proof.
  constructor.
  - constructor.
  - repeat constructor;simpl;intuition discriminate.
  - intros x y HX HY HE;cbn in HX,HY;contradiction.
  - constructor.
  - reflexivity.
Qed.

Lemma eval_write_gej_from_calls m mx my mf b bd dbase :
  Clight2.eval_funcall secp_ge m (Internal f_write_fe)
    [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 0)] E0 mx Vundef ->
  Clight2.eval_funcall secp_ge mx (Internal f_write_fe)
    [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 40)] E0 my Vundef ->
  Clight2.eval_funcall secp_ge my (Internal f_write_fe)
    [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 80)] E0 mf Vundef ->
  Clight2.eval_funcall secp_ge m (Internal f_write_gej)
    [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 0)] E0 mf Vundef.
Proof.
  intros HX HY HZ.
  assert (HR : (write_gej_env b bd dbase)!_r = Some (Vptr b (Ptrofs.repr 0)))
    by (unfold write_gej_env;apply PTree.gss).
  assert (HD : (write_gej_env b bd dbase)!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold write_gej_env;rewrite PTree.gso by discriminate;apply PTree.gss. }
  eapply eval_funcall_internal with (e := empty_env) (le1 := write_gej_env b bd dbase)
    (le2 := write_gej_env b bd dbase) (m1 := m) (m2 := mf) (out := Out_normal).
  - apply write_gej_entry.
  - rewrite write_gej_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mx) (le1 := write_gej_env b bd dbase).
    + eapply exec_write_gej_field;[left;reflexivity|exact HR|exact HD|exact HX].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := my) (le1 := write_gej_env b bd dbase).
      * eapply exec_write_gej_field;[right;left;reflexivity|exact HR|exact HD|exact HY].
      * eapply exec_write_gej_field;[right;right;left;reflexivity|exact HR|exact HD|exact HZ].
  - reflexivity.
  - reflexivity.
Qed.

Theorem eval_write_gej_infinity_literal m0 bd dbase bw edge cursor N bi (rc : Z) m b :
  write_frame_at m0 bd dbase bw edge cursor N -> 768 <= N ->
  finv m0 bd dbase bw edge cursor N bi m false [] ->
  fe_at m b 0 (repeat Int64.zero 5) -> fe_at m b 40 (repeat Int64.zero 5) ->
  fe_at m b 80 (repeat Int64.zero 5) -> Mem.range_perm m b 0 128 Cur Freeable ->
  xsep (extA m0 bd bw bi) [(b,0)] ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_gej)
      [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 0)] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_gej_infinity Simplicity.Alg.CoreFunSem tt)) /\
    Mem.range_perm mf b 0 128 Cur Freeable /\
    lframe (fun bx _ => bx <> b /\ ~ extA m0 bd bw bi bx) m mf.
Proof.
  intros HO HN HI HX HY HZ HP HS.
  destruct (eval_point_three_zero_writes m0 bd dbase bw edge cursor N bi rc m b
    HO HN HI HX HY HZ HP HS) as (mx & my & mf & HCX & HCY & HCZ & HFin & HFree & HFrame).
  exists mf; split;[eapply eval_write_gej_from_calls;eassumption|].
  split;[exact HFin|]. split;assumption.
Qed.
Print Assumptions eval_write_gej_infinity_literal.
