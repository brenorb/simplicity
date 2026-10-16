(** Actual writeBit call with a computed signed-int boolean expression. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Events.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_call C.jet_elements_transport.
Require Import C.jet_elements_steps C.jet_output_layout C.jet_elements_effects.
Require C.jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition elements_bit_expr_stmt (ret : option ident) (a : expr) : statement :=
  Scall ret
    (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); a].

Lemma exec_elements_bit_expr (bit : bool) ret a e le m bd dbase bw edge cur :
  typeof a = tint -> e!_writeBit = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  eval_expr elements_ge e le m a (Vint (if bit then Int.one else Int.zero)) ->
  write_frame_at m bd dbase bw edge cur 1 ->
  exists mf, Clight2.exec_stmt elements_ge e le m (elements_bit_expr_stmt ret a) E0
    (set_opttemp ret (Vint (if bit then Int.one else Int.zero)) le) mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 1 [Some bit].
Proof.
  intros HT Hnone HD HA HF.
  destruct (elements_writeBit_step m bd dbase bw edge cur bit HF) as (mf & HC & HE).
  exists mf. split; [|exact HE]. unfold elements_bit_expr_stmt.
  eapply exec_elements_helper_call with (f := jets.f_writeBit)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vint (if bit then Int.one else Int.zero)])
    (vres := Vint (if bit then Int.one else Int.zero)).
  - unfold elements_core_helpers; simpl; tauto.
  - exact Hnone.
  - eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs with (v1 := Vint (if bit then Int.one else Int.zero));
      [exact HA|unfold sem_cast; rewrite HT; destruct bit; reflexivity|apply eval_Enil].
  - reflexivity.
  - exact HC.
Qed.

Definition elements_skip_expr_stmt (a : expr) : statement :=
  Scall None
    (Evar _skipBits (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); a].

Lemma exec_elements_skip_expr n a e le m bd dbase bw edge cur :
  0 <= n <= Int.max_signed -> typeof a = tint -> e!_skipBits = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  eval_expr elements_ge e le m a (Vint (Int.repr n)) ->
  write_frame_at m bd dbase bw edge cur n ->
  exists mf, Clight2.exec_stmt elements_ge e le m (elements_skip_expr_stmt a) E0 le mf Out_normal /\
    write_effect m mf bd dbase bw edge cur n (repeat None (Z.to_nat n)).
Proof.
  intros Hn HT Hnone HD HA HF.
  assert (Hnat : Z.of_nat (Z.to_nat n) = n) by (apply Z2Nat.id; lia).
  destruct (elements_skipBits_step m bd dbase bw edge cur (Z.to_nat n) ltac:(rewrite Hnat; exact HF))
    as (mf & HC & HE). rewrite Hnat in HC, HE.
  exists mf. split; [|exact HE]. unfold elements_skip_expr_stmt.
  change le with (set_opttemp None Vundef le) at 2.
  eapply exec_elements_helper_call with (f := jets.f_skipBits)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr n)]) (vres := Vundef).
  - unfold elements_core_helpers; simpl; tauto.
  - exact Hnone.
  - eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs with (v1 := Vint (Int.repr n)); [exact HA| |apply eval_Enil].
    unfold sem_cast. rewrite HT.
    change (Some (Vlong (Int64.repr (Int.signed (Int.repr n)))) = Some (Vlong (Int64.repr n))).
    rewrite Int.signed_repr; [reflexivity|].
    change (-2147483648 <= n <= 2147483647). change (0 <= n <= 2147483647) in Hn. lia.
  - reflexivity.
  - exact HC.
Qed.
