(** Constant writeBit sequences, retaining the complete frame effect. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.BitMachine Simplicity.Translate.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_transport C.jet_elements_call.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_elements_effects C.jet_elements_steps.
Require Import C.jet_output_layout C.jet_output_layout_step.
Require C.jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition elements_const_bit (bit : bool) : statement :=
  Scall None
    (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (if bit then Int.one else Int.zero) tint].

Fixpoint elements_const_bits (bits : list bool) : statement :=
  match bits with
  | [] => Sbreak
  | bit :: rest => Ssequence (elements_const_bit bit) (elements_const_bits rest)
  end.

Lemma exec_elements_const_bit e le m bd dbase bw edge cur bit :
  e!_writeBit = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m bd dbase bw edge cur 1 ->
  exists mf, Clight2.exec_stmt elements_ge e le m (elements_const_bit bit) E0 le mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 1 [Some bit].
Proof.
  intros He HD HF.
  destruct (elements_writeBit_step m bd dbase bw edge cur bit HF) as (mf & HC & HE).
  exists mf. split; [|exact HE]. unfold elements_const_bit.
  change le with (set_opttemp None (Vint (if bit then Int.one else Int.zero)) le) at 2.
  eapply exec_elements_helper_call with (f := jets.f_writeBit)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vint (if bit then Int.one else Int.zero)])
    (vres := Vint (if bit then Int.one else Int.zero)).
  - unfold elements_core_helpers; simpl; tauto.
  - exact He.
  - eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs; [apply eval_Econst_int| |apply eval_Enil].
    destruct bit; reflexivity.
  - reflexivity.
  - exact HC.
Qed.

Theorem exec_elements_const_bits bits : bits <> [] ->
  forall e le m bd dbase bw edge cur,
  e!_writeBit = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m bd dbase bw edge cur (Z.of_nat (length bits)) ->
  exists mf, Clight2.exec_stmt elements_ge e le m (elements_const_bits bits) E0 le mf Out_break /\
    write_effect m mf bd dbase bw edge cur (Z.of_nat (length bits)) (map (@Some bool) bits).
Proof.
  induction bits as [|bit rest IH]; [intros H; contradiction|].
  intros _ e le m bd dbase bw edge cur He HD HF.
  assert (HF1 : write_frame_at m bd dbase bw edge cur 1).
  { eapply write_frame_at_shorter; [|exact HF]. cbn [length]. lia. }
  destruct (exec_elements_const_bit e le m bd dbase bw edge cur bit He HD HF1) as (m1 & HC1 & HE1).
  destruct rest as [|b rest].
  - exists m1. split; [|exact HE1].
    cbn [elements_const_bits].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HC1|apply exec_Sbreak].
  - assert (HF2 : write_frame_at m1 bd dbase bw edge (cur - 1) (Z.of_nat (length (b :: rest)))).
    { eapply write_frame_at_after_effect with (m := m) (cells := [Some bit]);
        [reflexivity|lia| |exact HE1].
      replace (1 + Z.of_nat (length (b :: rest))) with (Z.of_nat (length (bit :: b :: rest))) by (cbn [length]; lia).
      exact HF. }
    destruct (IH ltac:(discriminate) e le m1 bd dbase bw edge (cur - 1) He HD HF2) as (mf & HC2 & HE2).
    exists mf. split.
    + change (elements_const_bits (bit :: b :: rest)) with
        (Ssequence (elements_const_bit bit) (elements_const_bits (b :: rest))).
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eassumption.
    + change (map (@Some bool) (bit :: b :: rest)) with ([Some bit] ++ map (@Some bool) (b :: rest)).
      replace (Z.of_nat (length (bit :: b :: rest))) with (1 + Z.of_nat (length (b :: rest))) in * by (cbn [length]; lia).
      eapply write_effect_seq; [reflexivity|lia|exact HF|exact HE1|exact HE2].
Qed.
