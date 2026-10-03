(** Execution of the constant-pad writers of the core padding jets:
    [simplicity_writeN(dst, c)] / [writeBit(dst, true)] as write effects. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_wide C.jet_wide_spec C.jet_spec C.jet_bitcoin_effects.
Require Import C.jet_core_wrapper C.jet_core_steps.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque ge0.
Set Default Timeout 60.

Lemma exec_pad_writer e le m m' id f tya cc tres argexpr (v argv : val) bd dbase vres :
  e!id = None ->
  Genv.find_symbol (Clight.genv_genv ge0) id = Some (jet_symbol_block id) ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr (jet_symbol_block id) Ptrofs.zero) = Some (Internal f) ->
  type_of_fundef (Internal f) =
    Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tya Tnil)) tres cc ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  eval_expr ge0 e le m argexpr v -> sem_cast v (typeof argexpr) tya m = Some argv ->
  Clight2.eval_funcall ge0 m (Internal f) [Vptr bd (Ptrofs.repr dbase); argv] E0 m' vres ->
  Clight2.exec_stmt ge0 e le m
    (Scall None (Evar id (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tya Tnil)) tres cc))
      [Etempvar _dst (tptr (Tstruct _frameItem noattr)); argexpr]) E0 le m' Out_normal.
Proof.
  intros He Hs Hf Hty Hdst Harg Hcast Hcall.
  assert (Hexec : Clight2.exec_stmt ge0 e le m
    (Scall None (Evar id (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tya Tnil)) tres cc))
      [Etempvar _dst (tptr (Tstruct _frameItem noattr)); argexpr]) E0 (set_opttemp None vres le) m' Out_normal).
  { eapply exec_Scall with (vf := Vptr (jet_symbol_block id) Ptrofs.zero) (f := Internal f)
      (vargs := [Vptr bd (Ptrofs.repr dbase); argv]) (vres := vres).
    - reflexivity.
    - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact Hs]|apply deref_loc_reference; reflexivity].
    - eapply eval_Econs with (v1 := Vptr bd (Ptrofs.repr dbase)).
      + apply eval_Etempvar; exact Hdst.
      + reflexivity.
      + eapply eval_Econs with (v1 := v); [exact Harg|exact Hcast|apply eval_Enil].
    - exact Hf.
    - exact Hty.
    - exact Hcall. }
  exact Hexec.
Qed.

Definition pad_writer_ok (e : env) : Prop := True.

Definition pad8_0_stmt : statement :=
  Scall None (Evar _simplicity_write8 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tuchar Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 0) tint].

Lemma pad8_0_cells :
  encode (decode_word8 (Int64.repr (Int.unsigned (Cop.cast_int_int I8 Unsigned (Int.repr 0))))) =
    repeat (Some Datatypes.false) 8.
Proof. vm_compute. reflexivity. Qed.

Lemma pad8_0_step e le m bd dbase bw edge cur :
  e!_simplicity_write8 = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m bd dbase bw edge cur 8 ->
  exists m', Clight2.exec_stmt ge0 e le m pad8_0_stmt E0 le m' Out_normal /\
    write_effect m m' bd dbase bw edge cur 8 (repeat (Some Datatypes.false) 8).
Proof.
  intros He Hdst HF.
  destruct (core_write8_step m bd dbase bw edge cur (Cop.cast_int_int I8 Unsigned (Int.repr 0)) HF)
    as (m' & Hcall & Heff).
  exists m'. split.
  - eapply exec_pad_writer with (id := _simplicity_write8) (f := jets.f_simplicity_write8)
      (v := Vint (Int.repr 0)); try eassumption.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
    + reflexivity.
    + apply eval_Econst_int.
    + reflexivity.
  - rewrite <- pad8_0_cells. exact Heff.
Qed.

Definition pad8_255_stmt : statement :=
  Scall None (Evar _simplicity_write8 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tuchar Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 255) tint].

Lemma pad8_255_cells :
  encode (decode_word8 (Int64.repr (Int.unsigned (Cop.cast_int_int I8 Unsigned (Int.repr 255))))) =
    repeat (Some Datatypes.true) 8.
Proof. vm_compute. reflexivity. Qed.

Lemma pad8_255_step e le m bd dbase bw edge cur :
  e!_simplicity_write8 = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m bd dbase bw edge cur 8 ->
  exists m', Clight2.exec_stmt ge0 e le m pad8_255_stmt E0 le m' Out_normal /\
    write_effect m m' bd dbase bw edge cur 8 (repeat (Some Datatypes.true) 8).
Proof.
  intros He Hdst HF.
  destruct (core_write8_step m bd dbase bw edge cur (Cop.cast_int_int I8 Unsigned (Int.repr 255)) HF)
    as (m' & Hcall & Heff).
  exists m'. split.
  - eapply exec_pad_writer with (id := _simplicity_write8) (f := jets.f_simplicity_write8)
      (v := Vint (Int.repr 255)); try eassumption.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
    + reflexivity.
    + apply eval_Econst_int.
    + reflexivity.
  - rewrite <- pad8_255_cells. exact Heff.
Qed.

Definition pad16_0_stmt : statement :=
  Scall None (Evar _simplicity_write16 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 0) tint].

Lemma pad16_0_cells :
  encode (decode_wide W16 (Int64.zero_ext (wide_bits W16) (Int64.repr 0))) = repeat (Some Datatypes.false) 16.
Proof. vm_compute. reflexivity. Qed.

Lemma pad16_0_step e le m bd dbase bw edge cur :
  e!_simplicity_write16 = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m bd dbase bw edge cur 16 ->
  exists m', Clight2.exec_stmt ge0 e le m pad16_0_stmt E0 le m' Out_normal /\
    write_effect m m' bd dbase bw edge cur 16 (repeat (Some Datatypes.false) 16).
Proof.
  intros He Hdst HF.
  destruct (core_write_wide_step W16 m bd dbase bw edge cur (Int64.repr 0) HF) as (m' & Hcall & Heff).
  exists m'. split.
  - eapply exec_pad_writer with (id := _simplicity_write16) (f := jets.f_simplicity_write16)
      (v := Vint (Int.repr 0)); try eassumption.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
    + reflexivity.
    + apply eval_Econst_int.
    + simpl. unfold sem_cast. simpl. reflexivity.
  - rewrite <- pad16_0_cells. exact Heff.
Qed.

Definition pad16_max_stmt : statement :=
  Scall None (Evar _simplicity_write16 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 65535) tint].

Lemma pad16_max_cells :
  encode (decode_wide W16 (Int64.zero_ext (wide_bits W16) (Int64.repr 65535))) = repeat (Some Datatypes.true) 16.
Proof. vm_compute. reflexivity. Qed.

Lemma pad16_max_step e le m bd dbase bw edge cur :
  e!_simplicity_write16 = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m bd dbase bw edge cur 16 ->
  exists m', Clight2.exec_stmt ge0 e le m pad16_max_stmt E0 le m' Out_normal /\
    write_effect m m' bd dbase bw edge cur 16 (repeat (Some Datatypes.true) 16).
Proof.
  intros He Hdst HF.
  destruct (core_write_wide_step W16 m bd dbase bw edge cur (Int64.repr 65535) HF) as (m' & Hcall & Heff).
  exists m'. split.
  - eapply exec_pad_writer with (id := _simplicity_write16) (f := jets.f_simplicity_write16)
      (v := Vint (Int.repr 65535)); try eassumption.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
    + reflexivity.
    + apply eval_Econst_int.
    + simpl. unfold sem_cast. simpl. reflexivity.
  - rewrite <- pad16_max_cells. exact Heff.
Qed.

Definition pad32_0_stmt : statement :=
  Scall None (Evar _simplicity_write32 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 0) tint].

Lemma pad32_0_cells :
  encode (decode_wide W32 (Int64.zero_ext (wide_bits W32) (Int64.repr 0))) = repeat (Some Datatypes.false) 32.
Proof. vm_compute. reflexivity. Qed.

Lemma pad32_0_step e le m bd dbase bw edge cur :
  e!_simplicity_write32 = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m bd dbase bw edge cur 32 ->
  exists m', Clight2.exec_stmt ge0 e le m pad32_0_stmt E0 le m' Out_normal /\
    write_effect m m' bd dbase bw edge cur 32 (repeat (Some Datatypes.false) 32).
Proof.
  intros He Hdst HF.
  destruct (core_write_wide_step W32 m bd dbase bw edge cur (Int64.repr 0) HF) as (m' & Hcall & Heff).
  exists m'. split.
  - eapply exec_pad_writer with (id := _simplicity_write32) (f := jets.f_simplicity_write32)
      (v := Vint (Int.repr 0)); try eassumption.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
    + reflexivity.
    + apply eval_Econst_int.
    + simpl. unfold sem_cast. simpl. reflexivity.
  - rewrite <- pad32_0_cells. exact Heff.
Qed.

Definition pad32_max_stmt : statement :=
  Scall None (Evar _simplicity_write32 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr (-1)) tuint].

Lemma pad32_max_cells :
  encode (decode_wide W32 (Int64.zero_ext (wide_bits W32) (Int64.repr 4294967295))) = repeat (Some Datatypes.true) 32.
Proof. vm_compute. reflexivity. Qed.

Lemma pad32_max_step e le m bd dbase bw edge cur :
  e!_simplicity_write32 = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m bd dbase bw edge cur 32 ->
  exists m', Clight2.exec_stmt ge0 e le m pad32_max_stmt E0 le m' Out_normal /\
    write_effect m m' bd dbase bw edge cur 32 (repeat (Some Datatypes.true) 32).
Proof.
  intros He Hdst HF.
  destruct (core_write_wide_step W32 m bd dbase bw edge cur (Int64.repr 4294967295) HF) as (m' & Hcall & Heff).
  exists m'. split.
  - eapply exec_pad_writer with (id := _simplicity_write32) (f := jets.f_simplicity_write32)
      (v := Vint (Int.repr (-1))); try eassumption.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
    + reflexivity.
    + apply eval_Econst_int.
    + simpl. unfold sem_cast. simpl. reflexivity.
  - rewrite <- pad32_max_cells. exact Heff.
Qed.

Definition padbit_true_stmt : statement :=
  Scall None (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 1) tint].

Lemma padbit_true_step e le m bd dbase bw edge cur :
  e!_writeBit = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m bd dbase bw edge cur 1 ->
  exists m', Clight2.exec_stmt ge0 e le m padbit_true_stmt E0 le m' Out_normal /\
    write_effect m m' bd dbase bw edge cur 1 [Some Datatypes.true].
Proof.
  intros He Hdst HF.
  destruct (core_writeBit_step m bd dbase bw edge cur Datatypes.true HF) as (m' & Hcall & Heff).
  exists m'. split.
  - eapply exec_pad_writer with (id := _writeBit) (f := jets.f_writeBit) (v := Vint (Int.repr 1)); try eassumption.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
    + reflexivity.
    + apply eval_Econst_int.
    + simpl. unfold sem_cast. simpl. reflexivity.
  - exact Heff.
Qed.
