(** The actual opcode switches in output_null_datum, not a replacement body. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_const_bits.
Require Import C.jet_output_layout C.jet_elements_effects.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Fixpoint elements_statement_switches (s : statement) : list (expr * labeled_statements) :=
  match s with
  | Ssequence a b => elements_statement_switches a ++ elements_statement_switches b
  | Sifthenelse _ a b => elements_statement_switches a ++ elements_statement_switches b
  | Sloop a b => elements_statement_switches a ++ elements_statement_switches b
  | Sswitch a cases => [(a, cases)]
  | _ => []
  end.

Definition elements_null_data_small_switch :=
  nth 0 (elements_statement_switches (fn_body f_simplicity_output_null_datum))
    (Econst_int Int.zero tint, LSnil).

Definition elements_nibble_bits (n : nat) : list bool :=
  map (Z.testbit (Z.of_nat n)) [3; 2; 1; 0].

Lemma elements_null_data_small_switch_expr :
  fst elements_null_data_small_switch = Etempvar _t'31 tint.
Proof. reflexivity. Qed.

Lemma elements_null_data_small_selected n : (n < 16)%nat ->
  exists tail,
    seq_of_labeled_statement (select_switch (Z.of_nat n + 6) (snd elements_null_data_small_switch)) =
    Ssequence (elements_const_bits (elements_nibble_bits n)) tail.
Proof.
  intros Hn. do 16 (destruct n as [|n]; [eexists; reflexivity|]). lia.
Qed.

Definition elements_null_data_push_switch :=
  nth 1 (elements_statement_switches (fn_body f_simplicity_output_null_datum))
    (Econst_int Int.zero tint, LSnil).

Definition elements_push_kind_bits (n : nat) : list bool :=
  map (Z.testbit (Z.of_nat n)) [1; 0].

Lemma elements_null_data_push_switch_expr :
  fst elements_null_data_push_switch = Etempvar _t'15 tint.
Proof. reflexivity. Qed.

Lemma elements_null_data_push_selected n : (n < 4)%nat ->
  exists tail,
    seq_of_labeled_statement (select_switch (Z.of_nat n) (snd elements_null_data_push_switch)) =
    Ssequence (elements_const_bits (elements_push_kind_bits n)) tail.
Proof.
  intros Hn. do 4 (destruct n as [|n]; [eexists; reflexivity|]). lia.
Qed.

Lemma elements_push_kind_cells n : (n < 4)%nat ->
  map (@Some bool) (elements_push_kind_bits n) = @encode (Word 1) (@fromZ (WordToZ 1) (Z.of_nat n)).
Proof.
  intros Hn. do 4 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Theorem exec_elements_null_data_push_switch n e le m bd dbase bw edge cur :
  (n < 4)%nat -> e!_writeBit = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_t'15 = Some (Vint (Int.repr (Z.of_nat n))) ->
  write_frame_at m bd dbase bw edge cur 2 ->
  exists mf,
    Clight2.exec_stmt elements_ge e le m
      (Sswitch (fst elements_null_data_push_switch) (snd elements_null_data_push_switch))
      E0 le mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 2 (@encode (Word 1) (@fromZ (WordToZ 1) (Z.of_nat n))).
Proof.
  intros Hn He HD Hcode HF.
  destruct (exec_elements_const_bits (elements_push_kind_bits n) ltac:(discriminate)
    e le m bd dbase bw edge cur He HD HF) as (mf & HC & HE).
  destruct (elements_null_data_push_selected n Hn) as (tail & Htail).
  exists mf. split.
  - change Out_normal with (outcome_switch Out_break).
    eapply exec_Sswitch with (v := Vint (Int.repr (Z.of_nat n))) (n := Z.of_nat n).
    + rewrite elements_null_data_push_switch_expr. apply eval_Etempvar; exact Hcode.
    + rewrite elements_null_data_push_switch_expr.
      change (Some (Int.unsigned (Int.repr (Z.of_nat n))) = Some (Z.of_nat n)).
      rewrite Int.unsigned_repr; [reflexivity|].
      change (0 <= Z.of_nat n <= 4294967295). lia.
    + rewrite Htail. eapply exec_Sseq_2; [exact HC|discriminate].
  - change (write_effect m mf bd dbase bw edge cur 2 (map (@Some bool) (elements_push_kind_bits n))) in HE.
    rewrite (elements_push_kind_cells n Hn) in HE. exact HE.
Qed.

Lemma elements_nibble_cells n : (n < 16)%nat ->
  map (@Some bool) (elements_nibble_bits n) = @encode (Word 2) (@fromZ (WordToZ 2) (Z.of_nat n)).
Proof.
  intros Hn. do 16 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

Theorem exec_elements_null_data_small_switch n e le m bd dbase bw edge cur :
  (n < 16)%nat -> e!_writeBit = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_t'31 = Some (Vint (Int.repr (Z.of_nat n + 6))) ->
  write_frame_at m bd dbase bw edge cur 4 ->
  exists mf,
    Clight2.exec_stmt elements_ge e le m
      (Sswitch (fst elements_null_data_small_switch) (snd elements_null_data_small_switch))
      E0 le mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 4 (@encode (Word 2) (@fromZ (WordToZ 2) (Z.of_nat n))).
Proof.
  intros Hn He HD Hcode HF.
  destruct (exec_elements_const_bits (elements_nibble_bits n) ltac:(discriminate)
    e le m bd dbase bw edge cur He HD HF) as (mf & HC & HE).
  destruct (elements_null_data_small_selected n Hn) as (tail & Htail).
  exists mf. split.
  - change Out_normal with (outcome_switch Out_break).
    eapply exec_Sswitch with (v := Vint (Int.repr (Z.of_nat n + 6))) (n := Z.of_nat n + 6).
    + rewrite elements_null_data_small_switch_expr. apply eval_Etempvar; exact Hcode.
    + rewrite elements_null_data_small_switch_expr.
      change (Some (Int.unsigned (Int.repr (Z.of_nat n + 6))) = Some (Z.of_nat n + 6)).
      rewrite Int.unsigned_repr; [reflexivity|].
      change (0 <= Z.of_nat n + 6 <= 4294967295). lia.
    + rewrite Htail. eapply exec_Sseq_2; [exact HC|discriminate].
  - change (write_effect m mf bd dbase bw edge cur 4 (map (@Some bool) (elements_nibble_bits n))) in HE.
    rewrite (elements_nibble_cells n Hn) in HE. exact HE.
Qed.
