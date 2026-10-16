(** A real non-push opcode arm: reload the code, then execute its nibble switch.
    The code value is obtained from memory, not supplied as an execution premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_null_data_loads C.jet_elements_null_data_cases.
Require Import C.jet_output_layout C.jet_elements_effects.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j code : Prop :=
  0 <= ebase /\ ebase + 8 <= Ptrofs.max_unsigned /\
  0 <= txbase /\ txbase + 16 <= Ptrofs.max_unsigned /\
  0 <= outbase /\ outbase + 248 * Int64.unsigned i + 232 <= Ptrofs.max_unsigned /\
  0 <= opbase /\ opbase + 36 * Int64.unsigned j + 36 <= Ptrofs.max_unsigned /\
  elements_null_data_path_loads m be ebase bt txbase bout outbase bop opbase i j code.

Theorem exec_elements_null_data_reload_small n e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j :
  (n < 16)%nat -> e!_writeBit = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j (Int.repr (Z.of_nat n + 6)) ->
  write_frame_at m bd dbase bw edge cur 4 ->
  exists mf,
    Clight2.exec_stmt elements_ge e le m
      (elements_append_stmt (elements_null_data_reload _t'28 _t'29 _t'30 _t'31)
        (Sswitch (fst elements_null_data_small_switch) (snd elements_null_data_small_switch))) E0
      (elements_null_data_reload_temps _t'28 _t'29 _t'30 _t'31
        bt txbase bout outbase bop opbase (Int.repr (Z.of_nat n + 6)) le) mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 4 (@encode (Word 2) (@fromZ (WordToZ 2) (Z.of_nat n))).
Proof.
  intros Hn Hnone HD Henv Hi Hj
    (He0 & HeM & Ht0 & HtM & Ho0 & HoM & Hp0 & HpM & L1 & L2 & L3 & L4) HF.
  set (next := elements_null_data_reload_temps _t'28 _t'29 _t'30 _t'31
    bt txbase bout outbase bop opbase (Int.repr (Z.of_nat n + 6)) le).
  assert (Hreload : Clight2.exec_stmt elements_ge e le m
    (elements_null_data_reload _t'28 _t'29 _t'30 _t'31) E0 next m Out_normal).
  { unfold next. eapply exec_elements_null_data_reload; eauto.
    intros t Ht. simpl in Ht. repeat destruct Ht as [Ht|Ht]; subst;
      try contradiction; vm_compute; intuition discriminate. }
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold next. rewrite elements_null_data_reload_temps_other; [exact HD|].
    vm_compute; intuition discriminate. }
  assert (Hcode : next!_t'31 = Some (Vint (Int.repr (Z.of_nat n + 6)))).
  { unfold next, elements_null_data_reload_temps. apply PTree.gss. }
  destruct (exec_elements_null_data_small_switch n e next m bd dbase bw edge cur Hn Hnone HD' Hcode HF)
    as (mf & HC & HE).
  exists mf. split; [|exact HE].
  change E0 with (E0 ** E0). eapply exec_elements_append_stmt; [exact Hreload|exact HC].
Qed.

Definition elements_stmt_first (a b : option statement) : option statement :=
  match a with Some s => Some s | None => b end.

Fixpoint elements_find_set_prefix (id : ident) (s : statement) : option statement :=
  match s with
  | Ssequence a b =>
      match a with
      | Sset id' _ => if Pos.eqb id id' then Some s else
          elements_stmt_first (elements_find_set_prefix id a) (elements_find_set_prefix id b)
      | _ => elements_stmt_first (elements_find_set_prefix id a) (elements_find_set_prefix id b)
      end
  | Sifthenelse _ a b => elements_stmt_first (elements_find_set_prefix id a) (elements_find_set_prefix id b)
  | Sloop a b => elements_stmt_first (elements_find_set_prefix id a) (elements_find_set_prefix id b)
  | _ => None
  end.

Lemma elements_null_data_small_arm_source :
  elements_find_set_prefix _t'28 (fn_body f_simplicity_output_null_datum) =
    Some (elements_append_stmt (elements_null_data_reload _t'28 _t'29 _t'30 _t'31)
      (Sswitch (fst elements_null_data_small_switch) (snd elements_null_data_small_switch))).
Proof. reflexivity. Qed.

Theorem exec_elements_null_data_reload_push n e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j :
  (n < 4)%nat -> e!_writeBit = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j (Int.repr (Z.of_nat n)) ->
  write_frame_at m bd dbase bw edge cur 2 ->
  exists mf,
    Clight2.exec_stmt elements_ge e le m
      (elements_append_stmt (elements_null_data_reload _t'12 _t'13 _t'14 _t'15)
        (Sswitch (fst elements_null_data_push_switch) (snd elements_null_data_push_switch))) E0
      (elements_null_data_reload_temps _t'12 _t'13 _t'14 _t'15
        bt txbase bout outbase bop opbase (Int.repr (Z.of_nat n)) le) mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 2 (@encode (Word 1) (@fromZ (WordToZ 1) (Z.of_nat n))).
Proof.
  intros Hn Hnone HD Henv Hi Hj
    (He0 & HeM & Ht0 & HtM & Ho0 & HoM & Hp0 & HpM & L1 & L2 & L3 & L4) HF.
  set (next := elements_null_data_reload_temps _t'12 _t'13 _t'14 _t'15
    bt txbase bout outbase bop opbase (Int.repr (Z.of_nat n)) le).
  assert (Hreload : Clight2.exec_stmt elements_ge e le m
    (elements_null_data_reload _t'12 _t'13 _t'14 _t'15) E0 next m Out_normal).
  { unfold next. eapply exec_elements_null_data_reload; eauto.
    intros t Ht. simpl in Ht. repeat destruct Ht as [Ht|Ht]; subst;
      try contradiction; vm_compute; intuition discriminate. }
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold next. rewrite elements_null_data_reload_temps_other; [exact HD|].
    vm_compute; intuition discriminate. }
  assert (Hcode : next!_t'15 = Some (Vint (Int.repr (Z.of_nat n)))).
  { unfold next, elements_null_data_reload_temps. apply PTree.gss. }
  destruct (exec_elements_null_data_push_switch n e next m bd dbase bw edge cur Hn Hnone HD' Hcode HF)
    as (mf & HC & HE).
  exists mf. split; [|exact HE].
  change E0 with (E0 ** E0). eapply exec_elements_append_stmt; [exact Hreload|exact HC].
Qed.

Lemma elements_null_data_push_arm_source :
  elements_find_set_prefix _t'12 (fn_body f_simplicity_output_null_datum) =
    Some (elements_append_stmt (elements_null_data_reload _t'12 _t'13 _t'14 _t'15)
      (Sswitch (fst elements_null_data_push_switch) (snd elements_null_data_push_switch))).
Proof. reflexivity. Qed.
