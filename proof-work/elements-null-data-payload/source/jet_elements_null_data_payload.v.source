(** Actual push-data selector plus hash payload of output_null_datum. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets_elements C.jet_elements_linkage C.jet_exec.
Require Import C.jet_elements_field_eval C.jet_elements_index_eval C.jet_elements_null_data_loads.
Require Import C.jet_elements_null_data_small C.jet_elements_null_data_cases.
Require Import C.jet_elements_hash_write C.jet_elements_hash_helpers C.jet_uint32_array_init.
Require Import C.jet_output_layout C.jet_output_layout_step C.jet_elements_effects.
Require Import C.jet_application_sep C.jet_elements_env_load.
Require Import Simplicity.Digest C.jet_elements_script_cmr_local.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition elements_null_data_pointer_reload (t1 t2 t3 : ident) : statement :=
  Ssequence
    (Sset t1 (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
      _tx (tptr (Tstruct _elementsTransaction noattr))))
    (Ssequence
      (Sset t2 (Efield (Ederef (Etempvar t1 (tptr (Tstruct _elementsTransaction noattr)))
        (Tstruct _elementsTransaction noattr)) _output (tptr (Tstruct _sigOutput noattr))))
      (Sset t3 (elements_output_ops_expr t2))).

Definition elements_null_data_pointer_temps t1 t2 t3 bt txbase bout outbase bop opbase le :=
  PTree.set t3 (Vptr bop (Ptrofs.repr opbase))
    (PTree.set t2 (Vptr bout (Ptrofs.repr outbase)) (PTree.set t1 (Vptr bt (Ptrofs.repr txbase)) le)).

Lemma elements_null_data_pointer_temps_other t1 t2 t3 bt txbase bout outbase bop opbase le k :
  ~ In k [t1; t2; t3] ->
  (elements_null_data_pointer_temps t1 t2 t3 bt txbase bout outbase bop opbase le)!k = le!k.
Proof.
  intros H. unfold elements_null_data_pointer_temps.
  repeat rewrite PTree.gso by (simpl in H; intuition congruence). reflexivity.
Qed.

Lemma exec_elements_null_data_pointer_reload e le m t1 t2 t3 be ebase bt txbase bout outbase bop opbase i :
  (forall t, In t [t1; t2; t3] -> t <> _i) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  0 <= txbase -> txbase + 16 <= Ptrofs.max_unsigned ->
  0 <= outbase -> outbase + 248 * Int64.unsigned i + 232 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr m bt (txbase + 8) = Some (Vptr bout (Ptrofs.repr outbase)) ->
  Mem.load Mptr m bout (outbase + 248 * Int64.unsigned i + 224) = Some (Vptr bop (Ptrofs.repr opbase)) ->
  Clight2.exec_stmt elements_ge e le m (elements_null_data_pointer_reload t1 t2 t3) E0
    (elements_null_data_pointer_temps t1 t2 t3 bt txbase bout outbase bop opbase le) m Out_normal.
Proof.
  intros Hsafe Henv Hi He0 HeM Ht0 HtM Ho0 HoM L1 L2 L3.
  pose proof (Hsafe t1 (or_introl eq_refl)) as H1i.
  pose proof (Hsafe t2 (or_intror (or_introl eq_refl))) as H2i.
  set (le1 := PTree.set t1 (Vptr bt (Ptrofs.repr txbase)) le).
  set (le2 := PTree.set t2 (Vptr bout (Ptrofs.repr outbase)) le1).
  unfold elements_null_data_pointer_reload, elements_null_data_pointer_temps. fold le1 le2.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le1).
  - apply exec_set. eapply eval_elements_field_value with (sid := _txEnv) (delta := 0) (chunk := Mptr).
    + reflexivity.
    + exact elements_txEnv_tx.
    + reflexivity.
    + apply eval_elements_deref_struct; exact Henv.
    + rewrite elements_ptr_add_repr by lia. replace (ebase + 0) with ebase by lia.
      apply elements_loadv_repr; [lia|exact L1].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le2).
    + apply exec_set. eapply eval_elements_field_value with (sid := _elementsTransaction) (delta := 8) (chunk := Mptr).
      * reflexivity.
      * exact elements_elementsTransaction_output.
      * reflexivity.
      * apply eval_elements_deref_struct. unfold le1; apply PTree.gss.
      * rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact L2].
    + apply exec_set. eapply eval_elements_output_ops with (base := outbase) (r := i);
        [unfold le2; apply PTree.gss| |exact Ho0|lia|exact L3].
      unfold le2, le1. rewrite !PTree.gso by congruence. exact Hi.
Qed.

Definition elements_null_data_hash_call : statement :=
  Scall None
    (Evar _writeHash (Tfunction (Tcons (tptr (Tstruct _frameItem noattr))
      (Tcons (tptr (Tstruct _sha256_midstate noattr)) Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr));
     Eaddrof (Efield (elements_indexed_deref _t'11 _j _opcode) _dataHash (Tstruct _sha256_midstate noattr))
       (tptr (Tstruct _sha256_midstate noattr))].

Lemma exec_elements_null_data_hash_call e le m bd dbase bw edge cur bop opbase j xs :
  e!_writeHash = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_t'11 = Some (Vptr bop (Ptrofs.repr opbase)) -> le!_j = Some (Vlong j) ->
  0 <= opbase -> opbase + 36 * Int64.unsigned j + 32 <= Ptrofs.max_unsigned ->
  length xs = 8%nat -> uint32_array_at m bop (opbase + 36 * Int64.unsigned j) xs ->
  out_sep bd dbase bw edge cur 256 bop (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32) ->
  write_frame_at m bd dbase bw edge cur 256 ->
  exists mf, Clight2.exec_stmt elements_ge e le m elements_null_data_hash_call E0 le mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 256 (hash_cells xs).
Proof.
  intros Hnone HD HO HJ H0 HM HL HA HS HF.
  pose proof (Int64.unsigned_range j) as HJrange.
  destruct (eval_elements_writeHash_layout m bop (opbase + 36 * Int64.unsigned j)
    bd dbase bw edge cur xs HL ltac:(lia) HM HS HA HF) as (mf & HC & HE).
  exists mf. split; [|exact HE]. unfold elements_null_data_hash_call.
  change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (elements_symbol_block _writeHash) Ptrofs.zero)
    (f := Internal f_writeHash)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bop (Ptrofs.repr (opbase + 36 * Int64.unsigned j))])
    (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact Hnone|exact elements_writeHash_symbol]|
      apply deref_loc_reference; reflexivity].
  - eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs with (v1 := Vptr bop (Ptrofs.repr (opbase + 36 * Int64.unsigned j)));
      [|reflexivity|apply eval_Enil].
    replace (opbase + 36 * Int64.unsigned j) with (opbase + 36 * Int64.unsigned j + 0) by lia.
    eapply eval_elements_elem_field_addr with (sz := 36) (fdelta := 0);
      [exact elements_sizeof_opcode|exact elements_opcode_dataHash|exact HO|exact HJ|exact H0|lia|lia|lia|lia].
  - exact elements_writeHash_funct.
  - reflexivity.
  - exact HC.
Qed.

Definition elements_null_data_hash_tail : statement :=
  elements_append_stmt (elements_null_data_pointer_reload _t'9 _t'10 _t'11) elements_null_data_hash_call.

Theorem exec_elements_null_data_hash_tail e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j code xs :
  e!_writeHash = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j code ->
  length xs = 8%nat -> uint32_array_at m bop (opbase + 36 * Int64.unsigned j) xs ->
  out_sep bd dbase bw edge cur 256 bop (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32) ->
  write_frame_at m bd dbase bw edge cur 256 ->
  exists mf, Clight2.exec_stmt elements_ge e le m elements_null_data_hash_tail E0
    (elements_null_data_pointer_temps _t'9 _t'10 _t'11 bt txbase bout outbase bop opbase le) mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 256 (hash_cells xs).
Proof.
  intros Hnone HD Henv Hi Hj
    (He0 & HeM & Ht0 & HtM & Ho0 & HoM & Hp0 & HpM & L1 & L2 & L3 & L4) HL HA HS HF.
  set (next := elements_null_data_pointer_temps _t'9 _t'10 _t'11 bt txbase bout outbase bop opbase le).
  assert (HR : Clight2.exec_stmt elements_ge e le m
    (elements_null_data_pointer_reload _t'9 _t'10 _t'11) E0 next m Out_normal).
  { unfold next. eapply exec_elements_null_data_pointer_reload; eauto.
    intros t HT. simpl in HT. repeat destruct HT as [HT|HT]; subst; try contradiction; discriminate. }
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold next. rewrite elements_null_data_pointer_temps_other; [exact HD|]. vm_compute; intuition discriminate. }
  assert (HJ' : next!_j = Some (Vlong j)).
  { unfold next. rewrite elements_null_data_pointer_temps_other; [exact Hj|]. vm_compute; intuition discriminate. }
  assert (HO : next!_t'11 = Some (Vptr bop (Ptrofs.repr opbase))).
  { unfold next, elements_null_data_pointer_temps. apply PTree.gss. }
  destruct (exec_elements_null_data_hash_call e next m bd dbase bw edge cur bop opbase j xs
    Hnone HD' HO HJ' Hp0 ltac:(lia) HL HA HS HF) as (mf & HC & HE).
  exists mf. split; [|exact HE]. unfold elements_null_data_hash_tail.
  change E0 with (E0 ** E0). eapply exec_elements_append_stmt; [exact HR|exact HC].
Qed.

Lemma elements_null_data_hash_tail_source :
  elements_find_set_prefix _t'9 (fn_body f_simplicity_output_null_datum) = Some elements_null_data_hash_tail.
Proof. reflexivity. Qed.

Definition elements_null_data_push_arm : statement :=
  Ssequence
    (elements_append_stmt (elements_null_data_reload _t'12 _t'13 _t'14 _t'15)
      (Sswitch (fst elements_null_data_push_switch) (snd elements_null_data_push_switch)))
    elements_null_data_hash_tail.

Theorem exec_elements_null_data_push_arm n e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j xs :
  (n < 4)%nat -> e!_writeBit = None -> e!_writeHash = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j (Int.repr (Z.of_nat n)) ->
  length xs = 8%nat -> uint32_array_at m bop (opbase + 36 * Int64.unsigned j) xs ->
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 258 b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j) ->
  out_sep bd dbase bw edge cur 258 bop (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32) ->
  write_frame_at m bd dbase bw edge cur 258 ->
  exists mf, Clight2.exec_stmt elements_ge e le m elements_null_data_push_arm E0
    (elements_null_data_pointer_temps _t'9 _t'10 _t'11 bt txbase bout outbase bop opbase
      (elements_null_data_reload_temps _t'12 _t'13 _t'14 _t'15
        bt txbase bout outbase bop opbase (Int.repr (Z.of_nat n)) le)) mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 258
      (@encode (Word 1) (@fromZ (WordToZ 1) (Z.of_nat n)) ++ hash_cells xs).
Proof.
  intros Hn Hwrite Hhash HD Henv Hi Hj HP HL HA HSP HSH HF.
  pose proof HF as (_ & _ & _ & HCUR & _).
  assert (HF2 : write_frame_at m bd dbase bw edge cur 2).
  { eapply write_frame_at_shorter with (count := 258); [lia|exact HF]. }
  destruct (exec_elements_null_data_reload_push n e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j Hn Hwrite HD Henv Hi Hj HP HF2) as (m1 & CS & ES).
  set (next := elements_null_data_reload_temps _t'12 _t'13 _t'14 _t'15
    bt txbase bout outbase bop opbase (Int.repr (Z.of_nat n)) le).
  assert (HLen : Z.of_nat (length (@encode (Word 1) (@fromZ (WordToZ 1) (Z.of_nat n)))) = 2).
  { rewrite encode_length. reflexivity. }
  assert (HF256 : write_frame_at m1 bd dbase bw edge (cur - 2) 256).
  { eapply write_frame_at_after_effect with (m := m)
      (cells := @encode (Word 1) (@fromZ (WordToZ 1) (Z.of_nat n)));
      [exact HLen|lia|exact HF|exact ES]. }
  assert (HSP2 : Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 2 b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j)).
  { eapply Forall_impl; [|exact HSP]. intros [[b lo] hi] HS.
    eapply out_sep_sub with (cursor := cur) (count := 258); [lia|lia|lia|lia|exact HS]. }
  assert (HP1 : elements_null_data_path_valid m1 be ebase bt txbase bout outbase bop opbase i j (Int.repr (Z.of_nat n))).
  { destruct HP as (He0 & HeM & Ht0 & HtM & Ho0 & HoM & Hp0 & HpM & LOADS).
    unfold elements_null_data_path_valid. do 8 (split; [assumption|]).
    eapply elements_null_data_path_loads_preserved with (n := 2) (cur := cur);
      [lia|lia|exact ES|exact HSP2|exact LOADS]. }
  assert (HA1 : uint32_array_at m1 bop (opbase + 36 * Int64.unsigned j) xs).
  { intros k x HX.
    assert (HK : (k < 8)%nat).
    { rewrite <- HL. apply nth_error_Some. rewrite HX. discriminate. }
    rewrite (write_effect_env_load m m1 bd dbase bw edge cur 2
      (@encode (Word 1) (@fromZ (WordToZ 1) (Z.of_nat n))) cur 258 bop
      (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32)
      Mint32 (opbase + 36 * Int64.unsigned j + 4 * Z.of_nat k))
      by (first [exact ES | exact HSH | change (size_chunk Mint32) with 4; lia | lia]).
    exact (HA k x HX). }
  assert (HSH256 : out_sep bd dbase bw edge (cur - 2) 256 bop
    (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32)).
  { eapply out_sep_sub with (cursor := cur) (count := 258); [lia|lia|lia|lia|exact HSH]. }
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold next. rewrite elements_null_data_reload_temps_other; [exact HD|]. vm_compute; intuition discriminate. }
  assert (Henv' : next!_env = Some (Vptr be (Ptrofs.repr ebase))).
  { unfold next. rewrite elements_null_data_reload_temps_other; [exact Henv|]. vm_compute; intuition discriminate. }
  assert (Hi' : next!_i = Some (Vlong i)).
  { unfold next. rewrite elements_null_data_reload_temps_other; [exact Hi|]. vm_compute; intuition discriminate. }
  assert (Hj' : next!_j = Some (Vlong j)).
  { unfold next. rewrite elements_null_data_reload_temps_other; [exact Hj|]. vm_compute; intuition discriminate. }
  destruct (exec_elements_null_data_hash_tail e next m1 bd dbase bw edge (cur - 2)
    be ebase bt txbase bout outbase bop opbase i j (Int.repr (Z.of_nat n)) xs
    Hhash HD' Henv' Hi' Hj' HP1 HL HA1 HSH256 HF256) as (mf & CH & EH).
  exists mf. split.
  - unfold elements_null_data_push_arm.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CS|exact CH].
  - change 258 with (2 + 256).
    eapply write_effect_seq; [exact HLen|lia|exact HF|exact ES|exact EH].
Qed.

Fixpoint elements_statement_head_set (s : statement) : option ident :=
  match s with Sset id _ => Some id | Ssequence a _ => elements_statement_head_set a | _ => None end.

Fixpoint elements_find_head_prefix (id : ident) (s : statement) : option statement :=
  match s with
  | Ssequence a b =>
      match elements_statement_head_set a with
      | Some id' => if Pos.eqb id id' then Some s else
          elements_stmt_first (elements_find_head_prefix id a) (elements_find_head_prefix id b)
      | None => elements_stmt_first (elements_find_head_prefix id a) (elements_find_head_prefix id b)
      end
  | Sifthenelse _ a b | Sloop a b =>
      elements_stmt_first (elements_find_head_prefix id a) (elements_find_head_prefix id b)
  | _ => None
  end.

Lemma elements_null_data_push_arm_source :
  elements_find_head_prefix _t'12 (fn_body f_simplicity_output_null_datum) = Some elements_null_data_push_arm.
Proof. reflexivity. Qed.

(** The payload's actual output cells are the Simplicity pair encoding.
    The outer option/sum tags still belong to the enclosing jet proof. *)
Corollary exec_elements_null_data_push_pair n e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j (h : hash256) :
  (n < 4)%nat -> e!_writeBit = None -> e!_writeHash = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j (Int.repr (Z.of_nat n)) ->
  uint32_array_at m bop (opbase + 36 * Int64.unsigned j) (hash256_reg h) ->
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 258 b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j) ->
  out_sep bd dbase bw edge cur 258 bop (opbase + 36 * Int64.unsigned j) (opbase + 36 * Int64.unsigned j + 32) ->
  write_frame_at m bd dbase bw edge cur 258 ->
  exists mf, Clight2.exec_stmt elements_ge e le m elements_null_data_push_arm E0
    (elements_null_data_pointer_temps _t'9 _t'10 _t'11 bt txbase bout outbase bop opbase
      (elements_null_data_reload_temps _t'12 _t'13 _t'14 _t'15
        bt txbase bout outbase bop opbase (Int.repr (Z.of_nat n)) le)) mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 258
      (@encode (Ty.Prod (Word 1) (Word 8))
        (@fromZ (WordToZ 1) (Z.of_nat n), from_hash256 h)).
Proof.
  intros Hn HW HH HD HE HI HJ HP HA HS HSHash HF.
  destruct (exec_elements_null_data_push_arm n e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j (hash256_reg h)
    Hn HW HH HD HE HI HJ HP (hash256_len h) HA HS HSHash HF) as (mf & HC & EFF).
  exists mf. split; [exact HC|].
  change (@encode (Ty.Prod (Word 1) (Word 8))
    (@fromZ (WordToZ 1) (Z.of_nat n), from_hash256 h)) with
    (@encode (Word 1) (@fromZ (WordToZ 1) (Z.of_nat n)) ++ @encode (Word 8) (from_hash256 h)).
  rewrite encode_from_hash256. exact EFF.
Qed.
