(** Actual reserved/negative-one output suffix, including padding and memory reloads. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Events.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_transport C.jet_elements_call.
Require Import C.jet_elements_steps C.jet_elements_const_bits C.jet_elements_indexed_scalar.
Require Import C.jet_elements_null_data_loads C.jet_elements_null_data_small.
Require Import C.jet_output_layout C.jet_output_layout_step C.jet_elements_effects.
Require Import C.jet_application_sep.
Require C.jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition elements_null_data_reserved_write : statement :=
  Scall None
    (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr));
     Ebinop Oeq (Econst_int (Int.repr 5) tint) (Etempvar _t'19 tint) tint].

Lemma exec_elements_null_data_reserved_write (bit : bool) e le m bd dbase bw edge cur :
  e!_writeBit = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_t'19 = Some (Vint (Int.repr (if bit then 5 else 4))) ->
  write_frame_at m bd dbase bw edge cur 1 ->
  exists mf, Clight2.exec_stmt elements_ge e le m elements_null_data_reserved_write E0 le mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 1 [Some bit].
Proof.
  intros Hnone HD HC HF.
  destruct (elements_writeBit_step m bd dbase bw edge cur bit HF) as (mf & CALL & EFFECT).
  exists mf. split; [|exact EFFECT]. unfold elements_null_data_reserved_write.
  change le with (set_opttemp None (Vint (if bit then Int.one else Int.zero)) le) at 2.
  eapply exec_elements_helper_call with (f := jets.f_writeBit)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vint (if bit then Int.one else Int.zero)])
    (vres := Vint (if bit then Int.one else Int.zero)).
  - unfold elements_core_helpers; simpl; tauto.
  - exact Hnone.
  - eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs with (v1 := Vint (if bit then Int.one else Int.zero));
      [|destruct bit; reflexivity|apply eval_Enil].
    eapply eval_Ebinop with (v1 := Vint (Int.repr 5))
      (v2 := Vint (Int.repr (if bit then 5 else 4))).
    + apply eval_Econst_int.
    + apply eval_Etempvar; exact HC.
    + destruct bit; reflexivity.
  - reflexivity.
  - exact CALL.
Qed.

Definition elements_null_data_reserved_tail : statement :=
  elements_append_stmt (elements_null_data_reload _t'16 _t'17 _t'18 _t'19)
    elements_null_data_reserved_write.

Theorem exec_elements_null_data_reserved_tail (bit : bool) e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j :
  e!_writeBit = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j
    (Int.repr (if bit then 5 else 4)) ->
  write_frame_at m bd dbase bw edge cur 1 ->
  exists mf, Clight2.exec_stmt elements_ge e le m elements_null_data_reserved_tail E0
    (elements_null_data_reload_temps _t'16 _t'17 _t'18 _t'19
      bt txbase bout outbase bop opbase (Int.repr (if bit then 5 else 4)) le) mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 1 [Some bit].
Proof.
  intros Hnone HD Henv Hi Hj
    (He0 & HeM & Ht0 & HtM & Ho0 & HoM & Hp0 & HpM & L1 & L2 & L3 & L4) HF.
  set (next := elements_null_data_reload_temps _t'16 _t'17 _t'18 _t'19
    bt txbase bout outbase bop opbase (Int.repr (if bit then 5 else 4)) le).
  assert (Hreload : Clight2.exec_stmt elements_ge e le m
    (elements_null_data_reload _t'16 _t'17 _t'18 _t'19) E0 next m Out_normal).
  { unfold next. eapply exec_elements_null_data_reload; eauto.
    intros t Ht. simpl in Ht. repeat destruct Ht as [Ht|Ht]; subst;
      try contradiction; vm_compute; intuition discriminate. }
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold next. rewrite elements_null_data_reload_temps_other; [exact HD|].
    vm_compute; intuition discriminate. }
  assert (Hcode : next!_t'19 = Some (Vint (Int.repr (if bit then 5 else 4)))).
  { unfold next, elements_null_data_reload_temps. apply PTree.gss. }
  destruct (exec_elements_null_data_reserved_write bit e next m bd dbase bw edge cur Hnone HD' Hcode HF)
    as (mf & HC & HE).
  exists mf. split; [|exact HE]. unfold elements_null_data_reserved_tail.
  change E0 with (E0 ** E0). eapply exec_elements_append_stmt; [exact Hreload|exact HC].
Qed.

Lemma elements_null_data_reserved_tail_source :
  elements_find_set_prefix _t'16 (fn_body f_simplicity_output_null_datum) =
    Some elements_null_data_reserved_tail.
Proof. reflexivity. Qed.

Lemma exec_elements_skip_const n e le m bd dbase bw edge cur :
  0 <= n <= Int.max_signed -> e!_skipBits = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m bd dbase bw edge cur n ->
  exists mf, Clight2.exec_stmt elements_ge e le m (elements_skip_stmt n) E0 le mf Out_normal /\
    write_effect m mf bd dbase bw edge cur n (repeat None (Z.to_nat n)).
Proof.
  intros Hn Hnone HD HF.
  assert (Hnat : Z.of_nat (Z.to_nat n) = n) by (apply Z2Nat.id; lia).
  destruct (elements_skipBits_step m bd dbase bw edge cur (Z.to_nat n) ltac:(rewrite Hnat; exact HF))
    as (mf & HC & HE). rewrite Hnat in HC, HE.
  exists mf. split; [|exact HE]. unfold elements_skip_stmt.
  change le with (set_opttemp None Vundef le) at 2.
  eapply exec_elements_helper_call with (f := jets.f_skipBits)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr n)]) (vres := Vundef).
  - unfold elements_core_helpers; simpl; tauto.
  - exact Hnone.
  - eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs; [apply eval_Econst_int| |apply eval_Enil].
    change (Some (Vlong (Int64.repr (Int.signed (Int.repr n)))) = Some (Vlong (Int64.repr n))).
    rewrite Int.signed_repr; [reflexivity|].
    change (-2147483648 <= n <= 2147483647).
    change (0 <= n <= 2147483647) in Hn. lia.
  - reflexivity.
  - exact HC.
Qed.

Definition elements_null_data_reserved_padded : statement :=
  Ssequence (elements_skip_stmt 3) elements_null_data_reserved_tail.

Theorem exec_elements_null_data_reserved_padded (bit : bool) e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j :
  e!_skipBits = None -> e!_writeBit = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j
    (Int.repr (if bit then 5 else 4)) ->
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 3 b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j) ->
  write_frame_at m bd dbase bw edge cur 4 ->
  exists mf, Clight2.exec_stmt elements_ge e le m elements_null_data_reserved_padded E0
    (elements_null_data_reload_temps _t'16 _t'17 _t'18 _t'19
      bt txbase bout outbase bop opbase (Int.repr (if bit then 5 else 4)) le) mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 4 [None; None; None; Some bit].
Proof.
  intros Hskip Hwrite HD Henv Hi Hj HP HS HF.
  assert (HF3 : write_frame_at m bd dbase bw edge cur 3).
  { eapply write_frame_at_shorter with (count := 4); [lia|exact HF]. }
  destruct (exec_elements_skip_const 3 e le m bd dbase bw edge cur ltac:(change (0 <= 3 <= 2147483647); lia)
    Hskip HD HF3) as (m1 & CS & ES).
  assert (HF1 : write_frame_at m1 bd dbase bw edge (cur - 3) 1).
  { eapply write_frame_at_after_effect with (m := m) (cells := repeat None 3);
      [reflexivity|lia|exact HF|exact ES]. }
  destruct HP as (He0 & HeM & Ht0 & HtM & Ho0 & HoM & Hp0 & HpM & LOADS).
  assert (HCUR : 3 <= cur).
  { destruct HF3 as (_ & _ & _ & Hcur & _). lia. }
  assert (HP1 : elements_null_data_path_valid m1 be ebase bt txbase bout outbase bop opbase i j
    (Int.repr (if bit then 5 else 4))).
  { unfold elements_null_data_path_valid. do 8 (split; [assumption|]).
    eapply elements_null_data_path_loads_preserved with (n := 3);
      [lia|exact HCUR|exact ES|exact HS|exact LOADS]. }
  destruct (exec_elements_null_data_reserved_tail bit e le m1 bd dbase bw edge (cur - 3)
    be ebase bt txbase bout outbase bop opbase i j Hwrite HD Henv Hi Hj HP1 HF1) as (mf & CR & ER).
  exists mf. split.
  - unfold elements_null_data_reserved_padded.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CS|exact CR].
  - change [None; None; None; Some bit] with (repeat None 3 ++ [Some bit]).
    change 4 with (3 + 1).
    eapply write_effect_seq; [reflexivity|lia|exact HF|exact ES|exact ER].
Qed.

Fixpoint elements_find_skip_prefix (n : int) (s : statement) : option statement :=
  match s with
  | Ssequence a b =>
      match a with
      | Scall None (Evar id _) [_; Econst_int v _] =>
          if Pos.eqb id _skipBits && Int.eq n v then Some s else
            elements_stmt_first (elements_find_skip_prefix n a) (elements_find_skip_prefix n b)
      | _ => elements_stmt_first (elements_find_skip_prefix n a) (elements_find_skip_prefix n b)
      end
  | Sifthenelse _ a b => elements_stmt_first (elements_find_skip_prefix n a) (elements_find_skip_prefix n b)
  | Sloop a b => elements_stmt_first (elements_find_skip_prefix n a) (elements_find_skip_prefix n b)
  | _ => None
  end.

Lemma elements_null_data_reserved_padded_source :
  elements_find_skip_prefix (Int.repr 3) (fn_body f_simplicity_output_null_datum) =
    Some elements_null_data_reserved_padded.
Proof. reflexivity. Qed.

Fixpoint elements_first_loop (s : statement) : option statement :=
  match s with
  | Sloop a b => Some (Sloop a b)
  | Ssequence a b | Sifthenelse _ a b =>
      elements_stmt_first (elements_first_loop a) (elements_first_loop b)
  | _ => None
  end.

Definition elements_null_data_debug_loop : statement :=
  match elements_first_loop (fn_body f_simplicity_output_null_datum) with
  | Some s => s | None => Sskip
  end.

Definition elements_null_data_debug_body : statement :=
  match elements_null_data_debug_loop with
  | Sloop (Sifthenelse _ body _) _ => body
  | _ => Sskip
  end.

Lemma elements_null_data_debug_source :
  elements_first_loop (fn_body f_simplicity_output_null_datum) =
    Some (Sloop (Sifthenelse (Eunop Onotbool (Econst_int Int.one tint) tint)
      elements_null_data_debug_body Sskip) Sbreak).
Proof. reflexivity. Qed.

Lemma exec_elements_disabled_debug ge e le m dead :
  Clight2.exec_stmt ge e le m
    (Sloop (Sifthenelse (Eunop Onotbool (Econst_int Int.one tint) tint) dead Sskip) Sbreak)
    E0 le m Out_normal.
Proof.
  eapply exec_Sloop_stop2 with (t1 := E0) (t2 := E0) (out1 := Out_normal) (out2 := Out_break).
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
    + eapply eval_Eunop with (v1 := Vint Int.one); [apply eval_Econst_int|reflexivity].
    + reflexivity.
    + apply exec_Sskip.
  - constructor.
  - apply exec_Sbreak.
  - constructor.
Qed.

Definition elements_null_data_reserved_arm : statement :=
  Ssequence elements_null_data_debug_loop elements_null_data_reserved_padded.

Theorem exec_elements_null_data_reserved_arm (bit : bool) e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j :
  e!_skipBits = None -> e!_writeBit = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j
    (Int.repr (if bit then 5 else 4)) ->
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 3 b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j) ->
  write_frame_at m bd dbase bw edge cur 4 ->
  exists mf, Clight2.exec_stmt elements_ge e le m elements_null_data_reserved_arm E0
    (elements_null_data_reload_temps _t'16 _t'17 _t'18 _t'19
      bt txbase bout outbase bop opbase (Int.repr (if bit then 5 else 4)) le) mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 4 [None; None; None; Some bit].
Proof.
  intros Hskip Hwrite HD Henv Hi Hj HP HS HF.
  destruct (exec_elements_null_data_reserved_padded bit e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j Hskip Hwrite HD Henv Hi Hj HP HS HF) as (mf & HC & HE).
  exists mf. split; [|exact HE]. unfold elements_null_data_reserved_arm.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [|exact HC].
  unfold elements_null_data_debug_loop. rewrite elements_null_data_debug_source.
  apply exec_elements_disabled_debug.
Qed.

Fixpoint elements_find_loop_prefix (s : statement) : option statement :=
  match s with
  | Ssequence a b =>
      match a with Sloop _ _ => Some s | _ =>
        elements_stmt_first (elements_find_loop_prefix a) (elements_find_loop_prefix b)
      end
  | Sifthenelse _ a b => elements_stmt_first (elements_find_loop_prefix a) (elements_find_loop_prefix b)
  | _ => None
  end.

Lemma elements_null_data_reserved_arm_source :
  elements_find_loop_prefix (fn_body f_simplicity_output_null_datum) =
    Some elements_null_data_reserved_arm.
Proof. reflexivity. Qed.
