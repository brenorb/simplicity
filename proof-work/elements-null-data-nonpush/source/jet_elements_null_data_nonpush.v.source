(** Non-push opcode arm: actual tag comparison, 253-bit padding and payload. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.Ty Simplicity.Bit Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_bit_expr.
Require Import C.jet_elements_null_data_loads C.jet_elements_null_data_small C.jet_elements_null_data_cases.
Require Import C.jet_elements_null_data_reserved C.jet_elements_null_data_payload.
Require Import C.jet_output_layout C.jet_output_layout_step C.jet_elements_effects C.jet_application_sep.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition elements_nonpush_code (n : nat) (bit small : bool) : int :=
  Int.repr (if small then Z.of_nat n + 6 else if bit then 5 else 4).

Lemma elements_nonpush_is_small n bit small : (n < 16)%nat ->
  Int.cmp Cle (Int.repr 6) (elements_nonpush_code n bit small) = small.
Proof.
  intros Hn. destruct small; [|destruct bit; reflexivity].
  unfold elements_nonpush_code, Int.cmp, Int.lt.
  rewrite (Int.signed_repr (Z.of_nat n + 6)) by
    (change (-2147483648 <= Z.of_nat n + 6 <= 2147483647); lia).
  change (Int.signed (Int.repr 6)) with 6.
  destruct (zlt (Z.of_nat n + 6) 6); [lia|reflexivity].
Qed.

Definition elements_null_data_small_test : expr :=
  Ebinop Ole (Econst_int (Int.repr 6) tint) (Etempvar _t'35 tint) tint.

Lemma eval_elements_null_data_small_test n bit small e le m :
  (n < 16)%nat -> le!_t'35 = Some (Vint (elements_nonpush_code n bit small)) ->
  eval_expr elements_ge e le m elements_null_data_small_test (Vint (if small then Int.one else Int.zero)).
Proof.
  intros Hn HC. unfold elements_null_data_small_test.
  eapply eval_Ebinop with (v1 := Vint (Int.repr 6)) (v2 := Vint (elements_nonpush_code n bit small)).
  - apply eval_Econst_int.
  - apply eval_Etempvar; exact HC.
  - change (Some (Val.of_bool (Int.cmp Cle (Int.repr 6) (elements_nonpush_code n bit small))) =
      Some (Vint (if small then Int.one else Int.zero))).
    rewrite elements_nonpush_is_small by exact Hn. destruct small; reflexivity.
Qed.

Definition elements_null_data_small_condition : statement :=
  elements_append_stmt (elements_null_data_reload _t'32 _t'33 _t'34 _t'35)
    (elements_bit_expr_stmt (Some _t'4) elements_null_data_small_test).

Definition elements_nonpush_condition_temps (n : nat) (bit small : bool) bt txbase bout outbase bop opbase le :=
  PTree.set _t'4 (Vint (if small then Int.one else Int.zero))
    (elements_null_data_reload_temps _t'32 _t'33 _t'34 _t'35
      bt txbase bout outbase bop opbase (elements_nonpush_code n bit small) le).

Theorem exec_elements_null_data_small_condition n bit small e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j :
  (n < 16)%nat -> e!_writeBit = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j (elements_nonpush_code n bit small) ->
  write_frame_at m bd dbase bw edge cur 1 ->
  exists mf, Clight2.exec_stmt elements_ge e le m elements_null_data_small_condition E0
    (elements_nonpush_condition_temps n bit small bt txbase bout outbase bop opbase le) mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 1 [Some small].
Proof.
  intros Hn HW HD Henv Hi Hj
    (He0 & HeM & Ht0 & HtM & Ho0 & HoM & Hp0 & HpM & L1 & L2 & L3 & L4) HF.
  set (next := elements_null_data_reload_temps _t'32 _t'33 _t'34 _t'35
    bt txbase bout outbase bop opbase (elements_nonpush_code n bit small) le).
  assert (HR : Clight2.exec_stmt elements_ge e le m
    (elements_null_data_reload _t'32 _t'33 _t'34 _t'35) E0 next m Out_normal).
  { unfold next. eapply exec_elements_null_data_reload; eauto.
    intros t Ht. simpl in Ht. repeat destruct Ht as [Ht|Ht]; subst;
      try contradiction; vm_compute; intuition discriminate. }
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold next. rewrite elements_null_data_reload_temps_other; [exact HD|]. vm_compute; intuition discriminate. }
  assert (HC : next!_t'35 = Some (Vint (elements_nonpush_code n bit small))).
  { unfold next, elements_null_data_reload_temps. apply PTree.gss. }
  destruct (exec_elements_bit_expr small (Some _t'4) elements_null_data_small_test e next m bd dbase bw edge cur
    eq_refl HW HD' (eval_elements_null_data_small_test n bit small e next m Hn HC) HF) as (mf & CALL & EFF).
  exists mf. split; [|exact EFF]. unfold elements_null_data_small_condition, elements_nonpush_condition_temps.
  change E0 with (E0 ** E0). eapply exec_elements_append_stmt; [exact HR|exact CALL].
Qed.

Lemma elements_null_data_small_condition_source :
  elements_find_head_prefix _t'32 (fn_body f_simplicity_output_null_datum) =
    Some (Ssequence elements_null_data_small_condition
      (Sifthenelse (Etempvar _t'4 tbool)
        (elements_append_stmt (elements_null_data_reload _t'28 _t'29 _t'30 _t'31)
          (Sswitch (fst elements_null_data_small_switch) (snd elements_null_data_small_switch)))
        elements_null_data_reserved_arm)).
Proof. reflexivity. Qed.

Definition elements_nonpush_value (n : nat) (bit small : bool) : Ty.tySem (Ty.Sum Bit (Word 2)) :=
  if small then inr (@fromZ (WordToZ 2) (Z.of_nat n)) else inl (Bit.fromBool bit).

Lemma elements_nonpush_value_cells n bit small :
  @encode (Ty.Sum Bit (Word 2)) (elements_nonpush_value n bit small) =
    Some small :: (if small then @encode (Word 2) (@fromZ (WordToZ 2) (Z.of_nat n))
      else [None; None; None; Some bit]).
Proof. destruct small; [reflexivity|destruct bit; reflexivity]. Qed.

Lemma elements_null_data_path_valid_after m mf bd dbase bw edge cur count cells
    be ebase bt txbase bout outbase bop opbase i j code :
  0 < count -> count <= cur -> write_effect m mf bd dbase bw edge cur count cells ->
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur count b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j code ->
  elements_null_data_path_valid mf be ebase bt txbase bout outbase bop opbase i j code.
Proof.
  intros Hn Hcur HE HS (He0 & HeM & Ht0 & HtM & Ho0 & HoM & Hp0 & HpM & LOADS).
  unfold elements_null_data_path_valid. do 8 (split; [assumption|]).
  eapply elements_null_data_path_loads_preserved; eassumption.
Qed.

Definition elements_null_data_nonpush_choice : statement :=
  Ssequence elements_null_data_small_condition
    (Sifthenelse (Etempvar _t'4 tbool)
      (elements_append_stmt (elements_null_data_reload _t'28 _t'29 _t'30 _t'31)
        (Sswitch (fst elements_null_data_small_switch) (snd elements_null_data_small_switch)))
      elements_null_data_reserved_arm).

Theorem exec_elements_null_data_nonpush_choice n bit small e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j :
  (n < 16)%nat -> e!_writeBit = None -> e!_skipBits = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j (elements_nonpush_code n bit small) ->
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 5 b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j) ->
  write_frame_at m bd dbase bw edge cur 5 ->
  exists le' mf, Clight2.exec_stmt elements_ge e le m elements_null_data_nonpush_choice E0 le' mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 5 (@encode (Ty.Sum Bit (Word 2)) (elements_nonpush_value n bit small)).
Proof.
  intros Hn HW HS HD Henv Hi Hj HP HSEP HF.
  pose proof HF as (_ & _ & _ & HCUR & _).
  assert (HF1 : write_frame_at m bd dbase bw edge cur 1).
  { eapply write_frame_at_shorter with (count := 5); [lia|exact HF]. }
  destruct (exec_elements_null_data_small_condition n bit small e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j Hn HW HD Henv Hi Hj HP HF1) as (m1 & CC & EC).
  set (next := elements_nonpush_condition_temps n bit small bt txbase bout outbase bop opbase le).
  assert (HF4 : write_frame_at m1 bd dbase bw edge (cur - 1) 4).
  { eapply write_frame_at_after_effect with (m := m) (cells := [Some small]);
      [reflexivity|lia|exact HF|exact EC]. }
  assert (HSEP1 : Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 1 b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j)).
  { eapply Forall_impl; [|exact HSEP]. intros [[b lo] hi] H.
    eapply out_sep_sub with (cursor := cur) (count := 5); [lia|lia|lia|lia|exact H]. }
  assert (HP1 : elements_null_data_path_valid m1 be ebase bt txbase bout outbase bop opbase i j
    (elements_nonpush_code n bit small)).
  { eapply elements_null_data_path_valid_after with (cur := cur) (count := 1);
      [lia|lia|exact EC|exact HSEP1|exact HP]. }
  assert (Hother : forall k, In k [_dst; _env; _i; _j] -> next!k = le!k).
  { intros k HK. unfold next, elements_nonpush_condition_temps.
    assert (Hneq : k <> _t'4).
    { intros Hk. subst k. vm_compute in HK. intuition discriminate. }
    rewrite PTree.gso by exact Hneq.
    rewrite elements_null_data_reload_temps_other; [reflexivity|].
    intros HB. simpl in HB. repeat destruct HB as [HB|HB]; try contradiction;
      subst k; vm_compute in HK; intuition discriminate. }
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))) by (rewrite Hother by (simpl; tauto); exact HD).
  assert (Henv' : next!_env = Some (Vptr be (Ptrofs.repr ebase))) by (rewrite Hother by (simpl; tauto); exact Henv).
  assert (Hi' : next!_i = Some (Vlong i)) by (rewrite Hother by (simpl; tauto); exact Hi).
  assert (Hj' : next!_j = Some (Vlong j)) by (rewrite Hother by (simpl; tauto); exact Hj).
  assert (HC : next!_t'4 = Some (Vint (if small then Int.one else Int.zero))).
  { unfold next, elements_nonpush_condition_temps. apply PTree.gss. }
  destruct small.
  - destruct (exec_elements_null_data_reload_small n e next m1 bd dbase bw edge (cur - 1)
      be ebase bt txbase bout outbase bop opbase i j Hn HW HD' Henv' Hi' Hj' HP1 HF4) as (mf & CR & ER).
    eexists; exists mf. split.
    + unfold elements_null_data_nonpush_choice.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CC|].
      eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true);
        [apply eval_Etempvar; exact HC|reflexivity|exact CR].
    + rewrite elements_nonpush_value_cells. change 5 with (1 + 4).
      change (Some Datatypes.true :: @encode (Word 2) (@fromZ (WordToZ 2) (Z.of_nat n))) with
        ([Some Datatypes.true] ++ @encode (Word 2) (@fromZ (WordToZ 2) (Z.of_nat n))).
      eapply write_effect_seq; [reflexivity|lia|exact HF|exact EC|exact ER].
  - assert (HSEP3 : Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge (cur - 1) 3 b lo hi)
      (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j)).
    { eapply Forall_impl; [|exact HSEP]. intros [[b lo] hi] H.
      eapply out_sep_sub with (cursor := cur) (count := 5); [lia|lia|lia|lia|exact H]. }
    destruct (exec_elements_null_data_reserved_arm bit e next m1 bd dbase bw edge (cur - 1)
      be ebase bt txbase bout outbase bop opbase i j HS HW HD' Henv' Hi' Hj' HP1 HSEP3 HF4) as (mf & CR & ER).
    eexists; exists mf. split.
    + unfold elements_null_data_nonpush_choice.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CC|].
      eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false);
        [apply eval_Etempvar; exact HC|reflexivity|exact CR].
    + rewrite elements_nonpush_value_cells. change 5 with (1 + 4).
      change [Some Datatypes.false; None; None; None; Some bit] with ([Some Datatypes.false] ++ [None; None; None; Some bit]).
      eapply write_effect_seq; [reflexivity|lia|exact HF|exact EC|exact ER].
Qed.

Definition elements_null_data_padding_count : expr :=
  Ebinop Osub (Ebinop Oadd (Econst_int (Int.repr 2) tint) (Econst_int (Int.repr 256) tint) tint)
    (Econst_int (Int.repr 5) tint) tint.

Lemma eval_elements_null_data_padding_count e le m :
  eval_expr elements_ge e le m elements_null_data_padding_count (Vint (Int.repr 253)).
Proof.
  unfold elements_null_data_padding_count.
  eapply eval_Ebinop with (v1 := Vint (Int.repr 258)) (v2 := Vint (Int.repr 5)).
  - eapply eval_Ebinop with (v1 := Vint (Int.repr 2)) (v2 := Vint (Int.repr 256));
      [apply eval_Econst_int|apply eval_Econst_int|reflexivity].
  - apply eval_Econst_int.
  - reflexivity.
Qed.

Definition elements_null_data_nonpush_arm : statement :=
  Ssequence (elements_skip_expr_stmt elements_null_data_padding_count) elements_null_data_nonpush_choice.

Theorem exec_elements_null_data_nonpush_arm n bit small e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase bop opbase i j :
  (n < 16)%nat -> e!_writeBit = None -> e!_skipBits = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  elements_null_data_path_valid m be ebase bt txbase bout outbase bop opbase i j (elements_nonpush_code n bit small) ->
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 258 b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j) ->
  write_frame_at m bd dbase bw edge cur 258 ->
  exists le' mf, Clight2.exec_stmt elements_ge e le m elements_null_data_nonpush_arm E0 le' mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 258
      (repeat None 253 ++ @encode (Ty.Sum Bit (Word 2)) (elements_nonpush_value n bit small)).
Proof.
  intros Hn HW HS HD Henv Hi Hj HP HSEP HF.
  pose proof HF as (_ & _ & _ & HCUR & _).
  assert (HF253 : write_frame_at m bd dbase bw edge cur 253).
  { eapply write_frame_at_shorter with (count := 258); [lia|exact HF]. }
  destruct (exec_elements_skip_expr 253 elements_null_data_padding_count e le m bd dbase bw edge cur
    ltac:(change (0 <= 253 <= 2147483647); lia) eq_refl HS HD
    (eval_elements_null_data_padding_count e le m) HF253) as (m1 & CS & ES).
  assert (HF5 : write_frame_at m1 bd dbase bw edge (cur - 253) 5).
  { eapply write_frame_at_after_effect with (m := m) (cells := repeat None 253);
      [reflexivity|lia|exact HF|exact ES]. }
  assert (HSEP253 : Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 253 b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j)).
  { eapply Forall_impl; [|exact HSEP]. intros [[b lo] hi] H.
    eapply out_sep_sub with (cursor := cur) (count := 258); [lia|lia|lia|lia|exact H]. }
  assert (HP1 : elements_null_data_path_valid m1 be ebase bt txbase bout outbase bop opbase i j
    (elements_nonpush_code n bit small)).
  { eapply elements_null_data_path_valid_after with (cur := cur) (count := 253);
      [lia|lia|exact ES|exact HSEP253|exact HP]. }
  assert (HSEP5 : Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge (cur - 253) 5 b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j)).
  { eapply Forall_impl; [|exact HSEP]. intros [[b lo] hi] H.
    eapply out_sep_sub with (cursor := cur) (count := 258); [lia|lia|lia|lia|exact H]. }
  destruct (exec_elements_null_data_nonpush_choice n bit small e le m1 bd dbase bw edge (cur - 253)
    be ebase bt txbase bout outbase bop opbase i j Hn HW HS HD Henv Hi Hj HP1 HSEP5 HF5) as (le' & mf & CC & EC).
  exists le', mf. split.
  - unfold elements_null_data_nonpush_arm.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact CS|exact CC].
  - change 258 with (253 + 5).
    eapply write_effect_seq; [reflexivity|lia|exact HF|exact ES|exact EC].
Qed.

Fixpoint elements_find_call_prefix (id : ident) (s : statement) : option statement :=
  match s with
  | Ssequence a b =>
      match a with
      | Scall None (Evar id' _) _ => if Pos.eqb id id' then Some s else
          elements_stmt_first (elements_find_call_prefix id a) (elements_find_call_prefix id b)
      | _ => elements_stmt_first (elements_find_call_prefix id a) (elements_find_call_prefix id b)
      end
  | Sifthenelse _ a b | Sloop a b =>
      elements_stmt_first (elements_find_call_prefix id a) (elements_find_call_prefix id b)
  | _ => None
  end.

Lemma elements_null_data_nonpush_arm_source :
  elements_find_call_prefix _skipBits (fn_body f_simplicity_output_null_datum) = Some elements_null_data_nonpush_arm.
Proof. reflexivity. Qed.
