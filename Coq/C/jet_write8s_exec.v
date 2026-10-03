(** Exact pointer/count loop of write8s.  The internal run witness records
    each actual array load and write8 call; the layout contract must derive
    that witness from initial array/frame conditions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_write8.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma write8s_writer_symbol : Genv.find_symbol (Clight.genv_genv ge0) _simplicity_write8 =
  Some (jet_symbol_block _simplicity_write8).
Proof. vm_compute; reflexivity. Qed.
Lemma write8s_writer_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _simplicity_write8) Ptrofs.zero) = Some (Internal f_simplicity_write8).
Proof. vm_compute; reflexivity. Qed.
Lemma uint8_load_zero_ext m bi input x :
  Mem.load Mint8unsigned m bi input = Some (Vint x) -> Int.zero_ext 8 x = x.
Proof.
  intro HL. pose proof (Mem.load_cast m Mint8unsigned bi input (Vint x) HL) as H.
  change (Vint x = Vint (Int.zero_ext 8 x)) in H. congruence.
Qed.

Fixpoint write8s_run bi input bf base (xs : list int) m mf : Prop :=
  match xs with
  | [] => m = mf
  | x :: rest => exists mi,
    Mem.load Mint8unsigned m bi input = Some (Vint x) /\
    Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
      [Vptr bf (Ptrofs.repr base); Vint x] E0 mi Vundef /\
    write8s_run bi (input + 1) bf base rest mi mf
  end.
Definition write8s_loop_body := match f_write8s.(fn_body) with
  Sloop body _ => body | _ => Sskip end.
Definition write8s_loop_step := Sset _n
  (Ebinop Osub (Etempvar _n tulong) (Econst_int (Int.repr 1) tint) tulong).
Lemma write8s_body_shape : f_write8s.(fn_body) = Sloop write8s_loop_body write8s_loop_step.
Proof. reflexivity. Qed.
Definition write8s_body_env le bi input x :=
  PTree.set _t'2 (Vint x)
    (PTree.set _x (Vptr bi (Ptrofs.repr (input + 1)))
      (PTree.set _t'1 (Vptr bi (Ptrofs.repr input)) le)).

Lemma exec_write8s_body m mi le bi input bf base x count :
  0 <= input -> input + 1 <= Ptrofs.max_unsigned -> 0 < count <= Int64.max_unsigned ->
  le!_frame = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_x = Some (Vptr bi (Ptrofs.repr input)) -> le!_n = Some (Vlong (Int64.repr count)) ->
  Mem.load Mint8unsigned m bi input = Some (Vint x) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
    [Vptr bf (Ptrofs.repr base); Vint x] E0 mi Vundef ->
  Clight2.exec_stmt ge0 empty_env le m write8s_loop_body E0
    (write8s_body_env le bi input x) mi Out_normal.
Proof.
  intros HB HM HN HF HX HC HL HW.
  pose proof (uint8_load_zero_ext m bi input x HL) as Hcast.
  assert (Hnonzero : Int64.eq (Int64.repr count) Int64.zero = Datatypes.false).
  { apply Int64.eq_false. intro HE. apply (f_equal Int64.unsigned) in HE.
    rewrite Int64.unsigned_repr in HE by lia. change (count = 0) in HE. lia. }
  assert (Haddr : Ptrofs.add (Ptrofs.repr input) (Ptrofs.repr 1) = Ptrofs.repr (input + 1)).
  { unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr input) by lia.
    change (Ptrofs.unsigned (Ptrofs.repr 1)) with 1. reflexivity. }
  unfold write8s_loop_body; cbn [f_write8s fn_body].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m).
  - eapply exec_Sifthenelse with (v1 := Vlong (Int64.repr count)) (b := Datatypes.true).
    + apply eval_Etempvar; exact HC.
    + change (Some (negb (Int64.eq (Int64.repr count) Int64.zero)) = Some Datatypes.true).
      rewrite Hnonzero; reflexivity.
    + apply exec_Sskip.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _x (Vptr bi (Ptrofs.repr (input + 1)))
        (PTree.set _t'1 (Vptr bi (Ptrofs.repr input)) le)).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
        (le1 := PTree.set _t'1 (Vptr bi (Ptrofs.repr input)) le).
      * apply exec_set. apply eval_Etempvar; exact HX.
      * apply exec_set. eapply eval_Ebinop with (v1 := Vptr bi (Ptrofs.repr input))
          (v2 := Vint Int.one).
        -- apply eval_Etempvar. apply PTree.gss.
        -- apply eval_Econst_int.
        -- change (Some (Vptr bi (Ptrofs.add (Ptrofs.repr input) (Ptrofs.repr 1))) =
             Some (Vptr bi (Ptrofs.repr (input + 1)))). rewrite Haddr; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
        (le1 := write8s_body_env le bi input x).
      * apply exec_set. eapply eval_Elvalue.
        -- eapply eval_Ederef. apply eval_Etempvar.
           rewrite PTree.gso by discriminate. apply PTree.gss.
        -- apply deref_loc_value with (chunk := Mint8unsigned); [reflexivity|].
           unfold Mem.loadv. rewrite Ptrofs.unsigned_repr by lia. exact HL.
      * eapply exec_Scall with (vf := Vptr (jet_symbol_block _simplicity_write8) Ptrofs.zero)
          (vargs := [Vptr bf (Ptrofs.repr base); Vint x])
          (f := Internal f_simplicity_write8) (vres := Vundef).
        -- reflexivity.
        -- eapply eval_Elvalue.
           ++ eapply eval_Evar_global; [reflexivity|exact (write8s_writer_symbol)].
           ++ apply deref_loc_reference; reflexivity.
        -- eapply eval_Econs.
           ++ apply eval_Etempvar. unfold write8s_body_env.
              repeat rewrite PTree.gso by discriminate. exact HF.
           ++ reflexivity.
           ++ eapply eval_Econs;
                [apply eval_Etempvar; apply PTree.gss| |apply eval_Enil].
              change (Some (Vint (Int.zero_ext 8 x)) = Some (Vint x)).
              rewrite Hcast; reflexivity.
        -- exact (write8s_writer_funct).
        -- reflexivity.
        -- exact HW.
Qed.

Lemma exec_write8s_run le m mf bi input bf base xs :
  0 <= input -> input + 1 * Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  Z.of_nat (length xs) <= Int64.max_unsigned ->
  le!_frame = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_x = Some (Vptr bi (Ptrofs.repr input)) ->
  le!_n = Some (Vlong (Int64.repr (Z.of_nat (length xs)))) ->
  write8s_run bi input bf base xs m mf ->
  exists lef, Clight2.exec_stmt ge0 empty_env le m f_write8s.(fn_body) E0 lef mf Out_normal.
Proof.
  revert le m input. induction xs as [|x xs IH]; intros le m input HB HM HN HF HX HC HR.
  - change (m = mf) in HR. subst mf. exists le. rewrite write8s_body_shape.
    eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
    unfold write8s_loop_body; cbn [f_write8s fn_body].
    apply exec_Sseq_2; [|discriminate].
    eapply exec_Sifthenelse with (v1 := Vlong Int64.zero) (b := Datatypes.false).
    + apply eval_Etempvar; exact HC.
    + reflexivity.
    + apply exec_Sbreak.
  - destruct HR as [mi [HL [HW HR]]].
    pose proof (exec_write8s_body m mi le bi input bf base x (Z.of_nat (length (x :: xs)))
      HB ltac:(cbn [length] in HM; lia) ltac:(cbn [length] in HN |- *; lia) HF HX HC HL HW) as HS.
    set (len := Z.of_nat (length xs)).
    set (next := PTree.set _n (Vlong (Int64.repr len)) (write8s_body_env le bi input x)).
    assert (Hcount : Int64.sub (Int64.repr (Z.of_nat (length (x :: xs)))) Int64.one = Int64.repr len).
    { unfold Int64.sub. rewrite Int64.unsigned_repr by (cbn [length] in HN |- *; lia).
      change (Int64.unsigned Int64.one) with 1. f_equal. unfold len; cbn [length]; lia. }
    assert (HStep : Clight2.exec_stmt ge0 empty_env (write8s_body_env le bi input x) mi
      write8s_loop_step E0 next mi Out_normal).
    { apply exec_set. eapply eval_Ebinop with
        (v1 := Vlong (Int64.repr (Z.of_nat (length (x :: xs))))) (v2 := Vint Int.one).
      - apply eval_Etempvar. unfold write8s_body_env.
        repeat rewrite PTree.gso by discriminate. exact HC.
      - apply eval_Econst_int.
      - change (Some (Vlong (Int64.sub (Int64.repr (Z.of_nat (length (x :: xs)))) Int64.one)) =
          Some (Vlong (Int64.repr len))). rewrite Hcount; reflexivity. }
    destruct (IH next mi (input + 1) ltac:(lia) ltac:(cbn [length] in HM; lia)
      ltac:(cbn [length] in HN; lia)
      ltac:(unfold next, write8s_body_env; repeat rewrite PTree.gso by discriminate; exact HF)
      ltac:(unfold next, write8s_body_env; rewrite PTree.gso by discriminate;
        rewrite PTree.gso by discriminate; apply PTree.gss)
      ltac:(unfold next; apply PTree.gss) HR) as [lef HRest].
    exists lef. rewrite write8s_body_shape in HRest |- *.
    eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0)
      (le1 := write8s_body_env le bi input x) (m1 := mi) (out1 := Out_normal)
      (le2 := next) (m2 := mi); [exact HS|constructor|exact HStep|exact HRest].
Qed.

Definition write8s_env bf base bi input count :=
  PTree.set _n (Vlong (Int64.repr count))
    (PTree.set _x (Vptr bi (Ptrofs.repr input))
      (PTree.set _frame (Vptr bf (Ptrofs.repr base)) (create_undef_temps f_write8s.(fn_temps)))).
Lemma write8s_entry m bf base bi input count :
  function_entry2 ge0 f_write8s
    [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr input); Vlong (Int64.repr count)]
    m empty_env (write8s_env bf base bi input count) m.
Proof.
  constructor.
  - constructor.
  - repeat constructor; simpl; intuition discriminate.
  - intros i j HI HJ Heq. cbn in HI, HJ; subst j.
    destruct HI as [HI|[HI|[HI|HI]]]; destruct HJ as [HJ|[HJ|HJ]];
      try contradiction; vm_compute in HI, HJ; congruence.
  - constructor.
  - reflexivity.
Qed.

Theorem eval_write8s_from_run m mf bi input bf base xs :
  0 <= input -> input + 1 * Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  Z.of_nat (length xs) <= Int64.max_unsigned -> write8s_run bi input bf base xs m mf ->
  Clight2.eval_funcall ge0 m (Internal f_write8s)
    [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr input);
     Vlong (Int64.repr (Z.of_nat (length xs)))] E0 mf Vundef.
Proof.
  intros HB HM HN HR.
  destruct (exec_write8s_run (write8s_env bf base bi input (Z.of_nat (length xs)))
    m mf bi input bf base xs HB HM HN ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) HR)
    as [lef HS].
  eapply eval_funcall_internal with (e := empty_env)
    (le1 := write8s_env bf base bi input (Z.of_nat (length xs))) (le2 := lef)
    (m1 := m) (m2 := mf) (out := Out_normal);
    [apply write8s_entry|exact HS|reflexivity|reflexivity].
Qed.
