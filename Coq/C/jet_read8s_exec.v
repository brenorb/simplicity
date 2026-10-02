(** Exact read8s pointer/count loop. This INTERNAL run witness records actual
    reader calls and array stores; an initial-layout theorem must derive it
    before this helper can support any public jet equivalence. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_read8.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma read8s_reader_symbol : Genv.find_symbol (Clight.genv_genv ge0) _simplicity_read8 =
  Some (jet_symbol_block _simplicity_read8).
Proof. vm_compute; reflexivity. Qed.
Lemma read8s_reader_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _simplicity_read8) Ptrofs.zero) = Some (Internal f_simplicity_read8).
Proof. vm_compute; reflexivity. Qed.

Fixpoint read8s_run bi input bf base (xs : list int) m mf : Prop :=
  match xs with
  | [] => m = mf
  | x :: rest => exists mi ms,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_read8)
      [Vptr bf (Ptrofs.repr base)] E0 mi (Vint x) /\
    Mem.store Mint8unsigned mi bi input (Vint (Int.zero_ext 8 x)) = Some ms /\
    read8s_run bi (input + 1) bf base rest ms mf
  end.
Definition read8s_loop_body := match f_read8s.(fn_body) with
  Sloop body _ => body | _ => Sskip end.
Definition read8s_loop_step := Sset _n
  (Ebinop Osub (Etempvar _n tulong) (Econst_int (Int.repr 1) tint) tulong).
Lemma read8s_body_shape : f_read8s.(fn_body) = Sloop read8s_loop_body read8s_loop_step.
Proof. reflexivity. Qed.
Definition read8s_body_env le bi input x :=
  PTree.set _t'2 (Vint x)
    (PTree.set _x (Vptr bi (Ptrofs.repr (input + 1)))
      (PTree.set _t'1 (Vptr bi (Ptrofs.repr input)) le)).

Lemma exec_read8s_body m mi ms le bi input bf base x count :
  0 <= input -> input + 1 <= Ptrofs.max_unsigned -> 0 < count <= Int64.max_unsigned ->
  le!_frame = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_x = Some (Vptr bi (Ptrofs.repr input)) -> le!_n = Some (Vlong (Int64.repr count)) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_read8)
    [Vptr bf (Ptrofs.repr base)] E0 mi (Vint x) ->
  Mem.store Mint8unsigned mi bi input (Vint (Int.zero_ext 8 x)) = Some ms ->
  Clight2.exec_stmt ge0 empty_env le m read8s_loop_body E0
    (read8s_body_env le bi input x) ms Out_normal.
Proof.
  intros HB HM HN HF HX HC HR HS.
  assert (Hnonzero : Int64.eq (Int64.repr count) Int64.zero = Datatypes.false).
  { apply Int64.eq_false. intro HE. apply (f_equal Int64.unsigned) in HE.
    rewrite Int64.unsigned_repr in HE by lia. change (count = 0) in HE. lia. }
  assert (Haddr : Ptrofs.add (Ptrofs.repr input) (Ptrofs.repr 1) = Ptrofs.repr (input + 1)).
  { unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr input) by lia.
    change (Ptrofs.unsigned (Ptrofs.repr 1)) with 1. reflexivity. }
  unfold read8s_loop_body; cbn [f_read8s fn_body].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m).
  - eapply exec_Sifthenelse with (v1 := Vlong (Int64.repr count)) (b := Datatypes.true).
    + apply eval_Etempvar; exact HC.
    + change (Some (negb (Int64.eq (Int64.repr count) Int64.zero)) = Some Datatypes.true).
      rewrite Hnonzero; reflexivity.
    + apply exec_Sskip.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi)
      (le1 := read8s_body_env le bi input x).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
        (le1 := PTree.set _x (Vptr bi (Ptrofs.repr (input + 1)))
          (PTree.set _t'1 (Vptr bi (Ptrofs.repr input)) le)).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
          (le1 := PTree.set _t'1 (Vptr bi (Ptrofs.repr input)) le).
        -- apply exec_set. apply eval_Etempvar; exact HX.
        -- apply exec_set. eapply eval_Ebinop with (v1 := Vptr bi (Ptrofs.repr input))
             (v2 := Vint Int.one).
           ++ apply eval_Etempvar. apply PTree.gss.
           ++ apply eval_Econst_int.
           ++ change (Some (Vptr bi (Ptrofs.add (Ptrofs.repr input) (Ptrofs.repr 1))) =
                Some (Vptr bi (Ptrofs.repr (input + 1)))). rewrite Haddr; reflexivity.
      * eapply exec_Scall with (vf := Vptr (jet_symbol_block _simplicity_read8) Ptrofs.zero)
          (vargs := [Vptr bf (Ptrofs.repr base)])
          (f := Internal f_simplicity_read8) (vres := Vint x).
        -- reflexivity.
        -- eapply eval_Elvalue.
           ++ eapply eval_Evar_global; [reflexivity|exact read8s_reader_symbol].
           ++ apply deref_loc_reference; reflexivity.
        -- eapply eval_Econs.
           ++ apply eval_Etempvar. repeat rewrite PTree.gso by discriminate. exact HF.
           ++ reflexivity.
           ++ apply eval_Enil.
        -- exact read8s_reader_funct.
        -- reflexivity.
        -- exact HR.
    + eapply exec_Sassign_value with (v := Vint (Int.zero_ext 8 x))
        (v2 := Vint (Int.zero_ext 8 x)) (b := bi) (ofs := Ptrofs.repr input).
      * eapply eval_Ederef. apply eval_Etempvar.
        unfold read8s_body_env. repeat rewrite PTree.gso by discriminate. apply PTree.gss.
      * eapply eval_Ecast with (v1 := Vint x).
        -- apply eval_Etempvar; apply PTree.gss.
        -- reflexivity.
      * change (Some (Vint (Int.zero_ext 8 (Int.zero_ext 8 x))) = Some (Vint (Int.zero_ext 8 x))).
        rewrite Int.zero_ext_idem by lia; reflexivity.
      * apply assign_loc_value with (chunk := Mint8unsigned); [reflexivity|].
        unfold Mem.storev. rewrite Ptrofs.unsigned_repr by lia. exact HS.
Qed.

Lemma exec_read8s_run le m mf bi input bf base xs :
  0 <= input -> input + Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  Z.of_nat (length xs) <= Int64.max_unsigned ->
  le!_frame = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_x = Some (Vptr bi (Ptrofs.repr input)) ->
  le!_n = Some (Vlong (Int64.repr (Z.of_nat (length xs)))) ->
  read8s_run bi input bf base xs m mf ->
  exists lef, Clight2.exec_stmt ge0 empty_env le m f_read8s.(fn_body) E0 lef mf Out_normal.
Proof.
  revert le m input. induction xs as [|x xs IH]; intros le m input HB HM HN HF HX HC HR.
  - change (m = mf) in HR. subst mf. exists le. rewrite read8s_body_shape.
    eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
    unfold read8s_loop_body; cbn [f_read8s fn_body].
    apply exec_Sseq_2; [|discriminate].
    eapply exec_Sifthenelse with (v1 := Vlong Int64.zero) (b := Datatypes.false).
    + apply eval_Etempvar; exact HC.
    + reflexivity.
    + apply exec_Sbreak.
  - destruct HR as [mi [ms [Hread [Hstore HR]]]].
    pose proof (exec_read8s_body m mi ms le bi input bf base x (Z.of_nat (length (x :: xs)))
      HB ltac:(cbn [length] in HM; lia) ltac:(cbn [length] in HN |- *; lia) HF HX HC Hread Hstore) as HS.
    set (len := Z.of_nat (length xs)).
    set (next := PTree.set _n (Vlong (Int64.repr len)) (read8s_body_env le bi input x)).
    assert (Hcount : Int64.sub (Int64.repr (Z.of_nat (length (x :: xs)))) Int64.one = Int64.repr len).
    { unfold Int64.sub. rewrite Int64.unsigned_repr by (cbn [length] in HN |- *; lia).
      change (Int64.unsigned Int64.one) with 1. f_equal. unfold len; cbn [length]; lia. }
    assert (HStep : Clight2.exec_stmt ge0 empty_env (read8s_body_env le bi input x) ms
      read8s_loop_step E0 next ms Out_normal).
    { apply exec_set. eapply eval_Ebinop with
        (v1 := Vlong (Int64.repr (Z.of_nat (length (x :: xs))))) (v2 := Vint Int.one).
      - apply eval_Etempvar. unfold read8s_body_env.
        repeat rewrite PTree.gso by discriminate. exact HC.
      - apply eval_Econst_int.
      - change (Some (Vlong (Int64.sub (Int64.repr (Z.of_nat (length (x :: xs)))) Int64.one)) =
          Some (Vlong (Int64.repr len))). rewrite Hcount; reflexivity. }
    destruct (IH next ms (input + 1) ltac:(lia) ltac:(cbn [length] in HM; lia)
      ltac:(cbn [length] in HN; lia)
      ltac:(unfold next, read8s_body_env; repeat rewrite PTree.gso by discriminate; exact HF)
      ltac:(unfold next, read8s_body_env; rewrite PTree.gso by discriminate;
        rewrite PTree.gso by discriminate; apply PTree.gss)
      ltac:(unfold next; apply PTree.gss) HR) as [lef HRest].
    exists lef. rewrite read8s_body_shape in HRest |- *.
    eapply exec_Sloop_loop with (t1 := E0) (t2 := E0) (t3 := E0)
      (le1 := read8s_body_env le bi input x) (m1 := ms) (out1 := Out_normal)
      (le2 := next) (m2 := ms); [exact HS|constructor|exact HStep|exact HRest].
Qed.

Definition read8s_env bf base bi input count :=
  PTree.set _n (Vlong (Int64.repr count))
    (PTree.set _x (Vptr bi (Ptrofs.repr input))
      (PTree.set _frame (Vptr bf (Ptrofs.repr base)) (create_undef_temps f_read8s.(fn_temps)))).
Lemma read8s_entry m bf base bi input count :
  function_entry2 ge0 f_read8s
    [Vptr bi (Ptrofs.repr input); Vlong (Int64.repr count); Vptr bf (Ptrofs.repr base)]
    m empty_env (read8s_env bf base bi input count) m.
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

Theorem eval_read8s_from_run m mf bi input bf base xs :
  0 <= input -> input + Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  Z.of_nat (length xs) <= Int64.max_unsigned -> read8s_run bi input bf base xs m mf ->
  Clight2.eval_funcall ge0 m (Internal f_read8s)
    [Vptr bi (Ptrofs.repr input); Vlong (Int64.repr (Z.of_nat (length xs)));
     Vptr bf (Ptrofs.repr base)] E0 mf Vundef.
Proof.
  intros HB HM HN HR.
  destruct (exec_read8s_run (read8s_env bf base bi input (Z.of_nat (length xs)))
    m mf bi input bf base xs HB HM HN ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) HR)
    as [lef HS].
  eapply eval_funcall_internal with (e := empty_env)
    (le1 := read8s_env bf base bi input (Z.of_nat (length xs))) (le2 := lef)
    (m1 := m) (m2 := mf) (out := Out_normal);
    [apply read8s_entry|exact HS|reflexivity|reflexivity].
Qed.
