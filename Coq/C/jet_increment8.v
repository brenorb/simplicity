(** Conditional Clight execution infrastructure for [simplicity_increment_8].

    This file deliberately keeps the read/write helper calls explicit.  The
    resulting body theorem is composition infrastructure; the public
    equivalence theorem must still prove those helper executions from a
    concrete frame layout. *)

From Coq Require Import ZArith List PArith.BinPos.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.

Require Import C.jet_exec.
Require Import C.jet_one8.
Require Import C.jet_write8.
Require Import jets.

Import Clightdefs Clightdefs.ClightNotations.
Import Values Mem Ctypes.
Import Events.

Local Open Scope Z_scope.
Local Open Scope clight_scope.

Definition e_increment8 (bl : block) : env :=
  PTree.set _src (bl, Tstruct _frameItem noattr) empty_env.

Definition le_increment8 (bd bs : block) (ofs : ptrofs) : temp_env :=
  PTree.set _dst (Vptr bd Ptrofs.zero)
    (PTree.set _src (Vptr bs ofs)
      (PTree.set _env Vundef
        (create_undef_temps f_simplicity_increment_8.(fn_temps)))).

Lemma entry_increment8 : forall (m m1 : mem) (bl bd bs : block)
    (ofs : ptrofs),
    Mem.alloc m 0 16 = (m1, bl) ->
  function_entry2 ge0 f_simplicity_increment_8
    (Vptr bd Ptrofs.zero :: Vptr bs ofs :: Vundef :: nil) m
    (e_increment8 bl) (le_increment8 bd bs ofs) m1.
Proof.
  intros m m1 bl bd bs ofs Halloc.
  constructor.
  - change (list_norepet (_src :: nil)).
    repeat constructor; simpl; tauto.
  - change (list_norepet (_dst :: _src :: _env :: nil)).
    unfold _dst, _src, _env.
    repeat constructor; simpl; intuition discriminate.
  - change (list_disjoint (_dst :: _src :: _env :: nil)
      (_x :: _t'1 :: nil)).
    intros id1 id2 H1 H2 Heq.
    simpl in H1, H2.
    subst id2.
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H
    end.
    all: vm_compute in *; congruence.
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bl).
    + change (Mem.alloc m 0 16 = (m1, bl)). exact Halloc.
    + constructor.
  - simpl [le_increment8]. reflexivity.
Qed.

Lemma exec_increment8_copy : forall (m m' : mem) (bl bd bs : block)
    (ofs : ptrofs) (bytes : list memval),
    (access_mode (Tstruct _frameItem noattr) = By_copy) ->
    (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr) > 0 ->
      (alignof_blockcopy prog.(prog_comp_env) (Tstruct _frameItem noattr) |
        Ptrofs.unsigned ofs)) ->
    (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr) > 0 ->
      (alignof_blockcopy prog.(prog_comp_env) (Tstruct _frameItem noattr) |
        Ptrofs.unsigned Ptrofs.zero)) ->
    bl <> bs \/
      Ptrofs.unsigned ofs = Ptrofs.unsigned Ptrofs.zero \/
      Ptrofs.unsigned ofs + sizeof prog.(prog_comp_env)
        (Tstruct _frameItem noattr) <= Ptrofs.unsigned Ptrofs.zero \/
      Ptrofs.unsigned Ptrofs.zero + sizeof prog.(prog_comp_env)
        (Tstruct _frameItem noattr) <= Ptrofs.unsigned ofs ->
    Mem.loadbytes m bs (Ptrofs.unsigned ofs)
      (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr)) = Some bytes ->
    Mem.storebytes m bl 0 bytes = Some m' ->
    ClightBigstep.Clight2.exec_stmt ge0 (e_increment8 bl)
      (le_increment8 bd bs ofs) m
      (Sassign (Evar _src (Tstruct _frameItem noattr))
        (Etempvar _src (Tstruct _frameItem noattr)))
      E0 (le_increment8 bd bs ofs) m' Out_normal.
Proof.
  intros m m' bl bd bs ofs bytes Hmode Hsrc_align Hdst_align Hdisjoint
    Hload Hstore.
  eapply exec_Sassign_copy.
  - eapply eval_Evar_local.
    simpl [e_increment8]. reflexivity.
  - eapply eval_Etempvar.
    simpl [le_increment8]. reflexivity.
  - cbn; reflexivity.
  - eapply assign_frameItem_copy; eauto.
Qed.

Definition le_increment8_read (bd bs : block) (ofs : ptrofs) (r : int) :
    temp_env :=
  PTree.set _t'1 (Vint r) (le_increment8 bd bs ofs).

Definition le_increment8_x (bd bs : block) (ofs : ptrofs) (r : int) :
    temp_env :=
  PTree.set _x (Vint (Int.zero_ext 8 r))
    (le_increment8_read bd bs ofs r).

Definition increment8_read_stmt : statement :=
  Scall (Some _t'1)
    (Evar _simplicity_read8
      (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil)
        tuchar cc_default))
    ((Eaddrof (Evar _src (Tstruct _frameItem noattr))
      (tptr (Tstruct _frameItem noattr))) :: nil).

Lemma call_increment8_read : forall (le : temp_env) (m m' : mem)
    (bl : block) (r : int) (b : block),
  Genv.find_symbol (Clight.genv_genv ge0) _simplicity_read8 = Some b ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr b Ptrofs.zero) =
    Some (Internal f_simplicity_read8) ->
  ClightBigstep.Clight2.eval_funcall ge0 m
    (Internal f_simplicity_read8)
    (Vptr bl Ptrofs.zero :: nil) E0 m' (Vint r) ->
  ClightBigstep.Clight2.exec_stmt ge0 (e_increment8 bl) le m
    increment8_read_stmt E0 (PTree.set _t'1 (Vint r) le) m'
    Out_normal.
Proof.
  intros le m m' bl r b Hsym Hfun Hread.
  change (ClightBigstep.exec_stmt function_entry2 ge0 (e_increment8 bl) le m
    increment8_read_stmt E0 (set_opttemp (Some _t'1) (Vint r) le) m'
    Out_normal).
  eapply ClightBigstep.exec_Scall
    with (vf := Vptr b Ptrofs.zero)
         (vargs := Vptr bl Ptrofs.zero :: nil)
         (f := Internal f_simplicity_read8) (vres := Vint r).
  - vm_compute; reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global.
      * simpl; reflexivity.
      * exact Hsym.
    + apply deref_loc_reference.
      change (access_mode
        (Tfunction
          (Tcons (tptr (Tstruct _frameItem noattr)) Tnil)
          tuchar cc_default) = By_reference).
      reflexivity.
  - eapply eval_Econs.
    + eapply eval_Eaddrof.
      eapply eval_Evar_local.
      simpl [e_increment8]. reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - exact Hfun.
  - vm_compute; reflexivity.
  - exact Hread.
Qed.

Definition increment8_setx_stmt : statement :=
  Sset _x (Ecast (Etempvar _t'1 tuchar) tuchar).

Definition increment8_carry_expr : expr :=
  Ebinop Olt
    (Ebinop Osub
      (Ebinop Omul (Econst_int (Int.repr 1) tuint)
        (Econst_int (Int.repr 255) tuint) tuint)
      (Econst_int (Int.repr 1) tint) tuint)
    (Etempvar _x tuchar) tint.

Definition increment8_bit_stmt : statement :=
  Scall None
    (Evar _writeBit
      (Tfunction
        (Tcons (tptr (Tstruct _frameItem noattr))
          (Tcons tbool Tnil)) tbool cc_default))
    ((Etempvar _dst (tptr (Tstruct _frameItem noattr))) ::
     increment8_carry_expr :: nil).

Lemma call_increment8_writeBit : forall (le : temp_env) (m m' : mem)
    (bl bd : block) (bit : int) (vret : val) (b : block),
  le!_dst = Some (Vptr bd Ptrofs.zero) ->
  eval_expr ge0 (e_increment8 bl) le m increment8_carry_expr
    (Vint bit) ->
  sem_cast (Vint bit) (typeof increment8_carry_expr) tbool m =
    Some (Vint bit) ->
  Genv.find_symbol (Clight.genv_genv ge0) _writeBit = Some b ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr b Ptrofs.zero) =
    Some (Internal f_writeBit) ->
  ClightBigstep.Clight2.eval_funcall ge0 m
    (Internal f_writeBit)
    (Vptr bd Ptrofs.zero :: Vint bit :: nil) E0 m' vret ->
  ClightBigstep.Clight2.exec_stmt ge0 (e_increment8 bl) le m
    increment8_bit_stmt E0 le m' Out_normal.
Proof.
  intros le m m' bl bd bit vret b Hdst Hbit Hbit_cast Hsym Hfun HwriteBit.
  change (ClightBigstep.exec_stmt function_entry2 ge0 (e_increment8 bl) le m
    increment8_bit_stmt E0 le m' Out_normal).
  eapply ClightBigstep.exec_Scall
    with (vf := Vptr b Ptrofs.zero)
         (vargs := Vptr bd Ptrofs.zero :: Vint bit :: nil)
         (f := Internal f_writeBit) (vres := vret).
  - vm_compute; reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global.
      * simpl; reflexivity.
      * exact Hsym.
    + apply deref_loc_reference.
      change (access_mode
        (Tfunction
          (Tcons (tptr (Tstruct _frameItem noattr))
            (Tcons tbool Tnil)) tbool cc_default) = By_reference).
      reflexivity.
  - eapply eval_Econs.
    + eapply eval_Etempvar; exact Hdst.
    + reflexivity.
    + eapply eval_Econs.
      * exact Hbit.
      * exact Hbit_cast.
      * apply eval_Enil.
  - exact Hfun.
  - vm_compute; reflexivity.
  - exact HwriteBit.
Qed.

Definition increment8_sum_expr : expr :=
  Ecast
    (Ebinop Oadd
      (Ebinop Omul (Econst_int (Int.repr 1) tuint)
        (Etempvar _x tuchar) tuint)
      (Econst_int (Int.repr 1) tint) tuint)
    tuchar.

Definition increment8_write_stmt : statement :=
  Scall None
    (Evar _simplicity_write8
      (Tfunction
        (Tcons (tptr (Tstruct _frameItem noattr))
          (Tcons tuchar Tnil)) tvoid cc_default))
    ((Etempvar _dst (tptr (Tstruct _frameItem noattr))) ::
     increment8_sum_expr :: nil).

Lemma call_increment8_write : forall (le : temp_env) (m m' : mem)
    (bl bd : block) (x : int) (b : block),
  le!_dst = Some (Vptr bd Ptrofs.zero) ->
  eval_expr ge0 (e_increment8 bl) le m increment8_sum_expr
    (Vint x) ->
  sem_cast (Vint x) (typeof increment8_sum_expr) tuchar m =
    Some (Vint x) ->
  Genv.find_symbol (Clight.genv_genv ge0) _simplicity_write8 = Some b ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr b Ptrofs.zero) =
    Some (Internal f_simplicity_write8) ->
  ClightBigstep.Clight2.eval_funcall ge0 m
    (Internal f_simplicity_write8)
    (Vptr bd Ptrofs.zero :: Vint x :: nil) E0 m' Vundef ->
  ClightBigstep.Clight2.exec_stmt ge0 (e_increment8 bl) le m
    increment8_write_stmt E0 le m' Out_normal.
Proof.
  intros le m m' bl bd x b Hdst Hx Hx_cast Hsym Hfun Hwrite8.
  change (ClightBigstep.exec_stmt function_entry2 ge0 (e_increment8 bl) le m
    increment8_write_stmt E0 le m' Out_normal).
  eapply ClightBigstep.exec_Scall
    with (vf := Vptr b Ptrofs.zero)
         (vargs := Vptr bd Ptrofs.zero :: Vint x :: nil)
         (f := Internal f_simplicity_write8) (vres := Vundef).
  - vm_compute; reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global.
      * simpl; reflexivity.
      * exact Hsym.
    + apply deref_loc_reference.
      change (access_mode
        (Tfunction
          (Tcons (tptr (Tstruct _frameItem noattr))
            (Tcons tuchar Tnil)) tvoid cc_default) = By_reference).
      reflexivity.
  - eapply eval_Econs.
    + eapply eval_Etempvar; exact Hdst.
    + reflexivity.
    + eapply eval_Econs.
      * exact Hx.
      * exact Hx_cast.
      * apply eval_Enil.
  - exact Hfun.
  - vm_compute; reflexivity.
  - exact Hwrite8.
Qed.

Lemma eval_increment8_setx : forall (m : mem) (bl bd bs : block)
    (ofs : ptrofs) (r : int),
  eval_expr ge0 (e_increment8 bl) (le_increment8_read bd bs ofs r) m
    (Ecast (Etempvar _t'1 tuchar) tuchar)
    (Vint (Int.zero_ext 8 r)).
Proof.
  intros m bl bd bs ofs r.
  eapply eval_Ecast.
  - eapply eval_Etempvar.
    simpl [le_increment8_read le_increment8]. reflexivity.
  - cbn; reflexivity.
Qed.

Lemma increment8_body_composes : forall
    (m m1 m2 m3 m4 : mem) (bl bd bs : block) (ofs : ptrofs) (r : int),
  ClightBigstep.Clight2.exec_stmt ge0 (e_increment8 bl)
    (le_increment8 bd bs ofs) m
    (Sassign (Evar _src (Tstruct _frameItem noattr))
      (Etempvar _src (Tstruct _frameItem noattr)))
    E0 (le_increment8 bd bs ofs) m1 Out_normal ->
  ClightBigstep.Clight2.exec_stmt ge0 (e_increment8 bl)
    (le_increment8 bd bs ofs) m1 increment8_read_stmt
    E0 (le_increment8_read bd bs ofs r) m2 Out_normal ->
  ClightBigstep.Clight2.exec_stmt ge0 (e_increment8 bl)
    (le_increment8_x bd bs ofs r) m2 increment8_bit_stmt
    E0 (le_increment8_x bd bs ofs r) m3 Out_normal ->
  ClightBigstep.Clight2.exec_stmt ge0 (e_increment8 bl)
    (le_increment8_x bd bs ofs r) m3 increment8_write_stmt
    E0 (le_increment8_x bd bs ofs r) m4 Out_normal ->
  ClightBigstep.Clight2.exec_stmt ge0 (e_increment8 bl)
    (le_increment8 bd bs ofs) m (fn_body f_simplicity_increment_8)
    E0 (le_increment8_x bd bs ofs r) m4
    (Out_return (Some (Vint (Int.repr 1), tint))).
Proof.
  intros m m1 m2 m3 m4 bl bd bs ofs r Hcopy Hread Hbit Hwrite.
  unfold f_simplicity_increment_8; cbn.
  eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
  - exact Hcopy.
  - eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
    + eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * exact Hread.
      * apply exec_set.
        apply eval_increment8_setx.
    + eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
      * exact Hbit.
      * eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- exact Hwrite.
        -- apply ClightBigstep.exec_Sreturn_some.
           apply eval_Econst_int.
Qed.
