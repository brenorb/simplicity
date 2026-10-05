(** Execution of the actual C [Round] function of the SHA translation unit:
    two in-place updates through its pointer arguments. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jets_sha C.jet_sha_linkage.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 120.

Definition c_T1 (h e f g k : int) : int :=
  Int.add (Int.add (Int.add h (c_Sigma1 e)) (c_Ch e f g)) k.
Definition c_T2 (a b c : int) : int := Int.add (c_Sigma0 a) (c_Maj a b c).

Lemma int_mul1 x : Int.mul (Int.repr 1) x = x.
Proof. rewrite Int.mul_commut. apply Int.mul_one. Qed.

Definition round_le (a b c : int) (bd : block) (od : ptrofs) (e f g : int) (bh : block) (oh : ptrofs)
    (k : int) : temp_env :=
  PTree.set _k (Vint k) (PTree.set _h (Vptr bh oh) (PTree.set _g (Vint g) (PTree.set _f (Vint f)
    (PTree.set _e (Vint e) (PTree.set _d (Vptr bd od) (PTree.set _c (Vint c) (PTree.set _b (Vint b)
      (PTree.set _a (Vint a) (create_undef_temps (fn_temps f_Round)))))))))).

Lemma sha_helper_call1 e le m t fid f x v :
  Genv.find_symbol (Clight.genv_genv sha_ge) fid = Some (sha_symbol_block fid) ->
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block fid) Ptrofs.zero) = Some (Internal f) ->
  type_of_fundef (Internal f) = Tfunction (Tcons tuint Tnil) tuint cc_default ->
  e!fid = None -> forall a, eval_expr sha_ge e le m a (Vint x) -> typeof a = tuint ->
  Clight2.eval_funcall sha_ge m (Internal f) [Vint x] E0 m (Vint v) ->
  Clight2.exec_stmt sha_ge e le m
    (Scall (Some t) (Evar fid (Tfunction (Tcons tuint Tnil) tuint cc_default)) [a]) E0
    (PTree.set t (Vint v) le) m Out_normal.
Proof.
  intros Hs Hf Hty He a Ha Hta Hcall.
  change (PTree.set t (Vint v) le) with (set_opttemp (Some t) (Vint v) le).
  eapply exec_Scall with (vf := Vptr (sha_symbol_block fid) Ptrofs.zero) (vargs := [Vint x]) (f := Internal f).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact Hs]|apply deref_loc_reference; reflexivity].
  - eapply eval_Econs; [exact Ha|rewrite Hta; reflexivity|apply eval_Enil].
  - exact Hf.
  - exact Hty.
  - exact Hcall.
Qed.

Lemma sha_helper_call3 e le m t fid f x y z v :
  Genv.find_symbol (Clight.genv_genv sha_ge) fid = Some (sha_symbol_block fid) ->
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block fid) Ptrofs.zero) = Some (Internal f) ->
  type_of_fundef (Internal f) = Tfunction (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tuint cc_default ->
  e!fid = None -> forall a b c,
  eval_expr sha_ge e le m a (Vint x) -> typeof a = tuint ->
  eval_expr sha_ge e le m b (Vint y) -> typeof b = tuint ->
  eval_expr sha_ge e le m c (Vint z) -> typeof c = tuint ->
  Clight2.eval_funcall sha_ge m (Internal f) [Vint x; Vint y; Vint z] E0 m (Vint v) ->
  Clight2.exec_stmt sha_ge e le m
    (Scall (Some t) (Evar fid (Tfunction (Tcons tuint (Tcons tuint (Tcons tuint Tnil))) tuint cc_default))
      [a; b; c]) E0 (PTree.set t (Vint v) le) m Out_normal.
Proof.
  intros Hs Hf Hty He a b c Ha Hta Hb Htb Hc Htc Hcall.
  change (PTree.set t (Vint v) le) with (set_opttemp (Some t) (Vint v) le).
  eapply exec_Scall with (vf := Vptr (sha_symbol_block fid) Ptrofs.zero)
    (vargs := [Vint x; Vint y; Vint z]) (f := Internal f).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact Hs]|apply deref_loc_reference; reflexivity].
  - eapply eval_Econs; [exact Ha|rewrite Hta; reflexivity|].
    eapply eval_Econs; [exact Hb|rewrite Htb; reflexivity|].
    eapply eval_Econs; [exact Hc|rewrite Htc; reflexivity|apply eval_Enil].
  - exact Hf.
  - exact Hty.
  - exact Hcall.
Qed.

Theorem eval_sha_Round m a b c bd od e f g bh oh k d h :
  Mem.load Mint32 m bd (Ptrofs.unsigned od) = Some (Vint d) ->
  Mem.load Mint32 m bh (Ptrofs.unsigned oh) = Some (Vint h) ->
  Mem.valid_access m Mint32 bd (Ptrofs.unsigned od) Writable ->
  Mem.valid_access m Mint32 bh (Ptrofs.unsigned oh) Writable ->
  exists md m',
    Mem.store Mint32 m bd (Ptrofs.unsigned od) (Vint (Int.add d (c_T1 h e f g k))) = Some md /\
    Mem.store Mint32 md bh (Ptrofs.unsigned oh) (Vint (Int.add (c_T1 h e f g k) (c_T2 a b c))) = Some m' /\
    Clight2.eval_funcall sha_ge m (Internal f_Round)
      [Vint a; Vint b; Vint c; Vptr bd od; Vint e; Vint f; Vint g; Vptr bh oh; Vint k] E0 m' Vundef.
Proof.
  intros HLd HLh PWd PWh.
  destruct (Mem.valid_access_store m Mint32 bd (Ptrofs.unsigned od)
    (Vint (Int.add d (c_T1 h e f g k))) PWd) as [md SD].
  assert (PWh' : Mem.valid_access md Mint32 bh (Ptrofs.unsigned oh) Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store md Mint32 bh (Ptrofs.unsigned oh)
    (Vint (Int.add (c_T1 h e f g k) (c_T2 a b c))) PWh') as [m' SH].
  exists md, m'. split; [exact SD|]. split; [exact SH|].
  set (l0 := round_le a b c bd od e f g bh oh k).
  set (l1 := PTree.set _t'1 (Vint (c_Sigma1 e)) l0).
  set (l2 := PTree.set _t'2 (Vint (c_Ch e f g)) l1).
  set (l3 := PTree.set _t'6 (Vint h) l2).
  set (l4 := PTree.set _t1 (Vint (c_T1 h e f g k)) l3).
  set (l5 := PTree.set _t'3 (Vint (c_Sigma0 a)) l4).
  set (l6 := PTree.set _t'4 (Vint (c_Maj a b c)) l5).
  set (l7 := PTree.set _t2 (Vint (c_T2 a b c)) l6).
  set (l8 := PTree.set _t'5 (Vint d) l7).
  eapply eval_funcall_internal with (e := empty_env) (le1 := l0) (m1 := m) (le2 := l8) (m2 := m')
    (out := Out_normal).
  - apply function_entry2_intro.
    + apply list_norepet_nil.
    + repeat constructor; simpl; intuition discriminate.
    + intros x y HX HY Hxy. cbn in HX, HY.
      repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
        first [contradiction | vm_compute in Hxy; discriminate | congruence].
    + apply alloc_variables_nil.
    + reflexivity.
  - cbn [f_Round fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := l4).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := l2).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := l1).
        -- eapply sha_helper_call1 with (f := f_Sigma1) (x := e);
             [exact sha_Sigma1_symbol|exact sha_Sigma1_funct|reflexivity|reflexivity|
              apply eval_Etempvar; reflexivity|reflexivity|apply eval_sha_Sigma1].
        -- eapply sha_helper_call3 with (f := f_Ch) (x := e) (y := f) (z := g);
             [exact sha_Ch_symbol|exact sha_Ch_funct|reflexivity|reflexivity|
              apply eval_Etempvar; reflexivity|reflexivity|
              apply eval_Etempvar; reflexivity|reflexivity|
              apply eval_Etempvar; reflexivity|reflexivity|apply eval_sha_Ch].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := l3).
        -- constructor. eapply eval_Elvalue.
           ++ apply eval_Ederef. apply eval_Etempvar. reflexivity.
           ++ eapply deref_loc_value; [reflexivity|exact HLh].
        -- constructor.
           assert (Hv : c_T1 h e f g k =
             Int.add (Int.add (Int.add (Int.mul (Int.repr 1) h) (c_Sigma1 e)) (c_Ch e f g)) k)
             by (rewrite int_mul1; reflexivity).
           rewrite Hv. sha_ev.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := l7).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := l6).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := l5).
           ++ eapply sha_helper_call1 with (f := f_Sigma0) (x := a);
                [exact sha_Sigma0_symbol|exact sha_Sigma0_funct|reflexivity|reflexivity|
                 apply eval_Etempvar; reflexivity|reflexivity|apply eval_sha_Sigma0].
           ++ eapply sha_helper_call3 with (f := f_Maj) (x := a) (y := b) (z := c);
                [exact sha_Maj_symbol|exact sha_Maj_funct|reflexivity|reflexivity|
                 apply eval_Etempvar; reflexivity|reflexivity|
                 apply eval_Etempvar; reflexivity|reflexivity|
                 apply eval_Etempvar; reflexivity|reflexivity|apply eval_sha_Maj].
        -- constructor.
           assert (Hv : c_T2 a b c = Int.add (Int.mul (Int.repr 1) (c_Sigma0 a)) (c_Maj a b c))
             by (rewrite int_mul1; reflexivity).
           rewrite Hv. sha_ev.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := md) (le1 := l8).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := l8).
           ++ constructor. eapply eval_Elvalue.
              ** apply eval_Ederef. apply eval_Etempvar. reflexivity.
              ** eapply deref_loc_value; [reflexivity|exact HLd].
           ++ eapply exec_Sassign with (v2 := Vint (Int.add d (c_T1 h e f g k)))
                (v := Vint (Int.add d (c_T1 h e f g k))).
              ** apply eval_Ederef. apply eval_Etempvar. reflexivity.
              ** assert (Hv : Int.add d (c_T1 h e f g k) =
                   Int.add (Int.mul (Int.repr 1) d) (c_T1 h e f g k)) by (rewrite int_mul1; reflexivity).
                 rewrite Hv. sha_ev.
              ** reflexivity.
              ** eapply assign_loc_value; [reflexivity|exact SD].
        -- eapply exec_Sassign with (v2 := Vint (Int.add (c_T1 h e f g k) (c_T2 a b c)))
             (v := Vint (Int.add (c_T1 h e f g k) (c_T2 a b c))).
           ++ apply eval_Ederef. apply eval_Etempvar. reflexivity.
           ++ assert (Hv : Int.add (c_T1 h e f g k) (c_T2 a b c) =
                Int.add (Int.mul (Int.repr 1) (c_T1 h e f g k)) (c_T2 a b c)) by (rewrite int_mul1; reflexivity).
              rewrite Hv. sha_ev.
           ++ reflexivity.
           ++ eapply assign_loc_value; [reflexivity|exact SH].
  - cbn. reflexivity.
  - reflexivity.
Qed.
