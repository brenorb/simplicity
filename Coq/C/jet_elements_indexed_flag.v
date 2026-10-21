(** Indexed Elements frame wrapper with a parameterized branch-result
    temporary. The concrete issuance_hash uses t'3, unlike the older getters.
    C functions and the existing t'2 wrapper are unchanged. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_frame_layout C.jets_elements C.jet_elements_linkage.
Require C.jets.
Require Import C.jet_elements_field_eval C.jet_elements_transport C.jet_elements_call C.jet_elements_wrapper.
Require Import C.jet_elements_indexed_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Set Default Timeout 15.

Definition elements_indexed_cond_flag (bp tp cp : ident) (countfield : ident) : statement :=
  Ssequence
    (Sset tp (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
      _tx (tptr (Tstruct _elementsTransaction noattr))))
    (Ssequence
      (Sset cp (Efield (Ederef (Etempvar tp (tptr (Tstruct _elementsTransaction noattr)))
        (Tstruct _elementsTransaction noattr)) countfield tulong))
      (Scall (Some bp)
        (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
        [Etempvar _dst (tptr (Tstruct _frameItem noattr));
         Ebinop Olt (Etempvar _i tulong) (Etempvar cp tulong) tint])).

Definition elements_indexed_rest_flag (bp tp cp countfield : ident) (then_s else_s : statement) : statement :=
  Ssequence elements_indexed_head
    (Ssequence
      (Ssequence (elements_indexed_cond_flag bp tp cp countfield) (Sifthenelse (Etempvar bp tbool) then_s else_s))
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))).

Lemma elements_indexed_rest_flag_default tp cp countfield then_s else_s :
  elements_indexed_rest_flag _t'2 tp cp countfield then_s else_s =
  elements_indexed_rest tp cp countfield then_s else_s.
Proof. reflexivity. Qed.

Section Indexed.
Variables bp tp cp : ident.
Hypothesis Hbp : bp <> _env /\ bp <> _dst /\ bp <> _i /\ bp <> _t'1.
Hypothesis Htp : tp <> _env /\ tp <> _dst /\ tp <> _i /\ tp <> _t'1 /\ tp <> bp /\ tp <> cp.
Hypothesis Hcp : cp <> _env /\ cp <> _dst /\ cp <> _i /\ cp <> _t'1 /\ cp <> bp.

Ltac flag_gso := rewrite PTree.gso by (first [assumption | apply not_eq_sym; assumption | discriminate | (intro; congruence)]).

Lemma exec_elements_indexed_rest_flag e le0 countfield cdelta then_s else_s mc mr mb
    be ebase bt txbase bl bd dbase r nI (Post : mem -> Prop) :
  e!_simplicity_read32 = None -> e!_writeBit = None ->
  e!_src = Some (bl, Tstruct _frameItem noattr) ->
  le0!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
  le0!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall elements_ge mc (Internal jets.f_simplicity_read32)
    [Vptr bl (Ptrofs.repr 0)] E0 mr (Vlong r) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  0 <= txbase -> 0 <= cdelta -> txbase + cdelta + 8 <= Ptrofs.max_unsigned ->
  elements_field_at _elementsTransaction countfield cdelta ->
  Mem.load Mptr mr be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mint64 mr bt (txbase + cdelta) = Some (Vlong nI) ->
  Clight2.eval_funcall elements_ge mr (Internal jets.f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (if Int64.ltu r nI then Int.one else Int.zero)] E0 mb
    (Vint (if Int64.ltu r nI then Int.one else Int.zero)) ->
  (forall le', le'!_i = Some (Vlong r) -> le'!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
    le'!_env = Some (Vptr be (Ptrofs.repr ebase)) -> Int64.ltu r nI = true ->
    exists le'' me, Clight2.exec_stmt elements_ge e le' mb then_s E0 le'' me Out_normal /\ Post me) ->
  (forall le', le'!_i = Some (Vlong r) -> le'!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
    le'!_env = Some (Vptr be (Ptrofs.repr ebase)) -> Int64.ltu r nI = false ->
    exists le'' me, Clight2.exec_stmt elements_ge e le' mb else_s E0 le'' me Out_normal /\ Post me) ->
  exists le1 me,
    Clight2.exec_stmt elements_ge e le0 mc (elements_indexed_rest_flag bp tp cp countfield then_s else_s)
      E0 le1 me elements_returned_one /\ Post me.
Proof.
  intros Hrd Hwb Hsrc HEnv HDst Hread He0 He1 Ht0 Hc0 HcM HF Hld Hcnt Hwrite HThen HElse.
  destruct Hbp as (Hbp1 & Hbp2 & Hbp3 & Hbp4).
  destruct Htp as (Htp1 & Htp2 & Htp3 & Htp4 & Htp5 & Htp6).
  destruct Hcp as (Hcp1 & Hcp2 & Hcp3 & Hcp4 & Hcp5).
  set (le1 := PTree.set _i (Vlong r) (PTree.set _t'1 (Vlong r) le0)).
  set (le2 := PTree.set tp (Vptr bt (Ptrofs.repr txbase)) le1).
  set (le3 := PTree.set cp (Vlong nI) le2).
  set (le4 := PTree.set bp (Vint (if Int64.ltu r nI then Int.one else Int.zero)) le3).
  assert (Hi4 : le4!_i = Some (Vlong r)).
  { unfold le4, le3, le2, le1. flag_gso. flag_gso. flag_gso. apply PTree.gss. }
  assert (Hd4 : le4!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold le4, le3, le2, le1. flag_gso. flag_gso. flag_gso. flag_gso. flag_gso. exact HDst. }
  assert (He4 : le4!_env = Some (Vptr be (Ptrofs.repr ebase))).
  { unfold le4, le3, le2, le1. flag_gso. flag_gso. flag_gso. flag_gso. flag_gso. exact HEnv. }
  assert (Hbranch : exists le'' me, Clight2.exec_stmt elements_ge e le4 mb
    (if Int64.ltu r nI then then_s else else_s) E0 le'' me Out_normal /\ Post me).
  { destruct (Int64.ltu r nI) eqn:Hb; [apply HThen|apply HElse]; try assumption; reflexivity. }
  destruct Hbranch as (lef & me & HBr & HPost).
  assert (HHead : Clight2.exec_stmt elements_ge e le0 mc elements_indexed_head E0 le1 mr Out_normal).
  { unfold elements_indexed_head.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := PTree.set _t'1 (Vlong r) le0).
    - eapply exec_elements_helper_call with (id := _simplicity_read32) (f := jets.f_simplicity_read32)
        (vargs := [Vptr bl Ptrofs.zero]) (vres := Vlong r).
      + helper_in.
      + exact Hrd.
      + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact Hsrc|reflexivity|apply eval_Enil].
      + reflexivity.
      + exact Hread.
    - apply exec_set. apply eval_Etempvar. apply PTree.gss. }
  assert (HTx : Clight2.exec_stmt elements_ge e le1 mr
    (Sset tp (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
      _tx (tptr (Tstruct _elementsTransaction noattr)))) E0 le2 mr Out_normal).
  { apply exec_set.
    eapply eval_elements_field_value with (sid := _txEnv) (delta := 0) (chunk := Mptr).
    - reflexivity.
    - exact elements_txEnv_tx.
    - reflexivity.
    - apply eval_elements_deref_struct. unfold le1. flag_gso. flag_gso. exact HEnv.
    - rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact Hld]. }
  assert (HCnt : Clight2.exec_stmt elements_ge e le2 mr
    (Sset cp (Efield (Ederef (Etempvar tp (tptr (Tstruct _elementsTransaction noattr)))
      (Tstruct _elementsTransaction noattr)) countfield tulong)) E0 le3 mr Out_normal).
  { apply exec_set.
    eapply eval_elements_field_value with (sid := _elementsTransaction) (delta := cdelta) (chunk := Mint64).
    - reflexivity.
    - exact HF.
    - reflexivity.
    - apply eval_elements_deref_struct. unfold le2. apply PTree.gss.
    - rewrite elements_ptr_add_repr by (clear - Ht0 Hc0 HcM; lia).
      apply elements_loadv_repr; [clear - Ht0 Hc0 HcM; lia|exact Hcnt]. }
  assert (HWB : Clight2.exec_stmt elements_ge e le3 mr
    (Scall (Some bp)
      (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
      [Etempvar _dst (tptr (Tstruct _frameItem noattr));
       Ebinop Olt (Etempvar _i tulong) (Etempvar cp tulong) tint]) E0 le4 mb Out_normal).
  { eapply exec_elements_helper_call with (id := _writeBit) (f := jets.f_writeBit)
      (vargs := [Vptr bd (Ptrofs.repr dbase); Vint (if Int64.ltu r nI then Int.one else Int.zero)])
      (vres := Vint (if Int64.ltu r nI then Int.one else Int.zero)).
    - helper_in.
    - exact Hwb.
    - eapply eval_Econs.
      + apply eval_Etempvar. unfold le3, le2, le1. flag_gso. flag_gso. flag_gso. flag_gso. exact HDst.
      + reflexivity.
      + eapply eval_Econs.
        * eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vlong nI).
          -- apply eval_Etempvar. unfold le3, le2, le1. flag_gso. flag_gso. apply PTree.gss.
          -- apply eval_Etempvar. unfold le3. apply PTree.gss.
          -- exact (elements_ltu_cmp r nI mr).
        * apply elements_bool_cast.
        * apply eval_Enil.
    - reflexivity.
    - exact Hwrite. }
  eexists. eexists. split; [|exact HPost].
  unfold elements_indexed_rest_flag.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le1); [exact HHead|].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := lef); [|apply exec_Sreturn_some, eval_Econst_int].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le4).
  - unfold elements_indexed_cond_flag.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le2); [exact HTx|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le3); [exact HCnt|exact HWB].
  - eapply exec_Sifthenelse with (v1 := Vint (if Int64.ltu r nI then Int.one else Int.zero))
      (b := Int64.ltu r nI).
    + apply eval_Etempvar. unfold le4. apply PTree.gss.
    + destruct (Int64.ltu r nI); reflexivity.
    + exact HBr.
Qed.
End Indexed.
