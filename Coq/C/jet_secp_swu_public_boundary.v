(** Exact SWU public entry and source-copy environment adapter. Reuse the
    existing three-object allocation/copy facts, without changing the AST. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_decompress_public_entry C.jet_secp_decompress_public_prepare
  C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition swu_public_env bl bt bp : env := PTree.set _ge (bp,Tstruct __6121 noattr)
  (PTree.set _t (bt,Tstruct __5467 noattr) (PTree.set _src (bl,Tstruct _frameItem noattr) empty_env)).
Definition swu_public_temps v_env bd base bs sbase : temp_env := PTree.set _env v_env
  (PTree.set _src (Vptr bs (Ptrofs.repr sbase)) (PTree.set _dst (Vptr bd (Ptrofs.repr base))
    (create_undef_temps (fn_temps f_simplicity_swu)))).
Lemma swu_public_ok : fn_okb f_simplicity_swu=true.
Proof. reflexivity. Qed.
Lemma swu_public_entry v_env m ma mb mc bl bt bp bd base bs sbase :
  Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 40=(mb,bt) -> Mem.alloc mb 0 88=(mc,bp) ->
  function_entry2 secp_ge f_simplicity_swu
    [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m
    (swu_public_env bl bt bp) (swu_public_temps v_env bd base bs sbase) mc.
Proof.
  intros A B C;destruct (fn_okb_true _ swu_public_ok) as (NP & NV & Distinct).
  constructor;[exact NP|exact NV|exact Distinct| |reflexivity].
  eapply alloc_variables_cons with (m1:=ma) (b1:=bl);[exact A|].
  eapply alloc_variables_cons with (m1:=mb) (b1:=bt);[exact B|].
  eapply alloc_variables_cons with (m1:=mc) (b1:=bp);[exact C|constructor].
Qed.
Lemma swu_copy_environment le m mf bl bt bp :
  Clight2.exec_stmt secp_ge (decompress_public_env bl bt bp) le m decompress_public_copy E0 le mf Out_normal ->
  Clight2.exec_stmt secp_ge (swu_public_env bl bt bp) le m decompress_public_copy E0 le mf Out_normal.
Proof.
  intro Run;inversion Run;subst.
  match goal with Loc:eval_lvalue _ _ _ _ (Evar _src _) _ _ _ |- _ =>
    inversion Loc;subst end.
  - change (Some (bl,Tstruct _frameItem noattr)=Some (loc,Tstruct _frameItem noattr)) in H9.
    injection H9 as <-.
    eapply exec_Sassign with (v2:=v2) (v:=v).
    + apply eval_Evar_local;reflexivity.
    + inversion H2;subst.
      * apply eval_Etempvar;assumption.
      * match goal with Impossible:eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion Impossible end.
    + exact H6.
    + exact H7.
  - change (Some (bl,Tstruct _frameItem noattr)=None) in H3;discriminate H3.
Qed.
Lemma swu_copy_readonly e le m mf :
  Clight2.exec_stmt secp_ge e le m decompress_public_copy E0 le mf Out_normal -> readonly_preserved m mf.
Proof. intro Run;inversion Run;subst;eapply assign_preserved;eassumption. Qed.

Lemma swu_public_blocks bl bt bp : blocks_of_env secp_ge (swu_public_env bl bt bp)=
  [(bp,0,88);(bl,0,16);(bt,0,40)].
Proof. reflexivity. Qed.
Lemma swu_free_public_locals m bl bt bp : bt<>bl -> bp<>bl -> bt<>bp ->
  Mem.range_perm m bl 0 16 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable ->
  Mem.range_perm m bp 0 88 Cur Freeable -> exists mf,
  Mem.free_list m (blocks_of_env secp_ge (swu_public_env bl bt bp))=Some mf /\
  lframe (fun b _=>b<>bt /\ b<>bp /\ b<>bl) m mf.
Proof.
  intros TL PL TP FL FT FP.
  destruct (free_list_exists [(bp,0,88);(bl,0,16);(bt,0,40)] m) as (mf & Free & Unchanged).
  - cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi [Same | [Same | [Same | Empty] ]];
      [inversion Same;subst;exact FP|inversion Same;subst;exact FL|inversion Same;subst;exact FT|contradiction].
  - exists mf;split;[rewrite swu_public_blocks;exact Free|].
    eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
    intros b pos [NT [NP NL]] Valid;cbn;intuition congruence.
Qed.
