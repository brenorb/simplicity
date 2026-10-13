(* Actual scalar setter call in the reader's three-region context. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values Globalenvs.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_fe_b32 C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_symbolic_substitution.
Require Import C.jet_secp_frame.
Require Import C.jet_secp_fns.
Require Import C.jet_secp_scalar_reader_run C.jet_secp_scalar_set_b32_exec.
Require Import C.jet_secp_shift64_statement C.jet_secp_shift64_executor.
Require Import C.jet_secp_statement_prefix.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_reader_set_temps :=
  PTree.set jets_secp._overflow (XLc Int64.zero)
    (PTree.set jets_secp._b32 (XP 2 0) (PTree.set jets_secp._r (XP 0 0) (PTree.empty sx))).
Definition scalar_reader_set_initial bi edge :=
  mkst scalar_reader_set_temps (sregs (scalar_reader_state bi edge))
    (slog (scalar_reader_state bi edge)) 33.
Definition scalar_reader_set_run bi edge :=
  xstmt (genv_cenv secp_ge) [] secp_shift64_table 1000 []
    (scalar_reader_set_initial bi edge) scalar_set_prefix.
Definition scalar_reader_set_tree := Eval vm_compute in fun bi edge => scalar_reader_set_run bi edge.
Definition scalar_reader_set_state bi edge :=
  match scalar_reader_set_tree bi edge with Some (RDone state _) => state
  | _ => mkst (PTree.empty sx) [] [] 0 end.
Lemma scalar_reader_set_run_eq bi edge :
  scalar_reader_set_run bi edge = Some (RDone (scalar_reader_set_state bi edge) ONormal).
Proof. reflexivity. Qed.
Lemma scalar_reader_set_pointer bi edge :
  (stemps (scalar_reader_set_state bi edge))!jets_secp._overflow = Some (XLc Int64.zero).
Proof. reflexivity. Qed.
Definition scalar_reader_byte_shift n := XLv (S n).
Lemma scalar_reader_set_regions bi edge :
  sregs (scalar_reader_set_state bi edge) =
    [mkreg (map (cell_subst scalar_reader_byte_shift) (cells0 scalar_set_state)) true (Some 32);
     mkreg (mk_frame_cells (XA bi edge) (Int64.repr 256)) true (Some 16);
     mkreg (byte_cells 0 32 1) true (Some 32)].
Proof. reflexivity. Qed.
Definition scalar_reader_set_concrete_temps rho layout :=
  PTree.set jets_secp._overflow (den rho (lay layout) (XLc Int64.zero))
    (PTree.set jets_secp._b32 (den rho (lay layout) (XP 2 0))
      (PTree.set jets_secp._r (den rho (lay layout) (XP 0 0))
        (create_undef_temps (fn_temps f_secp256k1_scalar_set_b32)))).
Lemma scalar_reader_set_entry rho layout m :
  function_entry2 secp_ge f_secp256k1_scalar_set_b32
    (map (den rho (lay layout)) [XP 0 0; XP 2 0; XLc Int64.zero]) m
    empty_env (scalar_reader_set_concrete_temps rho layout) m.
Proof.
  constructor.
  - cbn; constructor.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy; cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in Hxy; discriminate|congruence].
  - constructor.
  - reflexivity.
Qed.
Lemma scalar_reader_set_tmatch rho layout :
  tmatch rho layout scalar_reader_set_temps (scalar_reader_set_concrete_temps rho layout).
Proof.
  unfold scalar_reader_set_temps, scalar_reader_set_concrete_temps.
  apply tmatch_set; apply tmatch_set; apply tmatch_set.
  intros id x H; rewrite PTree.gempty in H; discriminate.
Qed.
Local Opaque secp_ge xstmt scalar_reader_set_state scalar_set_prefix scalar_reader_set_initial.
Theorem eval_scalar_reader_set rho layout bi edge m :
  rep rho layout (sregs (scalar_reader_state bi edge)) m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_set_b32)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 2) (Ptrofs.repr (bas layout 2)); Vlong Int64.zero] E0 mf Vundef /\
    rep rho layout (sregs (scalar_reader_set_state bi edge)) mf /\
    lframe (fun b ofs => ~ foot layout (map rshape (sregs (scalar_reader_state bi edge))) b ofs) m mf.
Proof.
  intro HRep.
  pose proof (scalar_reader_set_run_eq bi edge) as HRun; unfold scalar_reader_set_run in HRun.
  destruct (xstmt_shift64_normal 1000 (scalar_reader_set_initial bi edge)
    scalar_set_prefix (scalar_reader_set_state bi edge) rho layout m
    (scalar_reader_set_concrete_temps rho layout) HRun HRep
    (scalar_reader_set_tmatch rho layout)) as [le [mf [HPrefix [HFinal [HTemp [_ HFrame]]]]]].
  assert (HNull : le!jets_secp._overflow = Some (Vlong Int64.zero)).
  { exact (HTemp jets_secp._overflow (XLc Int64.zero) (scalar_reader_set_pointer bi edge)). }
  exists mf; split.
  - assert (HArgs : map (den rho (lay layout)) [XP 0 0; XP 2 0; XLc Int64.zero] =
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vptr (blk layout 2) (Ptrofs.repr (bas layout 2)); Vlong Int64.zero]).
    { cbn [map den]; fold (blk layout 0) (bas layout 0) (blk layout 2) (bas layout 2).
      rewrite !Z.add_0_r; reflexivity. }
    rewrite <- HArgs.
    eapply eval_funcall_internal with (e := empty_env)
      (le1 := scalar_reader_set_concrete_temps rho layout) (le2 := le)
      (m1 := m) (m2 := mf) (out := Out_normal).
    + apply scalar_reader_set_entry.
    + rewrite scalar_set_body_exact; eapply exec_statement_prefix_then_last;
        [exact HPrefix|apply exec_scalar_set_null_suffix; exact HNull].
    + reflexivity.
    + reflexivity.
  - split; assumption.
Qed.
Definition scalar_reader_second :=
  match fn_body f_read_scalar with Ssequence _ second => second | _ => Sskip end.
Lemma scalar_reader_body_exact :
  fn_body f_read_scalar = Ssequence scalar_reader_first scalar_reader_second.
Proof. reflexivity. Qed.
Theorem exec_scalar_reader_second rho layout bi edge m e le :
  rep rho layout (sregs (scalar_reader_state bi edge)) m ->
  tmatch rho layout scalar_reader_temps le ->
  ematch layout scalar_reader_venv e ->
  exists mf,
    Clight2.exec_stmt secp_ge e le m scalar_reader_second E0 le mf Out_normal /\
    rep rho layout (sregs (scalar_reader_set_state bi edge)) mf /\
    lframe (fun b ofs => ~ foot layout (map rshape (sregs (scalar_reader_state bi edge))) b ofs) m mf.
Proof.
  intros HRep HTemps HEnv.
  destruct (eval_scalar_reader_set rho layout bi edge m HRep) as [mf [HCall [HFinal HFrame]]].
  destruct (secp_pure_ok jets_secp._secp256k1_scalar_set_b32 f_secp256k1_scalar_set_b32)
    as [b [HSymbol HFunction]].
  { unfold secp_pure; do 54 right; left; reflexivity. }
  assert (HGlobal : e!jets_secp._secp256k1_scalar_set_b32 = None).
  { exact (proj1 (HEnv jets_secp._secp256k1_scalar_set_b32)). }
  assert (HBuffer : e!jets_secp._buf = Some (blk layout 2, tarray tuchar 32)).
  { exact (proj1 (HEnv jets_secp._buf)). }
  assert (HBase : bas layout 2 = 0).
  { apply (proj2 (HEnv jets_secp._buf) 2%nat (tarray tuchar 32)); reflexivity. }
  assert (HR : le!jets_secp._r = Some (Vptr (blk layout 0) (Ptrofs.repr (bas layout 0)))).
  { pose proof (HTemps jets_secp._r (XP 0 0) eq_refl) as HR.
    cbn [den] in HR; fold (blk layout 0) (bas layout 0) in HR.
    rewrite Z.add_0_r in HR; exact HR. }
  exists mf; split; [|split; assumption].
  unfold scalar_reader_second; cbn [f_read_scalar fn_body].
  eapply exec_Scall with (optid := None) (vres := Vundef)
    (vf := Vptr b Ptrofs.zero)
    (f := Internal f_secp256k1_scalar_set_b32)
    (vargs := [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
      Vptr (blk layout 2) (Ptrofs.repr (bas layout 2)); Vlong Int64.zero]).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [exact HGlobal|exact HSymbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs with (v1 := Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))).
    + apply eval_Etempvar; exact HR.
    + reflexivity.
    + eapply eval_Econs with (v1 := Vptr (blk layout 2) (Ptrofs.repr (bas layout 2))).
      * rewrite HBase; change (Ptrofs.repr 0) with Ptrofs.zero.
      eapply eval_Elvalue.
        -- apply eval_Evar_local; exact HBuffer.
        -- apply deref_loc_reference; reflexivity.
      * reflexivity.
      * eapply eval_Econs with (v1 := Vlong Int64.zero).
        -- eapply eval_Ecast; [apply eval_Econst_int|reflexivity].
        -- reflexivity.
        -- constructor.
  - change (Genv.find_funct_ptr secp_ge b = Some (Internal f_secp256k1_scalar_set_b32)).
    exact HFunction.
  - reflexivity.
  - exact HCall.
Qed.
