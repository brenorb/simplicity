(** The compact executor with the already-proved original shift64 oracle. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_shift64_executor.
Require Import C.jet_sx_compact.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem compact_fun_shift64_sound fuel fd args regs nv result :
  compact_fun (genv_cenv secp_ge) [] secp_shift64_table fuel fd args regs [] nv = Some result ->
  forall rho beta m, rep rho beta regs m ->
  exists mf vres,
    Clight2.eval_funcall secp_ge m (Internal fd) (map (den rho (lay beta)) args) E0 mf vres /\
    rep rho beta (sregs (fst (rsel rho (lay beta) result))) mf /\
    match (stemps (fst (rsel rho (lay beta) result)))!1%positive with
    | Some x => vres = den rho (lay beta) x | None => vres = Vundef end /\
    map rshape (sregs (fst (rsel rho (lay beta) result))) = map rshape regs /\
    lframe (fun b ofs => ~ foot beta (map rshape regs) b ofs) m mf.
Proof.
  intros H rho beta m Hrep.
  assert (Hstable : forall (rho : nat -> int64) (log : list event) (m m' : mem),
    True -> lframe (fun (_ : block) (_ : Z) => False) m m' -> True) by auto.
  assert (Hvalid : forall (rho : nat -> int64) (log : list event) (m : mem) b,
    True -> False -> Mem.valid_block m b) by contradiction.
  destruct (xfun_sound secp_ge [] (fun _ _ => True) (fun _ _ _ => True) (fun _ => False)
    Hstable Hvalid _
    (compact_stmt_sound secp_ge [] secp_shift64_table (fun _ _ => True) (fun _ _ _ => True)
      (fun _ => False) Hstable Hvalid secp_shift64_table_correct fuel)
    fd args regs [] nv (PTree.empty sx) (Some 1%positive) result H rho beta m Hrep)
    as (mf & vres & Hcall & Hfinal & (v & Htemps & Hv) & Hnormal & Hshape & Hinv & Hframe).
  - split; intros; discriminate.
  - intros r _ [].
  - exact I.
  - apply Forall_forall; intros; exact I.
  - exists mf,vres; split; [exact Hcall|]. split; [exact Hfinal|]. split.
    + rewrite Htemps. destruct v as [x|]; unfold set_opt.
      * rewrite PTree.gss; exact Hv.
      * rewrite PTree.grs; exact Hv.
    + split; [exact Hshape|]. eapply lframe_implies; [exact Hframe|].
      intros b ofs Hf Hvblock; split; [exact Hvblock|]. split; [exact Hf|tauto].
Qed.
