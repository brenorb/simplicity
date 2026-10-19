(** Actual original [secp256k1_fe_sqr] in place ([r = a]) on one owned field
    region, executed by the symbolic executor with [fe_sqr_inner] and
    [u128_to_u64] inlined and the proved 128-bit helper oracles. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values Globalenvs.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_pure C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_field_add_initial.
Require Import C.jet_parallel_fe_mul_oracle C.jet_parallel_fe_mul_shift C.jet_parallel_fe_mul_model C.jet_parallel_fe_mul_run C.jet_parallel_fe_sqr_model.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Definition fe_sqr_table : list (ident * fentry) :=
  [(_secp256k1_fe_sqr_inner, FInt f_secp256k1_fe_sqr_inner);
   (_secp256k1_u128_mul, FOra f_secp256k1_u128_mul orc_mul);
   (_secp256k1_u128_accum_mul, FOra f_secp256k1_u128_accum_mul orc_acc);
   (_secp256k1_u128_accum_u64, FOra f_secp256k1_u128_accum_u64 orc_add64);
   (_secp256k1_u128_rshift, FOra f_secp256k1_u128_rshift orc_shr);
   (_secp256k1_u128_to_u64, FInt f_secp256k1_u128_to_u64)].

Lemma fe_sqr_table_ok id ent : flookup fe_sqr_table id = Some ent ->
  (exists b, Genv.find_symbol secp_ge id = Some b /\
             Genv.find_funct_ptr secp_ge b = Some (Internal (fentry_fd ent))) /\
  match ent with FInt _ => True
  | FOra fd o => oracle_ok secp_ge u128_evok u128_inv u128_ext fd o end.
Proof.
  intros H. cbn [fe_sqr_table flookup] in H.
  repeat match type of H with
  | (if Pos.eqb ?a id then _ else _) = _ =>
      let E := fresh "E" in destruct (Pos.eqb a id) eqn:E;
      [apply Pos.eqb_eq in E; subst id; inversion H; subst ent; clear H|]
  end; try discriminate.
  all: split; [apply secp_pure_ok; in_pure|].
  all: first [exact I|exact orc_mul_ok|exact orc_acc_ok|exact orc_add64_ok|exact orc_shr_ok].
Qed.

Definition fe_sqr_regs : list region := [free_region (fe_reg (vars5 0)) 40].
Definition fe_sqr_run : option res :=
  xfun (genv_cenv secp_ge) [] fe_sqr_table 400 f_secp256k1_fe_sqr
    [XP 0 0; XP 0 0] fe_sqr_regs [] 5.
Definition fe_sqr_tree := Eval vm_compute in fe_sqr_run.
Definition fe_sqr_state : sstate :=
  match fe_sqr_tree with Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.

Definition fe_sqr_out : list sx :=
  [XLb Band (XLv 35) fm_M; XLb Band (XLv 45) fm_M; XLb Band (XLv 57) fm_M;
   XLb Band (XLv 65) fm_M;
   XLb Badd (XLv 67) (XLb Band (XLb Band (XLv 23) fm_M) (XLsh Hshru fm_M 4))].
Definition fe_sqr_out_regs : list region := [mkreg (u64_cells 0 fe_sqr_out) true (Some 40)].

Lemma fe_sqr_run_eq : fe_sqr_run = Some (RDone fe_sqr_state ONormal).
Proof. vm_compute. reflexivity. Qed.
Lemma fe_sqr_log_eq : slog fe_sqr_state = fe_sqr_log.
Proof. vm_compute. reflexivity. Qed.
Lemma fe_sqr_out_eq : sregs fe_sqr_state = fe_sqr_out_regs.
Proof. vm_compute. reflexivity. Qed.
Lemma fe_sqr_return : (stemps fe_sqr_state)!1%positive = None.
Proof. vm_compute. reflexivity. Qed.

Local Opaque fe_sqr_state.

Theorem eval_fe_sqr_owned rho beta m :
  rep rho beta fe_sqr_regs m -> Forall (u128_evok rho) fe_sqr_log ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0)); Vptr (blk beta 0) (Ptrofs.repr (bas beta 0))]
      E0 mf Vundef /\
    rep rho beta fe_sqr_out_regs mf /\
    lframe (fun b o => ~ foot beta (map rshape fe_sqr_regs) b o) m mf.
Proof.
  intros HRep HSol.
  destruct (xfun_top_sound secp_ge [] fe_sqr_table u128_evok u128_inv u128_ext
    ltac:(intros; exact I) ltac:(intros; contradiction) fe_sqr_table_ok
    400 f_secp256k1_fe_sqr [XP 0 0; XP 0 0] fe_sqr_regs [] 5
    (RDone fe_sqr_state ONormal) fe_sqr_run_eq rho beta m HRep)
    as (mf & vres & HCall & HFinal & HRet & HShape & _ & HFrame).
  - split; [intros id r ty H; discriminate|intros id r ty H; discriminate].
  - intros r _ HF; exact HF.
  - exact I.
  - cbn [rsel fst]. rewrite fe_sqr_log_eq. exact HSol.
  - cbn [rsel fst] in HFinal, HRet, HShape. rewrite fe_sqr_return in HRet. subst vres.
    rewrite fe_sqr_out_eq in HFinal.
    change (map (den rho (lay beta)) [XP 0 0; XP 0 0]) with
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0 + 0)); Vptr (blk beta 0) (Ptrofs.repr (bas beta 0 + 0))]
      in HCall.
    rewrite !Z.add_0_r in HCall.
    exists mf. split; [exact HCall|]. split; [exact HFinal|].
    eapply lframe_implies; [exact HFrame|]. intros b o HQ HV.
    split; [exact HV|]. split; [exact HQ|intros HF; exact HF].
Qed.
Print Assumptions eval_fe_sqr_owned.
