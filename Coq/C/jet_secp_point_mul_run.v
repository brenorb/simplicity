(** Original in-place fe_mul on a coordinate inside an owned point.  The
    128-byte ownership stays with the point, including at offsets 40/80.
    Fresh u128 words are justified by proved actual-C helper oracles. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values Globalenvs.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_pure C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_point_write_run.
Require Import C.jet_secp_u128_word_oracle C.jet_secp_u128_word_shift C.jet_secp_field_mul_word_model.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition point_mul_table : list (ident * fentry) :=
  [(_secp256k1_fe_mul_inner, FInt f_secp256k1_fe_mul_inner);
   (_secp256k1_u128_mul, FOra f_secp256k1_u128_mul orc_mul);
   (_secp256k1_u128_accum_mul, FOra f_secp256k1_u128_accum_mul orc_acc);
   (_secp256k1_u128_accum_u64, FOra f_secp256k1_u128_accum_u64 orc_add64);
   (_secp256k1_u128_rshift, FOra f_secp256k1_u128_rshift orc_shr);
   (_secp256k1_u128_to_u64, FInt f_secp256k1_u128_to_u64)].

Lemma point_mul_table_ok id ent : flookup point_mul_table id = Some ent ->
  (exists b, Genv.find_symbol secp_ge id = Some b /\
             Genv.find_funct_ptr secp_ge b = Some (Internal (fentry_fd ent))) /\
  match ent with FInt _ => True
  | FOra fd o => oracle_ok secp_ge u128_evok u128_inv u128_ext fd o end.
Proof.
  intros H; cbn [point_mul_table flookup] in H.
  repeat match type of H with
  | (if Pos.eqb ?a id then _ else _) = _ =>
      let E := fresh "E" in destruct (Pos.eqb a id) eqn:E;
      [apply Pos.eqb_eq in E; subst id; inversion H; subst ent; clear H|]
  end; try discriminate.
  all: split; [apply secp_pure_ok; unfold secp_pure; repeat (first [left; reflexivity|right])|].
  all: first [exact I|exact orc_mul_ok|exact orc_acc_ok|exact orc_add64_ok|exact orc_shr_ok].
Qed.

Definition point_mul_regs k : list region :=
  [mkreg (u64_cells (point_coordinate_offset k) (vars5 0)) true (Some 128);
   free_region (fe_reg (vars5 5)) 40].
Definition point_mul_args k :=
  [XP 0 (point_coordinate_offset k);XP 0 (point_coordinate_offset k);XP 1 0].
Definition point_mul_run k := xfun (genv_cenv secp_ge) [] point_mul_table 400
  f_secp256k1_fe_mul (point_mul_args k) (point_mul_regs k) [] 10.
Definition point_mul_tree := Eval vm_compute in fun k => match k with
  | PointX => point_mul_run PointX | PointY => point_mul_run PointY | PointZ => point_mul_run PointZ end.
Definition point_mul_state k := match point_mul_tree k with
  | Some (RDone st _) => st | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition point_mul_mask : sx := XLc (Int64.repr 4503599627370495).
Definition point_mul_out : list sx :=
  [XLb Band (XLv 52) point_mul_mask;XLb Band (XLv 66) point_mul_mask;
   XLb Band (XLv 82) point_mul_mask;XLb Band (XLv 90) point_mul_mask;
   XLb Badd (XLv 92) (XLb Band (XLb Band (XLv 36) point_mul_mask) (XLsh Hshru point_mul_mask 4))].
Definition point_mul_out_regs k : list region :=
  [mkreg (u64_cells (point_coordinate_offset k) point_mul_out) true (Some 128);
   free_region (fe_reg (vars5 5)) 40].

Lemma point_mul_run_eq k : point_mul_run k = Some (RDone (point_mul_state k) ONormal).
Proof. destruct k; timeout 10 (vm_compute; reflexivity). Qed.
Lemma point_mul_log_eq k : slog (point_mul_state k) = fe_mul_log.
Proof. destruct k; timeout 10 (vm_compute; reflexivity). Qed.
Lemma point_mul_out_eq k : sregs (point_mul_state k) = point_mul_out_regs k.
Proof. destruct k; timeout 10 (vm_compute; reflexivity). Qed.
Lemma point_mul_return k : (stemps (point_mul_state k))!1%positive = None.
Proof. destruct k; timeout 10 (vm_compute; reflexivity). Qed.

Local Opaque point_mul_state secp_ge.
Theorem eval_point_mul_symbolic k rho beta m :
  rep rho beta (point_mul_regs k) m -> Forall (u128_evok rho) fe_mul_log ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0 + point_coordinate_offset k));
       Vptr (blk beta 0) (Ptrofs.repr (bas beta 0 + point_coordinate_offset k));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
    rep rho beta (point_mul_out_regs k) mf /\
    lframe (fun b ofs => ~ foot beta (map rshape (point_mul_regs k)) b ofs) m mf.
Proof.
  intros HR HSol.
  destruct (xfun_top_sound secp_ge [] point_mul_table u128_evok u128_inv u128_ext
    ltac:(intros; exact I) ltac:(intros; contradiction) point_mul_table_ok
    400 f_secp256k1_fe_mul (point_mul_args k) (point_mul_regs k) [] 10
    (RDone (point_mul_state k) ONormal) (point_mul_run_eq k) rho beta m HR)
    as (mf & vres & HC & HP & HV & HS & _ & HF).
  - split; intros; discriminate.
  - intros r _ HE; exact HE.
  - exact I.
  - cbn [rsel fst]; rewrite point_mul_log_eq; exact HSol.
  - cbn [rsel fst] in HP, HV, HS; rewrite point_mul_return in HV; subst vres.
    rewrite point_mul_out_eq in HP.
    change (map (den rho (lay beta)) (point_mul_args k)) with
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0 + point_coordinate_offset k));
       Vptr (blk beta 0) (Ptrofs.repr (bas beta 0 + point_coordinate_offset k));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1 + 0))] in HC.
    rewrite Z.add_0_r in HC.
    exists mf; split; [exact HC|]; split; [exact HP|].
    eapply lframe_implies; [exact HF|].
    intros b ofs HOutside HValid; split; [exact HValid|]; split; [exact HOutside|intros HE; exact HE].
Qed.
