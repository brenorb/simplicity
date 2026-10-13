(** Actual original unsigned multiplication helper on owned storage.
    This is execution infrastructure for scalar multiplication, not jet coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_sx_pure C.jet_secp_linkage C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition umul128_initial_regs : list region :=
  [mkreg (u64_cells 0 [XLv 2]) true (Some 8)].
Definition umul128_run : option res :=
  xfun (genv_cenv secp_ge) [] [] 100 f_secp256k1_umul128
    [XLv 0; XLv 1; XP 0 0] umul128_initial_regs [] 3.
Definition umul128_tree := Eval vm_compute in umul128_run.
Definition umul128_state : sstate :=
  match umul128_tree with Some (RDone state _) => state
  | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition mul_low32 x := XI2L Unsigned (XL2I x).
Definition umul128_ll := XLb Bmul (mul_low32 (XLv 0)) (mul_low32 (XLv 1)).
Definition umul128_lh := XLb Bmul (mul_low32 (XLv 0)) (XLsh Hshru (XLv 1) 32).
Definition umul128_hl := XLb Bmul (XLsh Hshru (XLv 0) 32) (mul_low32 (XLv 1)).
Definition umul128_hh := XLb Bmul (XLsh Hshru (XLv 0) 32) (XLsh Hshru (XLv 1) 32).
Definition umul128_mid := XLb Badd
  (XLb Badd (XLsh Hshru umul128_ll 32) (mul_low32 umul128_lh))
  (mul_low32 umul128_hl).
Definition umul128_lo := XLb Badd (XLsh Hshl umul128_mid 32) (mul_low32 umul128_ll).
Definition umul128_hi := XLb Badd
  (XLb Badd (XLb Badd umul128_hh (XLsh Hshru umul128_lh 32))
    (XLsh Hshru umul128_hl 32)) (XLsh Hshru umul128_mid 32).

Lemma umul128_run_eq : umul128_run = Some (RDone umul128_state ONormal).
Proof. reflexivity. Qed.
Lemma umul128_return : (stemps umul128_state)!1%positive = Some umul128_lo.
Proof. reflexivity. Qed.
Lemma umul128_output : sregs umul128_state =
  [mkreg (u64_cells 0 [umul128_hi]) true (Some 8)].
Proof. reflexivity. Qed.
Lemma umul128_log_nil : slog umul128_state = [].
Proof. reflexivity. Qed.

Local Opaque umul128_state.
Theorem eval_umul128_from_owned_region rho layout m :
  rep rho layout umul128_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_umul128)
      [Vlong (rho 0%nat); Vlong (rho 1%nat);
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf
      (den rho (lay layout) umul128_lo) /\
    rep rho layout [mkreg (u64_cells 0 [umul128_hi]) true (Some 8)] mf /\
    lframe (fun b ofs => ~ foot layout (map rshape umul128_initial_regs) b ofs) m mf.
Proof.
  intro HRep.
  destruct (xfun_pure secp_ge [] ltac:(intros id f H; contradiction) 100
    f_secp256k1_umul128 [XLv 0; XLv 1; XP 0 0] umul128_initial_regs 3
    (RDone umul128_state ONormal) umul128_run_eq eq_refl rho layout m HRep)
    as (mf & vres & HCall & HFinal & HReturn & HShape & HFrame).
  cbn [rsel fst] in HFinal, HReturn.
  rewrite umul128_return in HReturn; subst vres.
  rewrite umul128_output in HFinal.
  change (map (den rho (lay layout)) [XLv 0; XLv 1; XP 0 0]) with
    [Vlong (rho 0%nat); Vlong (rho 1%nat);
     Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0))] in HCall.
  rewrite Z.add_0_r in HCall.
  exists mf; split; [exact HCall|]; split; [exact HFinal|exact HFrame].
Qed.
