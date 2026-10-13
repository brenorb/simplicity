(** Actual original multiply-accumulate, including its temporary allocation
    and freeing through function entry/return. No helper-call premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_sx_pure C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_umul128_exec C.jet_secp_umul128_numeric C.jet_secp_u128_mul_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition u128_accum_mul_initial_regs : list region :=
  [mkreg (u64_cells 0 [XLv 2; XLv 3]) true (Some 16)].
Definition u128_accum_mul_run : option res :=
  xfun (genv_cenv secp_ge) [] (int_table u128_mul_functions) 250 f_secp256k1_u128_accum_mul
    [XP 0 0; XLv 0; XLv 1] u128_accum_mul_initial_regs [] 4.
Definition u128_accum_mul_tree := Eval vm_compute in u128_accum_mul_run.
Definition u128_accum_mul_state : sstate :=
  match u128_accum_mul_tree with Some (RDone state _) => state
  | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition accum_mul_lo := XLb Badd (XLv 2) umul128_lo.
Definition accum_mul_hi := XLb Badd (XLv 3)
  (XLb Badd umul128_hi (XI2L Signed (XLcmp Clt Unsigned accum_mul_lo umul128_lo))).

Lemma u128_accum_mul_run_eq : u128_accum_mul_run = Some (RDone u128_accum_mul_state ONormal).
Proof. reflexivity. Qed.
Lemma u128_accum_mul_return : (stemps u128_accum_mul_state)!1%positive = None.
Proof. reflexivity. Qed.
Lemma u128_accum_mul_output : sregs u128_accum_mul_state =
  [mkreg (u64_cells 0 [accum_mul_lo; accum_mul_hi]) true (Some 16)].
Proof. reflexivity. Qed.
Lemma u128_accum_mul_log_nil : slog u128_accum_mul_state = [].
Proof. reflexivity. Qed.

Local Opaque u128_accum_mul_state.
Theorem eval_u128_accum_mul_owned rho layout m :
  rep rho layout u128_accum_mul_initial_regs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_u128_accum_mul)
      [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0));
       Vlong (rho 0%nat); Vlong (rho 1%nat)] E0 mf Vundef /\
    rep rho layout [mkreg (u64_cells 0 [accum_mul_lo; accum_mul_hi]) true (Some 16)] mf /\
    lframe (fun b ofs => ~ foot layout (map rshape u128_accum_mul_initial_regs) b ofs) m mf.
Proof.
  intro HRep.
  destruct (xfun_pure secp_ge u128_mul_functions u128_mul_functions_ok 250
    f_secp256k1_u128_accum_mul [XP 0 0; XLv 0; XLv 1] u128_accum_mul_initial_regs 4
    (RDone u128_accum_mul_state ONormal) u128_accum_mul_run_eq eq_refl rho layout m HRep)
    as (mf & vres & HCall & HFinal & HReturn & HShape & HFrame).
  cbn [rsel fst] in HFinal, HReturn.
  rewrite u128_accum_mul_return in HReturn; subst vres.
  rewrite u128_accum_mul_output in HFinal.
  change (map (den rho (lay layout)) [XP 0 0; XLv 0; XLv 1]) with
    [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0 + 0));
     Vlong (rho 0%nat); Vlong (rho 1%nat)] in HCall.
  rewrite Z.add_0_r in HCall.
  exists mf; split; [exact HCall|]; split; [exact HFinal|exact HFrame].
Qed.
