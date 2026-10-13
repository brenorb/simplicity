(** Actual statement execution with the already-proved shift64 helper table. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_shift64_executor.
Require Import C.jet_sx_compact.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Theorem compact_stmt_shift64_normal fuel ve st stmt st' :
  compact_stmt (genv_cenv secp_ge) [] secp_shift64_table fuel ve st stmt =
    Some (RDone st' ONormal) ->
  forall rho beta e le m,
    rep rho beta (sregs st) m -> tmatch rho beta (stemps st) le -> ematch beta ve e ->
    exists le' m',
      Clight2.exec_stmt secp_ge e le m stmt E0 le' m' Out_normal /\
      rep rho beta (sregs st') m' /\ tmatch rho beta (stemps st') le' /\
      map rshape (sregs st') = map rshape (sregs st) /\
      lframe (fun b ofs => ~ foot beta (map rshape (sregs st)) b ofs) m m'.
Proof.
  intros H rho beta e le m Hrep Htm Hem.
  assert (Hstable : forall (rho : nat -> int64) (log : list event) (m m' : mem),
    True -> lframe (fun (_ : block) (_ : Z) => False) m m' -> True) by auto.
  assert (Hvalid : forall (rho : nat -> int64) (log : list event) (m : mem) b,
    True -> False -> Mem.valid_block m b) by contradiction.
  destruct (compact_stmt_sound secp_ge [] secp_shift64_table
    (fun _ _ => True) (fun _ _ _ => True) (fun _ => False)
    Hstable Hvalid secp_shift64_table_correct fuel
    ve st stmt (RDone st' ONormal) H rho beta e le m Hrep Htm Hem)
    as (le' & m' & out & Hex & Hpost).
  - split; intros; discriminate.
  - intros r _ [].
  - exact I.
  - apply Forall_forall; intros; exact I.
  - destruct Hpost as (HR & HT & HO & HS & HI & HF).
    cbn [rsel fst snd] in HR,HT,HO,HS.
    destruct out; try contradiction.
    exists le',m'; split; [exact Hex|]. split; [exact HR|]. split; [exact HT|].
    split; [exact HS|]. eapply lframe_implies; [exact HF|].
    intros b ofs Hf Hvblock; split; [exact Hvblock|]. split; [exact Hf|tauto].
Qed.
