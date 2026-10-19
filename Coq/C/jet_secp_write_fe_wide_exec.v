(** The unchanged C writer on general bounded limbs, including negation.
    All call/output facts follow from initial representation and frame invariants. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_sx_zval C.jet_secp_frame C.jet_secp_fe_math C.jet_secp_fe_b32.
Require Import C.jet_secp_write_fe_wrapper C.jet_secp_write_fe_numeric.
Require Import C.jet_secp_local_regions C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_write_fe_wide_values C.jet_secp_output_bytes.
Require Import C.jet_frame_inv C.jet_output_layout C.jet_predicate_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_fe_output t0 t1 t2 t3 t4 : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) (fe_val (Int64.unsigned t0) (Int64.unsigned t1)
    (Int64.unsigned t2) (Int64.unsigned t3) (Int64.unsigned t4) mod feP).
Lemma wide_fe_output_value t0 t1 t2 t3 t4 :
  @toZ (WordToZ 8) (wide_fe_output t0 t1 t2 t3 t4) =
  fe_val (Int64.unsigned t0) (Int64.unsigned t1)
    (Int64.unsigned t2) (Int64.unsigned t3) (Int64.unsigned t4) mod feP.
Proof.
  unfold wide_fe_output. rewrite to_fromZ.
  apply Z.mod_small. apply field_mod_256_range.
Qed.

Lemma wide_write_selected_outs t0 t1 t2 t3 t4 rc bd base layout :
  Int64.unsigned t0 <= 2 ^ 60 -> Int64.unsigned t1 <= 2 ^ 60 ->
  Int64.unsigned t2 <= 2 ^ 60 -> Int64.unsigned t3 <= 2 ^ 60 ->
  Int64.unsigned t4 <= 2 ^ 60 ->
  outsA (wide_fe_rho t0 t1 t2 t3 t4 rc)
    (slog (fst (rsel (wide_fe_rho t0 t1 t2 t3 t4 rc) layout (write_fe_result bd base)))) =
  Simplicity.Translate.encode (wide_fe_output t0 t1 t2 t3 t4).
Proof.
  intros H0 H1 H2 H3 H4. rewrite write_fe_selected_outs_bytes.
  replace (map (fun x => ii (den (wide_fe_rho t0 t1 t2 t3 t4 rc) β0 x))
    (write_fe_selected_bytes (wide_fe_rho t0 t1 t2 t3 t4 rc) layout bd base)) with
    (map (fun x => ii (den (wide_fe_rho t0 t1 t2 t3 t4 rc) layout x))
    (write_fe_selected_bytes (wide_fe_rho t0 t1 t2 t3 t4 rc) layout bd base)).
  - rewrite wide_write_selected_machine_bytes by assumption.
    rewrite <- wide_fe_output_value. apply be_bytes_canonical_encoding.
  - apply map_ext. intro x. apply (proj1 (den_proj_indep _ x layout β0)).
Qed.

Theorem eval_local_wide_write_fe m0 bd dbase bw edge cursor N bi rc
    t0 t1 t2 t3 t4 w0 outs0 m layout :
  write_frame_at m0 bd dbase bw edge cursor N ->
  Int64.unsigned t0 <= 2 ^ 60 -> Int64.unsigned t1 <= 2 ^ 60 ->
  Int64.unsigned t2 <= 2 ^ 60 -> Int64.unsigned t3 <= 2 ^ 60 ->
  Int64.unsigned t4 <= 2 ^ 60 ->
  rep (wide_fe_rho t0 t1 t2 t3 t4 rc) layout local_write_initial_regs m ->
  xsep (extA m0 bd bw bi) layout ->
  invA m0 bd dbase bw edge cursor N bi rc w0 outs0 256
    (wide_fe_rho t0 t1 t2 t3 t4 rc) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase);
       Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (outs0 ++ Simplicity.Translate.encode (wide_fe_output t0 t1 t2 t3 t4)) /\
    rep (wide_fe_rho t0 t1 t2 t3 t4 rc) layout
      (sregs (fst (rsel (wide_fe_rho t0 t1 t2 t3 t4 rc) (lay layout)
        (local_write_result bd (Ptrofs.repr dbase))))) mf /\
    lframe (frame (extA m0 bd bw bi) layout local_write_initial_regs m) m mf.
Proof.
  intros HO H0 H1 H2 H3 H4 HR HS HI.
  destruct (eval_local_write_fe m0 bd dbase bw edge cursor N bi 0 rc [] w0 outs0 HO
    m layout (wide_fe_rho t0 t1 t2 t3 t4 rc) HR HS HI)
    as (mf & HCall & HRep & HInv & HFrame).
  exists mf. split; [exact HCall|]. split.
  - unfold jet_secp_local_regions.wr_inv, invA in HInv. rewrite local_write_selected_log,
      write_fe_has_written, orb_true_r in HInv.
    rewrite wide_write_selected_outs in HInv by assumption.
    exact (proj1 (proj2 HInv)).
  - split; assumption.
Qed.
Print Assumptions eval_local_wide_write_fe.
