(** Exact output of the original write_scalar call, retaining its actual
    owned input region. Numeric decoding is only an internal bridge to the
    literal canonical Simplicity term. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_zval C.jet_sx_zrep C.jet_sx_mem.
Require Import C.jet_sx_exec.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_fe_b32 C.jet_secp_output_bytes.
Require Import C.jet_word_repr C.jet_frame_inv C.jet_output_layout C.jet_write8_sequence.
Require Import C.jet_secp_linkage C.jets_secp.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Simplicity.Alg.
Require Import C.jet_secp_scalar_get_b32_exec C.jet_secp_scalar_get_b32_numeric.
Require Import C.jet_secp_canonical_scalar.
Require Import C.jet_secp_scalar_writer_run C.jet_secp_scalar_writer_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_writer_event bd base :=
  hd (mkev tWR8 4 0 []) (slog (fst (rsel (fun _ => Int64.zero) β0 (scalar_writer_result bd base)))).
Definition scalar_writer_bytes bd base := tl (eargs (scalar_writer_event bd base)).
Lemma scalar_writer_log rho layout bd base :
  slog (fst (rsel rho layout (scalar_writer_result bd base))) = [scalar_writer_event bd base].
Proof. reflexivity. Qed.
Lemma scalar_writer_bytes_from_getter bd base :
  scalar_writer_bytes bd base = map cell_sx (cells0 scalar_get_state).
Proof. reflexivity. Qed.
Lemma scalar_writer_bytes_checked bd base :
  Forall (fun x => zb scalar_u64_bounds x = Some (0, 255) /\ isk KI x = true)
    (scalar_writer_bytes bd base).
Proof. rewrite scalar_writer_bytes_from_getter; repeat constructor; vm_compute; reflexivity. Qed.
Lemma scalar_writer_bytes_numeric value bd base :
  0 <= value < 2 ^ 256 ->
  map (zval (zrho (scalar_limb_rho value))) (scalar_writer_bytes bd base) = be_bytes value.
Proof.
  intro HValue; rewrite scalar_writer_bytes_from_getter, <- scalar_get_zcells_numeric by exact HValue.
  rewrite map_map; unfold zcells; apply map_ext; intro c.
  destruct (cval c) eqn:HVal; unfold cell_sx; rewrite HVal; reflexivity.
Qed.
Lemma scalar_writer_machine_bytes value bd base layout :
  0 <= value < 2 ^ 256 ->
  map (fun x => ii (den (scalar_limb_rho value) layout x)) (scalar_writer_bytes bd base) =
    map Int.repr (be_bytes value).
Proof.
  intro HValue; rewrite <- (scalar_writer_bytes_numeric value bd base HValue), map_map.
  apply map_ext_in; intros x HIn.
  destruct (proj1 (Forall_forall _ _) (scalar_writer_bytes_checked bd base) x HIn) as [HCheck HKind].
  rewrite (proj1 (den_zval_int (scalar_limb_rho value) scalar_u64_bounds layout
    ltac:(intro n; apply Int64.unsigned_range_2) x 0 255 HCheck HKind)); reflexivity.
Qed.
Lemma scalar_writer_has_written rho layout bd base :
  has_wr (slog (fst (rsel rho layout (scalar_writer_result bd base)))) = true.
Proof. reflexivity. Qed.
Lemma scalar_writer_outs_bytes rho layout bd base :
  outsA rho (slog (fst (rsel rho layout (scalar_writer_result bd base)))) =
    byte_sequence_cells (map (fun x => ii (den rho β0 x)) (scalar_writer_bytes bd base)).
Proof.
  rewrite scalar_writer_log; unfold outsA, is_wr, wr_bytes; cbn [map concat].
  rewrite app_nil_r; reflexivity.
Qed.
Lemma scalar_writer_outs_numeric value layout bd base :
  0 <= value < 2 ^ 256 ->
  outsA (scalar_limb_rho value)
    (slog (fst (rsel (scalar_limb_rho value) layout (scalar_writer_result bd base)))) =
    byte_sequence_cells (map Int.repr (be_bytes value)).
Proof.
  intro HValue; rewrite scalar_writer_outs_bytes, scalar_writer_machine_bytes by exact HValue; reflexivity.
Qed.
Lemma scalar_writer_outs_canonical (value : Ty.tySem (Word 8)) layout bd base :
  outsA (scalar_limb_rho (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))
    (slog (fst (rsel (scalar_limb_rho (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))
      layout (scalar_writer_result bd base)))) =
    encode (@canonical_scalar_normalize Alg.CoreFunSem value).
Proof. rewrite scalar_writer_outs_numeric by apply word_toZ_range; apply be_bytes_canonical_encoding. Qed.

Theorem eval_write_scalar_against_canonical_program m0 bd dbase bw outedge cursor N bi rc
    (value : Ty.tySem (Word 8)) w0 outs0 m layout :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  rep (scalar_limb_rho (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))
    layout scalar_writer_initial_regs m ->
  xsep (jet_secp_scalar_writer_exec.scalar_write_ext m0 bd bw bi) layout ->
  jet_secp_scalar_writer_exec.scalar_write_inv m0 bd dbase bw outedge cursor N bi rc w0 outs0
    (scalar_limb_rho (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value))) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_scalar)
      [Vptr bd (Ptrofs.repr dbase); Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf Vundef /\
    rep (scalar_limb_rho (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))
      layout scalar_writer_initial_regs mf /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (outs0 ++ encode (@canonical_scalar_normalize Alg.CoreFunSem value)) /\
    lframe (frame (jet_secp_scalar_writer_exec.scalar_write_ext m0 bd bw bi) layout scalar_writer_initial_regs m) m mf.
Proof.
  intros HOutput HRep HSep HInv.
  destruct (eval_write_scalar_from_initial_regions m0 bd dbase bw outedge cursor N bi 0 rc []
    w0 outs0 HOutput m layout
    (scalar_limb_rho (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))
    HRep HSep HInv) as [mf [HExec [HFinal [HFinalInv HFrame]]]].
  exists mf; split; [exact HExec|]; split; [exact HFinal|]; split; [|exact HFrame].
  unfold jet_secp_scalar_writer_exec.scalar_write_inv, invA in HFinalInv.
  rewrite scalar_writer_has_written, orb_true_r, scalar_writer_outs_canonical in HFinalInv.
  exact (proj1 (proj2 HFinalInv)).
Qed.
