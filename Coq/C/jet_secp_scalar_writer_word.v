(** Generic original scalar writer contract for any Word256 value, not a
    normalization-only adapter. Exact output is its canonical encoding. *)
From Coq Require Import ZArith List Bool.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_frame.
Require Import C.jet_word_repr C.jet_frame_inv C.jet_output_layout.
Require Import C.jet_secp_output_bytes.
Require Import C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_writer_run.
Require Import C.jet_secp_scalar_writer_exec C.jet_secp_scalar_writer_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma scalar_writer_outs_word (value : Ty.tySem (Word 8)) layout bd base :
  outsA (scalar_limb_rho (@toZ (WordToZ 8) value))
    (slog (fst (rsel (scalar_limb_rho (@toZ (WordToZ 8) value)) layout
      (scalar_writer_result bd base)))) = encode value.
Proof.
  rewrite scalar_writer_outs_numeric by apply word_toZ_range.
  apply be_bytes_canonical_encoding.
Qed.

Theorem eval_write_scalar_word m0 bd dbase bw outedge cursor N bi rc
    (value : Ty.tySem (Word 8)) w0 outs0 m layout :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  rep (scalar_limb_rho (@toZ (WordToZ 8) value)) layout scalar_writer_initial_regs m ->
  xsep (jet_secp_scalar_writer_exec.scalar_write_ext m0 bd bw bi) layout ->
  jet_secp_scalar_writer_exec.scalar_write_inv m0 bd dbase bw outedge cursor N bi rc w0 outs0
    (scalar_limb_rho (@toZ (WordToZ 8) value)) [] m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_scalar)
      [Vptr bd (Ptrofs.repr dbase); Vptr (blk layout 0) (Ptrofs.repr (bas layout 0))] E0 mf Vundef /\
    rep (scalar_limb_rho (@toZ (WordToZ 8) value)) layout scalar_writer_initial_regs mf /\
    finv m0 bd dbase bw outedge cursor N bi mf true (outs0 ++ encode value) /\
    lframe (frame (jet_secp_scalar_writer_exec.scalar_write_ext m0 bd bw bi)
      layout scalar_writer_initial_regs m) m mf.
Proof.
  intros HO HRep HSep HInv.
  destruct (eval_write_scalar_from_initial_regions m0 bd dbase bw outedge cursor N bi 0 rc []
    w0 outs0 HO m layout (scalar_limb_rho (@toZ (WordToZ 8) value)) HRep HSep HInv)
    as (mf & HExec & HFinal & HFinalInv & HFrame).
  exists mf; split; [exact HExec|]; split; [exact HFinal|]; split; [|exact HFrame].
  unfold jet_secp_scalar_writer_exec.scalar_write_inv, invA in HFinalInv.
  rewrite scalar_writer_has_written, orb_true_r, scalar_writer_outs_word in HFinalInv.
  exact (proj1 (proj2 HFinalInv)).
Qed.
