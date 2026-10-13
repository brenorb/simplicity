(* Proved shift64 calls are neutral to the frame reader/writer event log. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_exec.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_output_layout.
Require Import C.jet_secp_pure_oracle_frame C.jet_secp_u128_shift64_oracle.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma shift64_event_tag base xs regs regs' v tag cnt args log :
  u128_shift64_oracle base log xs regs = Some (regs', v, tag, cnt, args) ->
  tag = 0%nat.
Proof.
  unfold u128_shift64_oracle.
  destruct xs as [|arg0 [|arg1 [|extra tail]]]; try discriminate.
  destruct arg0; try discriminate; destruct arg1; try discriminate.
  destruct (Z.eqb d 0 && Int.eq i (Int.repr 64)); [|discriminate].
  destruct (nth_error regs r) as [reg|]; [|discriminate].
  destruct (rfree reg) as [sz|]; [|discriminate].
  destruct (Z.eqb sz 16); [|discriminate].
  destruct (xload regs r 8 tulong) as [hi|]; [|discriminate].
  destruct (isk KL hi); [|discriminate].
  destruct (xstore regs r 0 Mint64 hi) as [regs1|]; [|discriminate].
  destruct (xstore regs1 r 8 Mint64 (XLc Int64.zero)); [|discriminate].
  intro H; inversion H; reflexivity.
Qed.

Lemma invA_append_nonwrite m0 bd dbase bw outedge cursor N bi rc w0 outs0 cap
  rho log m ev :
  is_wr ev = false ->
  invA m0 bd dbase bw outedge cursor N bi rc w0 outs0 cap rho log m ->
  invA m0 bd dbase bw outedge cursor N bi rc w0 outs0 cap rho (log ++ [ev]) m.
Proof.
  intros HWrite HInv.
  unfold invA in *.
  rewrite has_wr_app, outsA_app, written_app.
  unfold has_wr, outsA at 2; cbn [existsb map concat written].
  rewrite HWrite; cbn [app]; rewrite Bool.orb_false_r, app_nil_r, Z.add_0_r.
  exact HInv.
Qed.

Theorem shift64_frame_oracle m0 bd dbase bw outedge cursor N bi rc w0 outs0 cap
  evok :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  oracle_ok secp_ge evok
    (invA m0 bd dbase bw outedge cursor N bi rc w0 outs0 cap)
    (extA m0 bd bw bi) f_secp256k1_u128_rshift u128_shift64_oracle.
Proof.
  intro HOutput.
  eapply pure_oracle_frame_lift.
  - exact u128_shift64_oracle_correct.
  - apply invA_stable; exact HOutput.
  - intros base xs regs regs' v tag cnt args log HRun rho m HInv.
    apply invA_append_nonwrite; [|exact HInv].
    unfold is_wr; cbn [etag].
    rewrite (shift64_event_tag base xs regs regs' v tag cnt args log HRun).
    reflexivity.
Qed.
