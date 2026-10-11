(* Transport a proved original-C oracle to a disjoint external invariant.
   No call or preservation premise is added to a public jet theorem. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma separated_external_not_foot rho layout regs m ext b ofs :
  rep rho layout regs m -> xsep ext layout -> ext b ->
  ~ foot layout (map rshape regs) b ofs.
Proof.
  intros [HLength _] HSep HExt HFoot.
  destruct HFoot as [r [sh [d [ch [HNth [HIn [HBlock HRest]]]]]]].
  assert (HIndex : (r < length layout)%nat).
  { rewrite HLength, <- (map_length rshape regs).
    apply nth_error_Some; congruence. }
  apply (HSep r HIndex). rewrite <- HBlock; exact HExt.
Qed.

Lemma pure_frame_external rho layout regs m mf ext :
  rep rho layout regs m -> xsep ext layout ->
  lframe (frame (fun _ => False) layout regs m) m mf ->
  lframe (fun b _ => ext b) m mf.
Proof.
  intros HRep HSep HFrame.
  eapply lframe_implies; [exact HFrame|].
  intros b ofs HExt HValid; split; [exact HValid|]; split.
  - eapply separated_external_not_foot; eassumption.
  - tauto.
Qed.

Theorem pure_oracle_frame_lift ge fd oracle evok
  (inv : (nat -> int64) -> list event -> mem -> Prop) ext :
  oracle_ok ge (fun _ _ => True) (fun _ _ _ => True)
    (fun _ => False) fd oracle ->
  (forall rho log m mf, inv rho log m ->
    lframe (fun b _ => ext b) m mf -> inv rho log mf) ->
  (forall base xs regs regs' v tag cnt args log,
    oracle base log xs regs = Some (regs', v, tag, cnt, args) ->
    forall rho m, inv rho log m ->
      inv rho (log ++ [mkev tag base cnt args]) m) ->
  oracle_ok ge evok inv ext fd oracle.
Proof.
  intros HOracle HStable HLog.
  intros base xs regs regs' v tag cnt args log rho layout m
    HRun HRep HSep HInv HSol HEv.
  destruct (HOracle base xs regs regs' v tag cnt args log rho layout m
    HRun HRep ltac:(intros r HR []) I
    ltac:(apply Forall_forall; intros; exact I) I)
    as [mf [vres [HCall [HFinal [_ [HShape [HReturn HFrame]]]]]]].
  exists mf, vres; split; [exact HCall|]; split; [exact HFinal|]; split.
  - eapply HLog; [exact HRun|].
    eapply HStable; [exact HInv|].
    eapply pure_frame_external; eassumption.
  - split; [exact HShape|]; split; [exact HReturn|].
    eapply lframe_implies; [exact HFrame|].
    intros b ofs [HValid [HOutside HExt]] _.
    split; [exact HValid|]; split; [exact HOutside|tauto].
Qed.
