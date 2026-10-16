(** Transfer a region through the actual load/permission/validity frame contract. *)
From Coq Require Import ZArith List.
From compcert Require Import Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_mem.
Set Default Timeout 10.

Lemma region_ok_lframe rho beta m mf r reg P :
  lframe P m mf ->
  (forall pos, P (blk beta r) pos) ->
  region_ok rho beta m r reg -> region_ok rho beta mf r reg.
Proof.
  intros HF HP (HB & HV & HS & HC & HO).
  split; [exact HB|]. split; [exact ((proj2 (proj2 HF)) _ HV)|].
  split; [exact HS|]. split.
  - apply Forall_forall; intros c Hin.
    pose proof (proj1 (Forall_forall _ _) HC c Hin) as (HM & HA & HPerm & HValue).
    split; [exact HM|]. split; [exact HA|]. split.
    + intros pos HPos; eapply (proj1 (proj2 HF)); [exact HV|apply HP|apply HPerm; exact HPos].
    + intros x Hx; destruct (HValue x Hx) as [HL HX]; split; [|exact HX].
      rewrite (proj1 HF) by auto; exact HL.
  - destruct (rfree reg) as [sz|]; [|exact I].
    destruct HO as (H0 & HW & HPerm & HSize).
    split; [exact H0|]. split; [exact HW|]. split; [|exact HSize].
    intros pos HPos; eapply (proj1 (proj2 HF)); [exact HV|apply HP|apply HPerm; exact HPos].
Qed.
