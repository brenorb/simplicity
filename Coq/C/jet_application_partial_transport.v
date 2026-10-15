(** Pointwise specification transport preserves success/failure returns,
    successful output/frame facts, and memory framing on every call. *)
From Coq Require Import ZArith List.
Require Import C.jet_application_partial.
Set Default Timeout 10.

Lemma application_jet_partial_spec_pointwise f ge E A B rep spec1 spec2 :
  (forall a e, spec1 a e = spec2 a e) ->
  application_jet_partial_spec f ge E A B rep spec1 ->
  application_jet_partial_spec f ge E A B rep spec2.
Proof.
  intros HE HS logical_env env m bd dbase bs sbase bi bw edge outedge cursor read_cursor a
    HR HB HA HF HC HM HI HW.
  destruct (HS logical_env env m bd dbase bs sbase bi bw edge outedge cursor read_cursor a
    HR HB HA HF HC HM HI HW) as [mf HRest].
  exists mf. rewrite <- (HE a logical_env). exact HRest.
Qed.

Print Assumptions application_jet_partial_spec_pointwise.
