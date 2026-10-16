(** Fuel adequacy for the canonical null-data parser port. Each accepted datum
    consumes an opcode byte, even an empty immediate push. No parsing result is
    assumed to avoid exhausting the Coq termination fuel. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Digest.
Require Import C.jet_elements_prim.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma getBytes_rest_length n bs data rest :
  getBytes n bs = Some (data, rest) -> (length rest <= length bs)%nat.
Proof.
  unfold getBytes. destruct (Z.leb n (Zlength bs)); [|discriminate].
  intros H. inversion H; subst. rewrite skipn_length. lia.
Qed.

Lemma getPush_rest_length width bs data rest :
  getPush width bs = Some (data, rest) -> (length rest <= length bs)%nat.
Proof.
  unfold getPush. destruct (getBytes width bs) as [[len rem]|] eqn:HL; [|discriminate].
  intros HD. pose proof (getBytes_rest_length _ _ _ _ HL).
  pose proof (getBytes_rest_length _ _ _ _ HD). lia.
Qed.

Lemma getTxNullDatum_consumes bs d rest :
  getTxNullDatum bs = Some (d, rest) -> (length rest < length bs)%nat.
Proof.
  destruct bs as [|op bs]; [discriminate|].
  unfold getTxNullDatum. cbv beta iota zeta. intros H.
  repeat match type of H with
  | context [if ?b then _ else _] => destruct b in H
  end.
  all: first [solve [inversion H; subst; cbn [length]; lia] | idtac].
  all: match type of H with
  | context [Datatypes.option_map _ (getPush ?w ?input)] =>
      destruct (getPush w input) as [[data rem]|] eqn:HP;
        cbn [Datatypes.option_map fst snd] in H; [|discriminate];
      inversion H; subst; pose proof (getPush_rest_length _ _ _ _ HP); cbn [length]; lia
  | context [Datatypes.option_map _ (getBytes ?n ?input)] =>
      destruct (getBytes n input) as [[data rem]|] eqn:HP;
        cbn [Datatypes.option_map fst snd] in H; [|discriminate];
      inversion H; subst; pose proof (getBytes_rest_length _ _ _ _ HP); cbn [length]; lia
  | _ => discriminate
  end.
Qed.

Inductive null_data_parse : list byte -> list (txNullDatumF (list byte)) -> Prop :=
| null_data_parse_nil : null_data_parse [] []
| null_data_parse_cons bs d rest ds :
    getTxNullDatum bs = Some (d, rest) -> null_data_parse rest ds -> null_data_parse bs (d :: ds).

Lemma getTxNullData_sound fuel bs ds :
  getTxNullData fuel bs = Some ds -> null_data_parse bs ds.
Proof.
  revert bs ds. induction fuel as [|fuel IH]; intros [|b bs] ds H.
  - inversion H; constructor.
  - discriminate.
  - inversion H; constructor.
  - cbn [getTxNullData] in H.
    destruct (getTxNullDatum (b :: bs)) as [[d rest]|] eqn:HD; [|discriminate].
    destruct (getTxNullData fuel rest) as [tail|] eqn:HT; [|discriminate].
    inversion H; subst. econstructor; [exact HD|apply IH; exact HT].
Qed.

Lemma getTxNullData_complete bs ds :
  null_data_parse bs ds -> forall fuel, (length bs <= fuel)%nat -> getTxNullData fuel bs = Some ds.
Proof.
  intros H. induction H as [|bs d rest ds HD HP IH]; intros fuel HF.
  - destruct fuel; reflexivity.
  - pose proof (getTxNullDatum_consumes bs d rest HD) as HS.
    destruct fuel as [|fuel]; [lia|]. destruct bs as [|b bs]; [discriminate|].
    cbn [getTxNullData]. rewrite HD, IH by (cbn [length] in HS, HF; lia). reflexivity.
Qed.

Theorem getTxNullData_fuel_adequate fuel bs ds :
  (length bs <= fuel)%nat -> (getTxNullData fuel bs = Some ds <-> null_data_parse bs ds).
Proof.
  intros HF. split; [apply getTxNullData_sound|intros HP; apply getTxNullData_complete; assumption].
Qed.

Lemma null_data_parse_length bs ds :
  null_data_parse bs ds -> (length ds <= length bs)%nat.
Proof.
  intros H. induction H; [reflexivity|]. pose proof (getTxNullDatum_consumes _ _ _ H). cbn [length]. lia.
Qed.

Theorem txNullData_parser_relation script ds :
  txNullData script = Some ds <->
  exists op rest, script = op :: rest /\ Byte.unsigned op = 106 /\ null_data_parse rest ds.
Proof.
  unfold txNullData. destruct script as [|op rest].
  - split; [discriminate|intros (? & ? & H & _); discriminate].
  - destruct (Z.eqb (Byte.unsigned op) 106) eqn:HO.
    + apply Z.eqb_eq in HO. rewrite getTxNullData_fuel_adequate by lia.
      split; [intros HP; exists op, rest; auto|].
      intros (op' & rest' & HE & _ & HP). inversion HE; subst. exact HP.
    + apply Z.eqb_neq in HO. split; [discriminate|].
      intros (op' & rest' & HE & HX & _). inversion HE; subst. contradiction.
Qed.
