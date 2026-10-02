(** Canonical full-shift programs rebalance the tuple without changing its
    serialized cells.  These shared bridges prepare the copy-based jet family;
    they do not discharge the generated copyBits external memcpy paths. *)
From Coq Require Import List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Import ListNotations.
Set Default Timeout 10.

Lemma encode_full_left_shift1 (X : Ty) n (v : Ty.tySem (Vector X n)) (x : Ty.tySem X) :
  encode (@full_left_shift1 X n Alg.CoreFunSem (v, x)) =
    @encode (Ty.Prod (Vector X n) X) (v, x).
Proof.
  revert v x. induction n as [|n IH]; intros v x.
  - reflexivity.
  - destruct v as [hi lo].
    set (l := @full_left_shift1 X n Alg.CoreFunSem (lo, x)).
    set (h := @full_left_shift1 X n Alg.CoreFunSem (hi, fst l)).
    pose proof (IH lo x) as HL. pose proof (IH hi (fst l)) as HH.
    change (encode (fst h) ++ (encode (snd h) ++ encode (snd l)) =
      (encode hi ++ encode lo) ++ encode x).
    change (@encode (Ty.Prod X (Vector X n)) l =
      @encode (Ty.Prod (Vector X n) X) (lo, x)) in HL.
    change (@encode (Ty.Prod X (Vector X n)) h =
      @encode (Ty.Prod (Vector X n) X) (hi, fst l)) in HH.
    destruct l as [lf ls]. destruct h as [hf hs].
    change (encode lf ++ encode ls = encode lo ++ encode x) in HL.
    change (encode hf ++ encode hs = encode hi ++ encode lf) in HH.
    cbn [fst snd].
    rewrite app_assoc, HH, <- app_assoc, HL, app_assoc. reflexivity.
Qed.

Lemma encode_full_right_shift1 (X : Ty) n (x : Ty.tySem X) (v : Ty.tySem (Vector X n)) :
  encode (@full_right_shift1 X n Alg.CoreFunSem (x, v)) =
    @encode (Ty.Prod X (Vector X n)) (x, v).
Proof.
  revert x v. induction n as [|n IH]; intros x v.
  - reflexivity.
  - destruct v as [hi lo].
    set (h := @full_right_shift1 X n Alg.CoreFunSem (x, hi)).
    set (l := @full_right_shift1 X n Alg.CoreFunSem (snd h, lo)).
    pose proof (IH x hi) as HH. pose proof (IH (snd h) lo) as HL.
    change ((encode (fst h) ++ encode (fst l)) ++ encode (snd l) =
      encode x ++ (encode hi ++ encode lo)).
    change (@encode (Ty.Prod (Vector X n) X) h =
      @encode (Ty.Prod X (Vector X n)) (x, hi)) in HH.
    change (@encode (Ty.Prod (Vector X n) X) l =
      @encode (Ty.Prod X (Vector X n)) (snd h, lo)) in HL.
    destruct h as [hf hs]. destruct l as [lf ls].
    change (encode hf ++ encode hs = encode x ++ encode hi) in HH.
    change (encode lf ++ encode ls = encode hs ++ encode lo) in HL.
    cbn [fst snd].
    rewrite <- app_assoc, HL, app_assoc, HH, <- app_assoc. reflexivity.
Qed.
