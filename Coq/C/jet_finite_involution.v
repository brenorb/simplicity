(** Constructive finite pairing for the curve-order argument. *)
From Coq Require Import List Arith Lia Wf_nat.
Import ListNotations.
Set Default Timeout 10.
Theorem fixed_point_free_involution_even {A:Type} (f:A->A) L:
 NoDup L ->(forall x,In x L ->In (f x) L) ->
 (forall x,In x L ->f (f x)=x) ->(forall x,In x L ->f x<>x) ->Nat.Even (length L).
Proof.
 remember (length L) as n eqn:Len;revert L Len.
 induction n using lt_wf_ind;intros L Len Unique Closed Invol Free.
 destruct L as [|x xs];[rewrite Len;exists 0;reflexivity|].
 apply NoDup_cons_iff in Unique;destruct Unique as [NotX Unique].
 assert (FXIn:In (f x) xs).
 { pose proof (Closed x (or_introl eq_refl)) as Found.
   destruct Found as [Same|Found];[exfalso;apply (Free x (or_introl eq_refl));congruence|exact Found]. }
 destruct (in_split _ _ FXIn) as (left & right & XS);subst xs.
 set (rest:=left++right).
 assert (RestUnique:NoDup rest) by (apply (NoDup_remove_1 left right (f x));exact Unique).
 assert (NotFX:~In (f x) rest) by (apply (NoDup_remove_2 left right (f x));exact Unique).
 assert (Membership:forall z,In z (x::left++f x::right) <->z=x \/z=f x \/In z rest).
 { intro z;unfold rest;cbn [In];rewrite !in_app_iff;cbn [In];intuition congruence. }
 assert (RestInTail:forall z,In z rest ->In z (left++f x::right)).
 { intros z Found;unfold rest in Found;apply in_app_iff in Found.
   apply in_app_iff;destruct Found as [Found|Found];[left;exact Found|right;right;exact Found]. }
 assert (RestIn:forall z,In z rest ->In z (x::left++f x::right)).
 { intros z Found;right;apply RestInTail;exact Found. }
 assert (NotXRest:~In x rest).
 { intro Found;apply NotX,RestInTail;exact Found. }
 assert (RestClosed:forall z,In z rest ->In (f z) rest).
 { intros z Found;pose proof (RestIn z Found) as InFull.
   pose proof (Closed z InFull) as FFull;apply Membership in FFull.
   destruct FFull as [FX|[FY|Good]];[| |exact Good].
   - pose proof (f_equal f FX) as Same;rewrite (Invol z InFull) in Same.
     exfalso;apply NotFX;rewrite <-Same;exact Found.
   - pose proof (f_equal f FY) as Same;rewrite (Invol z InFull),(Invol x (or_introl eq_refl)) in Same.
     exfalso;apply NotXRest;rewrite <-Same;exact Found. }
 assert (Short:length rest<n).
 { unfold rest;cbn [length] in Len;rewrite app_length in Len;cbn [length] in Len.
   rewrite app_length;lia. }
 destruct (H (length rest) Short rest eq_refl RestUnique RestClosed
   ltac:(intros z Found;apply Invol,RestIn;exact Found)
   ltac:(intros z Found;apply Free,RestIn;exact Found)) as [k K].
 exists (S k);cbn [length] in Len;rewrite app_length in Len;cbn [length] in Len.
 unfold rest in K;rewrite app_length in K;lia.
Qed.
