(** Actual branch expressions shared by byte shifts with and without fill.
    This is execution infrastructure, not an end-to-end jet contract. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_rotate8_helper.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift8_scalar_expr (right : bool) := Ecast (Ecast
  (if right then
    Ebinop Oshr (Etempvar _output tuchar) (Etempvar _amt tuchar) tint
   else Ebinop Oshl
    (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _output tuchar) tuint)
    (Etempvar _amt tuchar) tuint) tuchar) tuchar.
Definition shift8_scalar_result (right : bool) r a :=
  Int.zero_ext 8 (if right then Int.shr r a else Int.shl r a).
Definition shift8_fill_expr := Ecast
  (Ebinop Oxor (Econst_int (Int.repr 255) tint) (Etempvar _output tuchar) tint) tuchar.
Definition shift8_fill_result r := Int.zero_ext 8 (Int.xor (Int.repr 255) r).
Definition shift8_count_expr :=
  Ebinop Olt (Etempvar _amt tuchar) (Econst_int (Int.repr 8) tint) tint.

Definition shift8_helper (right : bool) :=
  if right then f_right_shift_helper_8 else f_left_shift_helper_8.
Definition shift8_reader (nibble : bool) result := Scall (Some result)
  (Evar (if nibble then _simplicity_read4 else _simplicity_read8)
    (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tuchar cc_default))
  [Etempvar _src (tptr (Tstruct _frameItem noattr))].
Definition shift8_fill_step := Sifthenelse (Etempvar _with tbool)
  (Sset _output shift8_fill_expr) Sskip.

Lemma shift8_helper_body right : (shift8_helper right).(fn_body) =
  Ssequence
    (Ssequence (shift8_reader true _t'1)
      (Sset _amt (Ecast (Etempvar _t'1 tuchar) tuchar)))
    (Ssequence
      (Ssequence (shift8_reader false _t'2)
        (Sset _output (Ecast (Etempvar _t'2 tuchar) tuchar)))
      (Ssequence shift8_fill_step
        (Ssequence
          (Sifthenelse shift8_count_expr (Sset _output (shift8_scalar_expr right))
            (Sset _output (Ecast (Econst_int Int.zero tint) tuchar)))
          (Ssequence shift8_fill_step
            (Scall None
              (Evar _simplicity_write8 (Tfunction
                (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tuchar Tnil)) tvoid cc_default))
              [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _output tuchar]))))).
Proof. destruct right; reflexivity. Qed.

Lemma eval_shift8_scalar_expr right e le m r a :
  0 <= Int.unsigned a < 8 -> le!_output = Some (Vint r) -> le!_amt = Some (Vint a) ->
  eval_expr ge0 e le m (shift8_scalar_expr right) (Vint (shift8_scalar_result right r a)).
Proof.
  intros HA HR HM.
  assert (HG : Int.ltu a Int.iwordsize = true) by (apply int_shift_guard; lia).
  unfold shift8_scalar_expr, shift8_scalar_result.
  eapply eval_Ecast with (v1 := Vint (Int.zero_ext 8 (if right then Int.shr r a else Int.shl r a))).
  - eapply eval_Ecast with (v1 := Vint (if right then Int.shr r a else Int.shl r a)).
    + destruct right.
      * eapply eval_Ebinop with (v1 := Vint r) (v2 := Vint a).
        -- apply eval_Etempvar; exact HR.
        -- apply eval_Etempvar; exact HM.
        -- change ((if Int.ltu a Int.iwordsize then Some (Vint (Int.shr r a)) else None) =
            Some (Vint (Int.shr r a))). rewrite HG; reflexivity.
      * eapply eval_Ebinop with (v1 := Vint r) (v2 := Vint a).
        -- eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vint r).
           ++ constructor.
           ++ apply eval_Etempvar; exact HR.
           ++ change (Some (Vint (Int.mul Int.one r)) = Some (Vint r)).
              rewrite Int.mul_commut, Int.mul_one; reflexivity.
        -- apply eval_Etempvar; exact HM.
        -- change ((if Int.ltu a Int.iwordsize then Some (Vint (Int.shl r a)) else None) =
            Some (Vint (Int.shl r a))). rewrite HG; reflexivity.
    + destruct right; reflexivity.
  - change (Some (Vint (Int.zero_ext 8 (Int.zero_ext 8
      (if right then Int.shr r a else Int.shl r a)))) =
      Some (Vint (Int.zero_ext 8 (if right then Int.shr r a else Int.shl r a)))).
    rewrite Int.zero_ext_idem by lia; reflexivity.
Qed.

Lemma eval_shift8_fill_expr e le m r : le!_output = Some (Vint r) ->
  eval_expr ge0 e le m shift8_fill_expr (Vint (shift8_fill_result r)).
Proof.
  intros HR. unfold shift8_fill_expr, shift8_fill_result.
  eapply eval_Ecast with (v1 := Vint (Int.xor (Int.repr 255) r)).
  - eapply eval_Ebinop with (v1 := Vint (Int.repr 255)) (v2 := Vint r).
    + constructor.
    + apply eval_Etempvar; exact HR.
    + reflexivity.
  - reflexivity.
Qed.

Lemma eval_shift8_count_expr e le m a : 0 <= Int.unsigned a < 256 -> le!_amt = Some (Vint a) ->
  eval_expr ge0 e le m shift8_count_expr
    (Vint (if zlt (Int.unsigned a) 8 then Int.one else Int.zero)).
Proof.
  intros HA HM.
  assert (HS : Int.signed a = Int.unsigned a).
  { apply Int.signed_eq_unsigned. change Int.max_signed with 2147483647; lia. }
  unfold shift8_count_expr.
  eapply eval_Ebinop with (v1 := Vint a) (v2 := Vint (Int.repr 8)).
  - apply eval_Etempvar; exact HM.
  - constructor.
  - change (Some (Val.of_bool (Int.lt a (Int.repr 8))) =
      Some (Vint (if zlt (Int.unsigned a) 8 then Int.one else Int.zero))).
    unfold Int.lt. rewrite HS. change (Int.signed (Int.repr 8)) with 8.
    destruct (zlt (Int.unsigned a) 8); reflexivity.
Qed.
