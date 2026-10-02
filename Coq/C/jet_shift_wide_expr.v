(** Exact generated LP64 shift-helper shapes and branch expressions, shared
    by 16/32/64-bit consumers. This infrastructure alone adds no jet coverage. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_wide C.jet_rotate_wide_helper C.jet_shift8_expr.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift_wide_helper s (right : bool) := match s, right with
  | W16, false => f_left_shift_helper_16 | W16, true => f_right_shift_helper_16
  | W32, false => f_left_shift_helper_32 | W32, true => f_right_shift_helper_32
  | W64, false => f_left_shift_helper_64 | W64, true => f_right_shift_helper_64 end.
Definition shift_wide_scalar_expr (right : bool) := Ecast
  (if right then Ebinop Oshr (Etempvar _output tulong) (Etempvar _amt tuchar) tulong
   else Ebinop Oshl
    (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _output tulong) tulong)
    (Etempvar _amt tuchar) tulong) tulong.
Definition shift_wide_scalar_result (right : bool) r a :=
  if right then Int64.shru r (Int64.repr (Int.unsigned a))
  else Int64.shl r (Int64.repr (Int.unsigned a)).
Definition shift_wide_fill_constant s := match s with
  | W16 => Econst_int (Int.repr 65535) tint
  | W32 => Econst_int Int.mone tuint
  | W64 => Econst_long Int64.mone tulong end.
Definition shift_wide_fill_mask s := match s with
  | W16 => Int64.repr 65535 | W32 => Int64.repr 4294967295 | W64 => Int64.mone end.
Definition shift_wide_fill_expr s :=
  Ebinop Oxor (shift_wide_fill_constant s) (Etempvar _output tulong) tulong.
Definition shift_wide_fill_result s r := Int64.xor (shift_wide_fill_mask s) r.
Definition shift_wide_count_expr s :=
  Ebinop Olt (Etempvar _amt tuchar) (Econst_int (Int.repr (wide_bits s)) tint) tint.
Definition shift_wide_count_reader s := shift8_reader
  (match s with W16 => true | _ => false end) _t'1.
Definition shift_wide_payload_reader s := Scall (Some _t'2)
  (Evar (wide_reader_id s) (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tulong cc_default))
  [Etempvar _src (tptr (Tstruct _frameItem noattr))].
Definition shift_wide_fill_step s := Sifthenelse (Etempvar _with tbool)
  (Sset _output (shift_wide_fill_expr s)) Sskip.

Lemma shift_wide_helper_body s right : (shift_wide_helper s right).(fn_body) =
  Ssequence
    (Ssequence (shift_wide_count_reader s)
      (Sset _amt (Ecast (Etempvar _t'1 tuchar) tuchar)))
    (Ssequence
      (Ssequence (shift_wide_payload_reader s) (Sset _output (Etempvar _t'2 tulong)))
      (Ssequence (shift_wide_fill_step s)
        (Ssequence
          (Sifthenelse (shift_wide_count_expr s) (Sset _output (shift_wide_scalar_expr right))
            (Sset _output (Ecast (Econst_int Int.zero tint) tulong)))
          (Ssequence (shift_wide_fill_step s)
            (Scall None
              (Evar (wide_writer_id s) (Tfunction
                (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
              [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _output tulong]))))).
Proof. destruct s, right; reflexivity. Qed.

Lemma eval_shift_wide_scalar_expr right e le m r a :
  0 <= Int.unsigned a < 64 -> le!_output = Some (Vlong r) -> le!_amt = Some (Vint a) ->
  eval_expr ge0 e le m (shift_wide_scalar_expr right) (Vlong (shift_wide_scalar_result right r a)).
Proof.
  intros HA HR HM.
  assert (HG : Int.ltu a Int64.iwordsize' = true) by (apply long_int_shift_guard; exact HA).
  unfold shift_wide_scalar_expr, shift_wide_scalar_result.
  eapply eval_Ecast with (v1 := Vlong (if right then Int64.shru r (Int64.repr (Int.unsigned a))
    else Int64.shl r (Int64.repr (Int.unsigned a)))).
  - destruct right.
    + eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vint a).
      * apply eval_Etempvar; exact HR.
      * apply eval_Etempvar; exact HM.
      * change ((if Int.ltu a Int64.iwordsize' then
          Some (Vlong (Int64.shru r (Int64.repr (Int.unsigned a)))) else None) =
          Some (Vlong (Int64.shru r (Int64.repr (Int.unsigned a))))).
        rewrite HG; reflexivity.
    + eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vint a).
      * eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vlong r).
        -- constructor.
        -- apply eval_Etempvar; exact HR.
        -- change (Some (Vlong (Int64.mul Int64.one r)) = Some (Vlong r)).
           rewrite Int64.mul_commut, Int64.mul_one; reflexivity.
      * apply eval_Etempvar; exact HM.
      * change ((if Int.ltu a Int64.iwordsize' then
          Some (Vlong (Int64.shl r (Int64.repr (Int.unsigned a)))) else None) =
          Some (Vlong (Int64.shl r (Int64.repr (Int.unsigned a))))).
        rewrite HG; reflexivity.
  - destruct right; reflexivity.
Qed.

Lemma eval_shift_wide_fill_expr s e le m r : le!_output = Some (Vlong r) ->
  eval_expr ge0 e le m (shift_wide_fill_expr s) (Vlong (shift_wide_fill_result s r)).
Proof.
  intros HR. destruct s; unfold shift_wide_fill_expr, shift_wide_fill_result,
    shift_wide_fill_constant, shift_wide_fill_mask.
  all: eapply eval_Ebinop.
  all: first [apply eval_Econst_int | apply eval_Econst_long |
    solve [apply eval_Etempvar; exact HR] | reflexivity].
Qed.

Lemma eval_shift_wide_count_expr s e le m a :
  0 <= Int.unsigned a < 256 -> le!_amt = Some (Vint a) ->
  eval_expr ge0 e le m (shift_wide_count_expr s)
    (Vint (if zlt (Int.unsigned a) (wide_bits s) then Int.one else Int.zero)).
Proof.
  intros HA HM.
  assert (HS : Int.signed a = Int.unsigned a).
  { apply Int.signed_eq_unsigned. change Int.max_signed with 2147483647; lia. }
  assert (HW : Int.signed (Int.repr (wide_bits s)) = wide_bits s) by (destruct s; reflexivity).
  unfold shift_wide_count_expr.
  eapply eval_Ebinop with (v1 := Vint a) (v2 := Vint (Int.repr (wide_bits s))).
  - apply eval_Etempvar; exact HM.
  - constructor.
  - change (Some (Val.of_bool (Int.lt a (Int.repr (wide_bits s)))) =
      Some (Vint (if zlt (Int.unsigned a) (wide_bits s) then Int.one else Int.zero))).
    unfold Int.lt. rewrite HS, HW. destruct (zlt (Int.unsigned a) (wide_bits s)); reflexivity.
Qed.
