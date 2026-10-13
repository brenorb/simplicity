(** Complete original affine writer from owned bounded fields, not assumed calls. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp.
Require Import C.jet_frame_inv C.jet_output_layout C.jet_secp_point_write_field.
Require Import C.jet_secp_affine_two_writes C.jet_secp_write_ge_body.
Require Simplicity.Translate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_write_ge_general m0 bd dbase bw edge cursor N bi (rc : Z) m b fx fy :
  write_frame_at m0 bd dbase bw edge cursor N -> 512 <= N ->
  finv m0 bd dbase bw edge cursor N bi m false [] ->
  point_field_bounds fx -> point_field_bounds fy ->
  fe_at m b 0 (point_field_limbs fx) -> fe_at m b 40 (point_field_limbs fy) ->
  Mem.range_perm m b 0 88 Cur Freeable -> xsep (extA m0 bd bw bi) [(b,0)] ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_write_ge)
      [Vptr bd (Ptrofs.repr dbase);Vptr b (Ptrofs.repr 0)] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (Simplicity.Translate.encode (point_field_output fx) ++
       Simplicity.Translate.encode (point_field_output fy)) /\
    Mem.range_perm mf b 0 88 Cur Freeable /\
    lframe (fun bx _ => bx <> b /\ ~ extA m0 bd bw bi bx) m mf.
Proof.
  intros HO HN HI HBX HBY HX HY HP HS.
  destruct (eval_affine_two_general_writes m0 bd dbase bw edge cursor N bi rc m b fx fy
    HO HN HI HBX HBY HX HY HP HS) as (mx & mf & HCX & HCY & HFin & HFree & HFrame).
  exists mf; split;[eapply eval_write_ge_from_calls;eassumption|].
  split;[exact HFin|];split;assumption.
Qed.
Print Assumptions eval_write_ge_general.
