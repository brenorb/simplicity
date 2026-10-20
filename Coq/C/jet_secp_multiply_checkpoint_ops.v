(** Exact symbolic specialization of the actual original C multiplier. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Values.
Require Import C.jet_sx_expr.
Require Import C.jet_secp_multiply_shift_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition sx_low32 a := XI2L Unsigned (XL2I a).
Definition sx_product a b : sx * sx :=
  let ll := XLb Bmul (sx_low32 a) (sx_low32 b) in
  let lh := XLb Bmul (sx_low32 a) (XLsh Hshru b 32) in
  let hl := XLb Bmul (XLsh Hshru a 32) (sx_low32 b) in
  let hh := XLb Bmul (XLsh Hshru a 32) (XLsh Hshru b 32) in
  let mid := XLb Badd (XLb Badd (XLsh Hshru ll 32) (sx_low32 lh)) (sx_low32 hl) in
  (XLb Badd (XLsh Hshl mid 32) (sx_low32 ll),
   XLb Badd (XLb Badd (XLb Badd hh (XLsh Hshru lh 32)) (XLsh Hshru hl 32)) (XLsh Hshru mid 32)).
Definition sx_carry lo a := XI2L Signed (XLcmp Clt Unsigned lo a).
Definition sx_accum (s : sx * sx) a b : sx * sx :=
  let p := sx_product a b in let lo := XLb Badd (fst s) (fst p) in
  (lo, XLb Badd (snd s) (XLb Badd (snd p) (sx_carry lo (fst p)))).
Definition sx_accum_word (s : sx * sx) a : sx * sx :=
  let lo := XLb Badd (fst s) a in (lo, XLb Badd (snd s) (sx_carry lo a)).
Definition sx_shift52 (s : sx * sx) := (shift52_lo_sx (fst s) (snd s), shift52_hi_sx (snd s)).
Definition sx_shift64 (s : sx * sx) := (snd s, XLc Int64.zero).
