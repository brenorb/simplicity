(** Original reader numeric bridge independent of enclosing allocation size. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_zval C.jet_sx_zrep.
Require Import C.jet_sx_exec C.jet_encoding C.jet_input_layout C.jet_secp_fe_nv.
Require Import C.jet_secp_wrapper_run C.jet_secp_read_fe_numeric.
Require Import C.jet_secp_point_write_run C.jet_secp_point_read_values C.jet_secp_owned_read_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma owned_read_selected_cells size k bi edge rho layout :
  cells0 (fst (rsel rho layout (owned_read_result size k bi edge))) =
  map (point_shift_cell (point_coordinate_offset k))
    (cells0 (fst (rsel rho layout (read_fe_result bi edge)))).
Proof.
  rewrite !selected_cells_rsel.
  destruct k; cbn [owned_read_result owned_read_tree read_fe_result read_fe_tree selected_cells].
  all: repeat match goal with |- context[if ?condition then _ else _] => destruct condition end.
  all: reflexivity.
Qed.

Lemma owned_read_selected_checked size k bi edge rho layout :
  zreg_okb read_bounds (point_coordinate_offset k)
    (cells0 (fst (rsel rho layout (owned_read_result size k bi edge)))) = true.
Proof.
  rewrite owned_read_selected_cells.
  replace (point_coordinate_offset k) with (point_coordinate_offset k + 0) at 1 by lia.
  rewrite point_shift_zreg_checked; apply read_fe_selected_checked.
Qed.

Theorem owned_read_selected_canonical size k (value : Ty.tySem (Simplicity.Word.Word 8)) rc bi edge layout :
  zcells (zrho (read_fe_rho (frame_input_word_bits value) rc))
    (cells0 (fst (rsel (read_fe_rho (frame_input_word_bits value) rc) layout
      (owned_read_result size k bi edge)))) =
  C.jet_secp_fe_math.fe_limbs_of
    (@Simplicity.Word.ToZ.Theory.toZ (Simplicity.Word.WordToZ 8)
      (@C.jet_secp_canonical_normalize.canonical_fe_normalize Simplicity.Alg.CoreFunSem value)).
Proof.
  rewrite owned_read_selected_cells, point_shift_zcells; apply read_fe_selected_canonical.
Qed.
