(** Complete actual arbitrary Buffer63 writer from initial canonical arrays,
    including both assertion loops, initial shift, mixed loop and return.
    Shared infrastructure only, not an individual public jet theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Maps.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_umul128_layout C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks.
Require Import C.jet_buffer_write_choices C.jet_read8s_layout C.jet_write_buffer8_empty_exec.
Require Import C.jet_write_buffer8_empty_run C.jet_write_buffer8_empty_call C.jet_write_buffer8_loop_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition buffer8_write_temps bf base bi input len := PTree.set _n (Vint (Int.repr 5))
  (PTree.set _len (Vlong (Int64.repr len)) (PTree.set _buf (Vptr bi (Ptrofs.repr input))
    (PTree.set _dst (Vptr bf (Ptrofs.repr base)) (create_undef_temps f_simplicity_write_buffer8.(fn_temps))))).

Theorem eval_write_buffer8_from_loop m mf bf base bi input len lef :
  Clight2.exec_stmt ge0 empty_env
    (PTree.set _i (Vlong (Int64.repr 32)) (buffer8_write_temps bf base bi input len))
    m buffer8_actual_loop E0 lef mf Out_normal ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_write_buffer8)
    [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr input); Vlong (Int64.repr len); Vint (Int.repr 5)]
    E0 mf Vundef.
Proof.
  intro HLoop. set (le0 := buffer8_write_temps bf base bi input len).
  set (le1 := PTree.set _i (Vlong (Int64.repr 32)) le0).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le0) (le2 := lef)
    (m1 := m) (m2 := mf) (out := Out_normal).
  - constructor.
    + constructor.
    + change (list_norepet [_dst; _buf; _len; _n]). vm_compute.
      repeat (apply list_norepet_cons; [simpl; intuition discriminate|]). constructor.
    + change (list_disjoint [_dst; _buf; _len; _n] [_i; _t'2; _t'1]); vm_compute; intuition congruence.
    + constructor.
    + reflexivity.
  - rewrite buffer8_body_prefix.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m).
    + apply exec_buffer8_disabled_assert.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m).
      * apply exec_buffer8_disabled_assert.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
        -- apply exec_set. unfold le0, buffer8_write_temps; umul128_scalar.
        -- exact HLoop.
  - reflexivity.
  - reflexivity.
Qed.

Theorem eval_write_buffer8_layout m bi input bf base bw edge cursor tail
    (x : Ty.tySem (buffer_type (Word 3) 5)) :
  0 <= tail -> 0 <= input -> input + 63 <= Ptrofs.max_unsigned -> bi <> bf -> bi <> bw ->
  uint8_array_at m bi input (map word8_array_value (byte_chunks_values (buffer_byte_chunks 5 x))) ->
  write_frame_at m bf base bw edge cursor (510 + tail) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_write_buffer8)
      [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr input);
        Vlong (Int64.repr (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 x))))); Vint (Int.repr 5)]
      E0 mf Vundef /\
    frame_output_cells_at mf bw edge cursor (encode x) /\
    write_prefix_at m mf bw edge cursor /\
    write_frame_at mf bf base bw edge (cursor - 510) tail /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - 510) / 64)) (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HT HI HM Hif Hiw HA HW.
  set (le := PTree.set _i (Vlong (Int64.repr 32))
    (buffer8_write_temps bf base bi input (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 x)))))).
  assert (HIndex : le!_i = Some (Vlong (Int64.repr
    (buffer8_empty_index (map (fun c => Z.of_nat (fst c)) (buffer_byte_chunks 5 x)))))).
  { rewrite <- map_map, buffer_byte_chunks_counts. unfold le; apply PTree.gss. }
  destruct (exec_buffer8_write_loop_layout (buffer_byte_chunks 5 x) m le bi input bf base bw edge cursor tail
    (buffer_byte_chunks_sized 5 x) (buffer_byte_chunks_ordered 5 x) (buffer63_chunks_chain x)
    ltac:(unfold le, buffer8_write_temps; umul128_lookup)
    ltac:(unfold le, buffer8_write_temps; umul128_lookup)
    ltac:(unfold le, buffer8_write_temps; umul128_lookup) HIndex HT HI
    ltac:(rewrite buffer63_chunks_capacity; exact HM)
    ltac:(rewrite buffer63_chunks_capacity; change (63 <= 18446744073709551615); lia)
    Hif Hiw HA ltac:(rewrite buffer63_chunks_width; exact HW))
    as (mf & lef & HLoop & HCells & HPrefix & HFrame & HMemory & HPerm & HValid).
  rewrite buffer63_chunks_width in HFrame, HMemory.
  rewrite <- buffer_byte_chunks_cells in HCells.
  exists mf. split; [eapply eval_write_buffer8_from_loop; exact HLoop|].
  exact (conj HCells (conj HPrefix (conj HFrame (conj HMemory (conj HPerm HValid))))).
Qed.
