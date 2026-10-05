(** Uniform initial-only frame contract for every positive copy up to 64
    bits.  The two paths that call plain libc [memcpy] use the explicit
    [memcpy_model] premise; everything else is the unconditional
    [eval_copyBits_small_no_memcpy_layout]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_encoding C.jet_context_separated C.jet_copyBits_separation.
Require Import C.jet_copyBits_short_cells C.jet_copyBits_loop_crossing C.jet_copyBits_small_layout C.jet_memcpy_model C.jet_copyBits_memcpy_cells.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 30.

Theorem eval_copyBits_small_layout (Hmodel : memcpy_model) m bd base bs sbase bi edge rc bw outedge cursor n cells :
  frame_base_valid sbase -> frame_fields_at m bs sbase bi edge rc ->
  write_frame_at m bd base bw outedge cursor n -> n = Z.of_nat (length cells) ->
  0 < n <= 64 ->
  jet_copy_buffers_separated bd bi bw edge outedge cursor rc n ->
  frame_input_cells_at m bi edge rc cells ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_copyBits)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    frame_output_cells_at mf bw outedge cursor cells /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd base bw outedge (cursor - n) /\
    loads_outside_ranges m mf bd (base + 8) (base + 16)
      bw (outedge + 8 * ((cursor - n) / 64)) (write_word_address outedge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HF Hwrite Hlen Hn Hsep Hinput.
  assert (Hdec : copy_small_memcpy_case rc cursor n \/ ~ copy_small_memcpy_case rc cursor n)
    by (unfold copy_small_memcpy_case; lia).
  destruct Hdec as [Hcase|Hno];
    [|eapply eval_copyBits_small_no_memcpy_layout; eassumption].
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hcm.
  pose proof Hwrite as HWC. destruct HWC as [_ [_ [_ [Hcapacity _]]]].
  destruct (copy_input_cells_head m bi edge rc cells ltac:(lia) Hinput) as [HR Hrest].
  pose proof (copy_buffers_separated_words bd bi bw edge outedge cursor rc n 0 0 Hsep
    ltac:(lia) ltac:(lia) ltac:(lia)) as Hsephead.
  rewrite Z.add_0_r, Z.sub_0_r in Hsephead.
  destruct Hcase as [[Hcz Hrz]|[Hpartial [Hss Hlt]]].
  - rewrite (copy_small_aligned_low outedge cursor n Hcz Hn).
    eapply eval_copyBits_memcpy_aligned_layout; try eassumption; lia.
  - rewrite (copy_small_crossing_low outedge cursor n Hpartial ltac:(lia)).
    eapply eval_copyBits_memcpy_equal_layout; try eassumption; lia.
Qed.
