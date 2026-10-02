(** Initial-only short-copy contracts for the actual helper and wrapper.
    The count fits in both current words, with a partially filled destination.
    Crossing/aligned cases are still required before counting any public jet. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_access C.jet_frame_constants.
Require Import C.jet_read8_layout C.jet_write_layout C.jet_output_layout C.jet_copyBits_exec.
Require Import C.jet_copyBits_helper_exec C.jet_copyBits_helper_right C.jet_copyBits_short_word.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_copy_helper_short m bd base bs sbase bi edge rc bw outedge cursor n old source :
  frame_base_valid sbase -> frame_base_valid base ->
  frame_fields_at m bs sbase bi edge rc -> frame_fields_at m bd base bw outedge cursor ->
  0 <= rc <= Int64.max_unsigned -> 1 <= cursor <= Int64.max_unsigned ->
  8 * (1 + rc / 64) <= edge <= Ptrofs.max_unsigned ->
  0 <= outedge -> write_word_address outedge cursor <= Ptrofs.max_unsigned ->
  0 < cursor mod 64 -> 0 < n <= 64 - rc mod 64 -> n <= cursor mod 64 ->
  bd <> bw ->
  (bi <> bw \/ edge - 8 * (1 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (1 + rc / 64)) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bw (write_word_address outedge cursor) = Some (Vlong old) ->
  Mem.valid_access m Mint64 bw (write_word_address outedge cursor) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_copyBitsHelper)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    Mem.load Mint64 mf bw (write_word_address outedge cursor) =
      Some (Vlong (copy_short_value (64 - rc mod 64) (cursor mod 64) old source)) /\
    frame_fields_at mf bd base bw outedge cursor /\
    (forall chunk b ofs, b <> bw \/ ofs + size_chunk chunk <= write_word_address outedge cursor \/
      write_word_address outedge cursor + 8 <= ofs -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HB HF HW HR HC HE HO HA Hpartial Hn Hnd Hbd Hsep Hsource Hold PW.
  unfold copy_short_value.
  destruct (zlt (64 - rc mod 64) (cursor mod 64)) as [Hleft|Hright].
  - eapply eval_copy_helper_short_left with (bi := bi) (edge := edge) (rc := rc)
      (old := old) (source := source); eassumption || lia.
  - eapply eval_copy_helper_short_right with (bi := bi) (edge := edge) (rc := rc)
      (old := old) (source := source); eassumption || lia.
Qed.

Theorem eval_copyBits_short m bd base bs sbase bi edge rc bw outedge cursor n old source :
  frame_base_valid sbase -> frame_base_valid base ->
  frame_fields_at m bs sbase bi edge rc -> frame_fields_at m bd base bw outedge cursor ->
  0 <= rc <= Int64.max_unsigned -> 1 <= cursor <= Int64.max_unsigned ->
  8 * (1 + rc / 64) <= edge <= Ptrofs.max_unsigned ->
  0 <= outedge -> write_word_address outedge cursor <= Ptrofs.max_unsigned ->
  0 < cursor mod 64 -> 0 < n <= 64 - rc mod 64 -> n <= cursor mod 64 ->
  bd <> bw ->
  (bi <> bw \/ edge - 8 * (1 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (1 + rc / 64)) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bw (write_word_address outedge cursor) = Some (Vlong old) ->
  Mem.valid_access m Mint64 bw (write_word_address outedge cursor) Writable ->
  Mem.valid_access m Mint64 bd (base + 8) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_copyBits)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    Mem.load Mint64 mf bw (write_word_address outedge cursor) =
      Some (Vlong (copy_short_value (64 - rc mod 64) (cursor mod 64) old source)) /\
    frame_fields_at mf bd base bw outedge (cursor - n) /\
    loads_outside_ranges m mf bd (base + 8) (base + 16)
      bw (write_word_address outedge cursor) (write_word_address outedge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HB HF HW HR HC HE HO HA Hpartial Hn Hnd Hbd Hsep Hsource Hold PW PC.
  assert (Hncursor : 0 < n <= cursor).
  { pose proof (Z.div_pos cursor 64 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_mod cursor 64 ltac:(lia)); lia. }
  destruct (eval_copy_helper_short m bd base bs sbase bi edge rc bw outedge cursor n old source
    HS HB HF HW HR HC HE HO HA Hpartial Hn Hnd Hbd Hsep Hsource Hold PW)
    as [mi [Hcall [Hword [Hfields [Houtside [Hperm Hvalid]]]]]].
  assert (PCi : Mem.valid_access mi Mint64 bd (base + 8) Writable).
  { destruct PC as [HP Halign]. split; [|exact Halign].
    intros ofs Hrange. apply Hperm. apply HP; exact Hrange. }
  destruct (eval_copyBits_nonzero_advances m mi bd base bs (Ptrofs.repr sbase)
    bw outedge cursor n HB Hncursor ltac:(lia) Hcall Hfields PCi)
    as [mf [Hwrapper [Hfieldsf [HcursorOutside [Hpermf Hvalidf]]]]].
  exists mf. split; [exact Hwrapper|]. split.
  - rewrite HcursorOutside; [exact Hword|left; congruence].
  - split; [exact Hfieldsf|]. split.
    + intros chunk b ofs Hcursor HwordOutside.
      rewrite HcursorOutside by exact Hcursor.
      apply Houtside; exact HwordOutside.
    + split.
      * intros b ofs kind p HP. apply Hpermf. apply Hperm; exact HP.
      * intros b HV. apply Hvalidf. apply Hvalid; exact HV.
Qed.
