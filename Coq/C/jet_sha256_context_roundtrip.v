(** Actual reader and writer calls composed from initial memory on the
    successful count domain. This is shared serialization infrastructure,
    not a generated public jet function or complete public jet coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_encoding C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_buffer_empty_spec C.jet_buffer_input.
Require Import C.jet_sha256_max_counter C.jet_readBit_layout C.jet_read_sha256_overflow.
Require Import C.jet_read_sha256_context_initial C.jet_write_sha256_context_canonical.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_sha256_context_roundtrip m bs sbase bi edge rc bc cbase bo output bd dbase bw outedge cursor
    (buf : Ty.tySem (buffer_type (Word 3) 5)) (count : Ty.tySem (Word 6)) (state : Ty.tySem (Word 8)) :
  @toZ (WordToZ 6) count < 36028797018963968 ->
  sha256_max_counter_at m ->
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned ->
  Mem.range_perm m bc (cbase + 16) (cbase + 79) Cur Writable ->
  Mem.valid_access m Mint64 bc (cbase + 8) Writable ->
  Mem.valid_access m Mint8unsigned bc (cbase + 80) Writable ->
  Mem.load Mptr m bc cbase = Some (Vptr bo (Ptrofs.repr output)) ->
  0 <= output -> output + 32 <= Ptrofs.max_unsigned -> (4 | output) ->
  Mem.range_perm m bo output (output + 32) Cur Writable ->
  bs <> bc -> bs <> bi -> bc <> bi -> bo <> bs -> bo <> bi -> bo <> bc ->
  frame_base_valid sbase -> 0 <= rc -> rc + 830 <= Int64.max_unsigned ->
  frame_fields_at m bs sbase bi edge rc -> Mem.valid_access m Mint64 bs (sbase + 8) Writable ->
  frame_input_cells_at m bi edge rc (encode buf ++ encode count ++ encode state) ->
  bd <> bs -> bd <> bc -> bd <> bo -> bw <> bs -> bw <> bc -> bw <> bo ->
  write_frame_at m bd dbase bw outedge cursor 830 ->
  exists mr mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_read_sha256_context)
      [Vptr bc (Ptrofs.repr cbase); Vptr bs (Ptrofs.repr sbase)] E0 mr (Vint Int.one) /\
    Clight2.eval_funcall ge0 mr (Internal f_simplicity_write_sha256_context)
      [Vptr bd (Ptrofs.repr dbase); Vptr bc (Ptrofs.repr cbase)] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw outedge cursor
      (@encode (Ty.Prod (buffer_type (Word 3) 5) (Ty.Prod (Word 6) (Word 8))) (buf,(count,state))) /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd dbase bw outedge (cursor - 830) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bs \/ ofs + size_chunk chunk <= sbase + 8 \/ sbase + 16 <= ofs) ->
      (b <> bc \/ ofs + size_chunk chunk <= cbase + 8 \/ cbase + 81 <= ofs) ->
      (b <> bo \/ ofs + size_chunk chunk <= output \/ output + 32 <= ofs) ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - 830) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HCount HGlobal HB HM HBufP HCtxW HOverW HO HO0 HOM HOA HOutP
    Hsc Hsi Hci Hos Hoi Hoc Hbase HR HMax HS HW HCells
    Hds Hdc Hdo Hws Hwc Hwo HWrite.
  destruct (eval_read_sha256_context_initial_layout m bs sbase bi edge rc bc cbase bo output buf count state
    HGlobal HB HM HBufP HCtxW HOverW HO HO0 HOM HOA HOutP Hsc Hsi Hci Hos Hoi Hoc Hbase HR HMax HS HW HCells)
    as (mr & r & HRead & Hr & HOutput & HBuf & HState & HCounter & HOverflow & HSrc & HLimit & HPermR & HMemR).
  assert (HFalse : sha256_read_overflow r = Datatypes.false).
  { apply sha256_read_overflow_false; rewrite Hr; exact HCount. }
  rewrite HFalse in HRead, HOverflow.
  assert (HLoads : forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mr b ofs = Some v).
  { intros chunk b ofs v HWhich HL.
    assert (HV : Mem.valid_block m b).
    { eapply Mem.perm_valid_block.
      eapply (Mem.valid_access_perm m chunk b ofs Cur Readable).
      eapply Mem.load_valid_access; exact HL. }
    rewrite HMemR; [exact HL|exact HV| | | ];
      left; destruct HWhich; subst; congruence. }
  assert (HWriteR : write_frame_at mr bd dbase bw outedge cursor 830).
  { eapply write_frame_at_preserved; [exact HLoads|exact HPermR|exact HWrite]. }
  destruct (eval_write_sha256_context_canonical mr bd dbase bw outedge cursor bc cbase bo output
    r Datatypes.false buf count state Hr HCount HB HM HO0 HOM ltac:(congruence) ltac:(congruence)
    ltac:(congruence) ltac:(congruence) HCounter HOutput HOverflow HBuf HState HWriteR)
    as (mf & HCall & HEncoded & HPrefix & HFields & HMemW & HPermW & HValidW).
  exists mr, mf. split; [exact HRead|]. split; [exact HCall|]. split; [exact HEncoded|]. split.
  - intros old HL. apply HPrefix. eapply HLoads; [right; reflexivity|exact HL].
  - split; [exact HFields|]. split.
    + intros b ofs kind p HP. apply HPermW, HPermR; exact HP.
    + intros chunk b ofs HV Hbs Hbc Hbo Hbd Hbw.
      rewrite HMemW by assumption. apply HMemR; assumption.
Qed.
