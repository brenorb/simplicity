(** Evaluator-valid input/output separation, derived rather than assumed.
    The environment correspondence remains explicit and independent of input
    frame aliasing; actual calls preserve every other represented frame. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Maps Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_prim.
Require Import C.jet_elements_null_data_layout C.jet_elements_null_data_guard_compose.
Require Import C.jet_elements_null_data_output_guard C.jet_elements_null_data_index.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_encoding C.jet_application_sep.
Require Import C.jet_bitmachine_rep C.jet_context C.jet_read_after_write.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Local Notation OpcodeTy := (Ty.Sum (Ty.Prod (Word 1) (Word 8)) (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2))).

Definition bm_active_read_cursor s : Z :=
  read_padding (read_size (activeReadFrame s)) + Z.of_nat (length (prevData (activeReadFrame s))).

Lemma bm_active_read_encoded_prefix {A : Ty} (a : A) tail m L s :
  bm_rep m L s -> nextData (activeReadFrame s) = encode a ++ tail ->
  frame_base_valid (item_ofs (active_read_loc L)) /\ (8 | item_ofs (active_read_loc L)) /\
  frame_fields_at m (frames_blk L) (item_ofs (active_read_loc L)) (cells_blk L)
    (edge_ofs (active_read_loc L)) (bm_active_read_cursor s) /\
  0 <= bm_active_read_cursor s /\
  bm_active_read_cursor s + Z.of_nat (bitSize A) <= Int64.max_unsigned /\
  frame_input_cells_at m (cells_blk L) (edge_ofs (active_read_loc L)) (bm_active_read_cursor s) (encode a).
Proof.
  intros (_ & _ & HAR & _) HNext.
  unfold read_frame_rep in HAR.
  destruct HAR as (HB & HA & HF & HE & HM & HW & HC).
  assert (Hsize : read_size (activeReadFrame s) = Z.of_nat (length (prevData (activeReadFrame s))) +
      Z.of_nat (bitSize A) + Z.of_nat (length tail)).
  { unfold read_size. rewrite HNext, app_length, encode_length. lia. }
  assert (Hpad : 0 <= read_padding (read_size (activeReadFrame s))).
  { unfold read_padding. pose proof (frame_words_bounds (read_size (activeReadFrame s)) ltac:(lia)). lia. }
  split; [exact HB|]. split; [exact HA|]. split; [exact HF|].
  split; [unfold bm_active_read_cursor; lia|]. split; [unfold bm_active_read_cursor; lia|].
  rewrite HNext in HC. apply frame_input_cells_at_app in HC. destruct HC as [_ HC].
  apply frame_input_cells_at_app in HC. destruct HC as [HC _]. rewrite rev_length in HC. exact HC.
Qed.

Definition elements_null_data_bm_environment_case m bd dbase bw edge cur
    be ebase bt txbase bout outbase i (jw : Ty.tySem Word32) parsed unused_hash : Prop :=
  Z.of_nat (length parsed) <= Int64.max_unsigned /\
  elements_null_data_count_path m be ebase bt txbase bout outbase i (Int64.repr (Z.of_nat (length parsed))) /\
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur 261 b lo hi)
    (elements_null_data_count_footprint be ebase bt txbase bout outbase i) /\
  elements_null_data_selected_initial m bd dbase bw edge cur 261
    be ebase bt txbase bout outbase i (Int64.repr (toZ jw)) parsed unused_hash.

Definition bm_state_after_output s (cells : list Cell) : RunState :=
  {| inactiveReadFrames := inactiveReadFrames s;
     activeReadFrame := activeReadFrame s;
     activeWriteFrame := {| writeData := rev cells ++ writeData (activeWriteFrame s);
                            writeEmpty := (writeEmpty (activeWriteFrame s) - length cells)%nat |};
     inactiveWriteFrames := inactiveWriteFrames s |}.

Theorem elements_output_null_datum_bitmachine environment parsed unused_hash (iw jw : Ty.tySem Word32)
    m L s tail be ebase bt txbase bout outbase count flag :
  bm_rep m L s -> bm_separated L s -> active_write_writable m L s ->
  nextData (activeReadFrame s) = @encode (Ty.Prod Word32 Word32) (iw, jw) ++ tail ->
  (261 <= writeEmpty (activeWriteFrame s))%nat ->
  elements_null_data_output_rep m be ebase bt txbase bout outbase (Int64.repr (toZ iw)) count flag ->
  (andb (Int64.ltu (Int64.repr (toZ iw)) count) flag = true ->
    elements_null_data_bm_environment_case m (frames_blk L) (item_ofs (active_write_loc L))
      (cells_blk L) (edge_ofs (active_write_loc L)) (Z.of_nat (writeEmpty (activeWriteFrame s)))
      be ebase bt txbase bout outbase (Int64.repr (toZ iw)) jw parsed unused_hash) ->
  (match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ iw)) with
   | Some txo => txNullData (txoScript txo)
   | None => None
   end) = (if andb (Int64.ltu (Int64.repr (toZ iw)) count) flag then Some parsed else None) ->
  exists mf value,
    @elements_output_null_datum_spec (PrimitivePrimSem option_Monad_Zero) (iw, jw) environment = Some value /\
    Clight2.eval_funcall elements_ge m (Internal f_simplicity_output_null_datum)
      (jet_args (Vptr be (Ptrofs.repr ebase)) L) E0 mf (Vint Int.one) /\
    bm_rep mf L (bm_state_after_output s (@encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy)) value)).
Proof.
  intros HBM HSep [HV HW] HNext HSpace HOutput HEnv HLogical.
  pose proof HBM as (HBlocks & HIR & HAR & HAW & HIW).
  destruct (@bm_active_read_encoded_prefix (Ty.Prod Word32 Word32) (iw, jw) tail m L s HBM HNext)
    as (HSbase & HAlign & HFields & Hrc0 & HrcMax & HCells).
  apply frame_input_word_pair_encode in HCells. destruct HCells as [HI HJ].
  change (frame_input_word_at m (cells_blk L) (edge_ofs (active_read_loc L))
    (bm_active_read_cursor s + 32) jw) in HJ.
  assert (HF : write_frame_at m (frames_blk L) (item_ofs (active_write_loc L)) (cells_blk L)
    (edge_ofs (active_write_loc L)) (Z.of_nat (writeEmpty (activeWriteFrame s))) 261).
  { change 261 with (Z.of_nat 261).
    eapply write_frame_at_of_rep; [exact HSpace|exact HBlocks|exact HAW|exact HV|exact HW]. }
  assert (HPayload : andb (Int64.ltu (Int64.repr (toZ iw)) count) flag = true ->
    elements_null_data_layout_payload m (frames_blk L) (item_ofs (active_write_loc L)) (cells_blk L)
      (edge_ofs (active_write_loc L)) (Z.of_nat (writeEmpty (activeWriteFrame s)))
      (cells_blk L) (edge_ofs (active_read_loc L)) (bm_active_read_cursor s)
      be ebase bt txbase bout outbase (Int64.repr (toZ iw)) jw parsed unused_hash).
  { intros HG. specialize (HEnv HG) as (Hlen & HCount & HCsep & HSelected).
    unfold elements_null_data_layout_payload. split; [exact HJ|]. split.
    - intros k HK. unfold bm_active_read_cursor.
      replace (read_padding (read_size (activeReadFrame s)) + Z.of_nat (length (prevData (activeReadFrame s))) + 32 + k)
        with (read_padding (read_size (activeReadFrame s)) + (Z.of_nat (length (prevData (activeReadFrame s))) + 32 + k)) by lia.
      eapply bm_active_read_word_out_sep; [exact HBM|exact HSep|lia|].
      unfold read_size. rewrite HNext, app_length, encode_length.
      change (bitSize (Ty.Prod Word32 Word32)) with 64%nat. lia.
    - exact (conj Hlen (conj HCount (conj HCsep HSelected))). }
  destruct (elements_output_null_datum_initial_equivalence environment parsed unused_hash iw jw m
    (frames_blk L) (item_ofs (active_write_loc L)) (frames_blk L) (item_ofs (active_read_loc L))
    (cells_blk L) (cells_blk L) (edge_ofs (active_write_loc L)) (Z.of_nat (writeEmpty (activeWriteFrame s)))
    (edge_ofs (active_read_loc L)) (bm_active_read_cursor s) be ebase bt txbase bout outbase count flag
    HSbase HAlign HFields HI ltac:(change (bm_active_read_cursor s + 64 <= Int64.max_unsigned) in HrcMax; lia)
    HOutput HPayload HLogical HF) as (mf & value & HSem & HC & HO & HP & HFieldsF & HLoads).
  exists mf, value. split; [exact HSem|]. split; [exact HC|].
  set (out := @encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy)) value) in *.
  assert (Hlen : length out = 261%nat) by (unfold out; rewrite encode_length; reflexivity).
  set (n := (writeEmpty (activeWriteFrame s) - length out)%nat).
  assert (Hcur : Z.of_nat (length out + n) = Z.of_nat (writeEmpty (activeWriteFrame s))) by (unfold n; lia).
  assert (Hnext : Z.of_nat (writeEmpty (activeWriteFrame s)) - 261 = Z.of_nat n) by (unfold n; lia).
  unfold bm_state_after_output. fold out n.
  eapply bm_rep_after_write with (out := out) (wd := writeData (activeWriteFrame s)) (e := n);
    [|lia|exact HBM|exact HSep| | | |].
  - replace (length out + n)%nat with (writeEmpty (activeWriteFrame s)) by (unfold n; lia).
    destruct (activeWriteFrame s); reflexivity.
  - rewrite Hcur. exact HO.
  - rewrite Hcur. exact HP.
  - rewrite <- Hnext. exact HFieldsF.
  - rewrite Hcur, <- Hnext. exact HLoads.
Qed.
