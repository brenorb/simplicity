(** The complete original [simplicity_hash_to_curve] against its frozen
    Simplicity assertion [hash_to_curve = assert hash_to_curve_core]
    (LibSecp256k1.hs:729--742,836--837), reduced exactly to one property of
    that specification.

    C rejects only digests that are not field elements; the specification
    additionally fails when the two accepted digests map to points whose sum is
    infinity.  This module proves, with the existing explicit memcpy/CTZ
    premises, that:
    - the public contract holds whenever every key with two accepted digests
      has a successful specification result ([hash_to_curve_accepted_finite]);
    - at any key with accepted digests and failing specification, the proved C
      call returns success while the specification's return is failure;
    - pointwise, the C return equals the specification's iff that key is not
      such a key.
    The property depends on two SHA-256 digests of each key and is neither
    proved nor refuted here: see [JET_SECP_HASH_TO_CURVE_MISMATCHES.md]. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.extraMath C.jet_memcpy_model C.jet_ctz_model C.jet_encoding C.jet_frame_layout
 C.jet_input_layout C.jet_output_layout C.jet_write_layout C.jet_frame_spec C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame
 C.jet_secp_linkage C.jets_secp C.jet_partial C.jet_secp_initialized_partial_contract
 C.jet_secp_field_cmov C.jet_secp_rescale_literal C.jet_secp_generator_hash_map
 C.jet_secp_sha_startup C.jet_secp_swu_startup C.jet_secp_generator_sha_absorb
 C.jet_secp_hash_public_call C.jet_secp_hash_to_curve_spec C.jet_secp_hash_to_curve_compare
 C.jet_clight_internal_preserve C.jet_clight_forward C.jet_secp_ctz_jets C.jet_secp_taptweak_writer_state
 C.jet_secp_sha_dispatch.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_hash_to_curve Simplicity.Translate.encode rescale_field_output.

(** * Startup state *)

Definition hash_ready (m : mem) : Prop :=
  secp_sha_startup m /\ swu_startup m /\ (forall prefix, generator_sha_prefix_state prefix m) /\
  taptweak_dispatch_extent m.

Theorem hash_ready_initial m : Genv.init_mem jets_secp.prog = Some m -> hash_ready m.
Proof.
  intro Init. split; [apply secp_sha_startup_initial; exact Init|].
  split; [apply swu_startup_initial; exact Init|].
  split; [intro prefix; apply generator_sha_prefix_initial; exact Init|].
  apply taptweak_dispatch_extent_initial; exact Init.
Qed.

(** An 8-byte block cannot hold a write frame of at least two words. *)
Lemma small_block_write_separate m bg hi bd base bw edge cursor N :
  hi <= 9 -> 64 < N -> block_extent m bg hi -> write_frame_at m bd base bw edge cursor N -> bw <> bg.
Proof.
  intros Small Big Bounds (Base & Fields & Edge & Count & Max & WriteCursor & Writes) Same; subst bw.
  destruct (Writes 0 ltac:(lia)) as (A0 & High0 & Apart0 & Write0 & Word0).
  destruct (Writes 64 ltac:(lia)) as (A64 & High64 & Apart64 & Write64 & Word64).
  pose proof (proj1 Write0 (write_cell_address edge cursor 0+7) ltac:(change
    (write_cell_address edge cursor 0<=write_cell_address edge cursor 0+7<write_cell_address edge cursor 0+8);lia)) as Top.
  pose proof (proj1 Write64 (write_cell_address edge cursor 64) ltac:(change
    (write_cell_address edge cursor 64<=write_cell_address edge cursor 64<write_cell_address edge cursor 64+8);lia)) as Bottom.
  pose proof (Bounds _ Cur Writable Top) as TopBound. pose proof (Bounds _ Cur Writable Bottom) as BottomBound.
  assert (Delta : write_cell_address edge cursor 0 = write_cell_address edge cursor 64 + 8).
  { unfold write_cell_address. replace (cursor-1-0) with (cursor-1) by lia.
    replace (cursor-1-64) with ((cursor-1)+(-1)*64) by lia.
    rewrite Z.div_add by lia. lia. }
  lia.
Qed.

Lemma secp_sha_startup_loads m mf : secp_sha_startup m -> mem_forward m mf ->
  Mem.load Mptr mf secp_sha_dispatch_block 0 = Mem.load Mptr m secp_sha_dispatch_block 0 ->
  Mem.load Mint64 mf secp_sha_counter_block 0 = Mem.load Mint64 m secp_sha_counter_block 0 ->
  secp_sha_startup mf.
Proof.
  intros [[Dispatch Counter] [NoWrite NoFree]] Forward LD LC.
  assert (VD : Mem.valid_block m secp_sha_dispatch_block).
  { unfold secp_sha_dispatch_ok in Dispatch. apply Mem.load_valid_access in Dispatch.
    eapply Mem.valid_access_valid_block; eapply Mem.valid_access_implies; [exact Dispatch|constructor]. }
  assert (VC : Mem.valid_block m secp_sha_counter_block).
  { apply Mem.load_valid_access in Counter.
    eapply Mem.valid_access_valid_block; eapply Mem.valid_access_implies; [exact Counter|constructor]. }
  split; [split|split].
  - unfold secp_sha_dispatch_ok in *. exact (eq_trans LD Dispatch).
  - exact (eq_trans LC Counter).
  - intros ofs Perm. apply (NoWrite ofs). exact (proj2 (Forward _ VC) ofs Writable Perm).
  - intros ofs Perm. apply (NoFree ofs). exact (proj2 (Forward _ VD) ofs Freeable Perm).
Qed.

(** * The open property and the C/specification comparison *)

(** Both generator digests are field elements (C's only rejection). *)
Notation hash_accepted key := (generator_hash_accepted false key && generator_hash_accepted true key).

(** Every key whose two digests are field elements has a successful
    specification result, i.e. its two mapped points do not sum to infinity. *)
Definition hash_to_curve_accepted_finite : Prop :=
  forall key, hash_accepted key = true ->
    @literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero) key <> None.

(** The proved C return agrees with the specification's exactly when the key
    is not an accepted key with failing specification. *)
Lemma hash_return_agreement_iff key (spec : option (Ty.tySem (Ty.Prod (Word 8) (Word 8)))) flag ox oy :
  spec = (if hash_accepted key
          then if Int.eq flag Int.zero then Some (rescale_field_output ox, rescale_field_output oy) else None
          else None) ->
  (Vint (cmov_int (hash_accepted key)) = jet_partial_return spec <->
   (hash_accepted key = true -> spec <> None)).
Proof.
  intros ->. destruct (hash_accepted key); [|split; [discriminate|reflexivity]].
  destruct (Int.eq flag Int.zero); cbn; split.
  - intros _ _; discriminate.
  - reflexivity.
  - intro E; discriminate E.
  - intro H; exfalso; exact (H eq_refl eq_refl).
Qed.

Section Public.
Context (Copy : memcpy_model) (Count : ctz_model).

Theorem hash_to_curve_public_compared env m bd base bs sbase bi bw edge outedge cursor rc
    (key : Ty.tySem (Word 8)) :
  hash_ready m -> frame_base_valid sbase -> (8|sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  frame_input_cells_at m bi edge rc (Simplicity.Translate.encode key) ->
  write_frame_at m bd base bw outedge cursor 512 ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_simplicity_hash_to_curve)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); env] E0 mf
      (Vint (cmov_int (hash_accepted key))) /\
    (Vint (cmov_int (hash_accepted key))
       = jet_partial_return (@literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero) key) <->
     (hash_accepted key = true -> @literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero) key <> None)) /\
    (hash_accepted key = true -> @literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero) key <> None ->
     match @literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero) key with
     | Some value => frame_output_cells_at mf bw outedge cursor (Simplicity.Translate.encode value) /\
         write_prefix_at m mf bw outedge cursor /\ frame_fields_at mf bd base bw outedge (cursor - 512)
     | None => True end) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - 512) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    hash_ready mf.
Proof.
  intros (SHA & SWU & Prefixes & Extent) Base Align Source RC Max Input Output.
  destruct (eval_hash_to_curve_compared Copy key env m bd base bs sbase bw outedge cursor 512 bi edge rc
    (ctz_model_count_calls Count) SHA SWU Prefixes Output ltac:(lia) Base Align Source Input RC Max)
    as (mf & sx & sy & sz & flag & ox & oy & Call & SpecEq & Value & Final & Frame & RO).
  pose (result := (if hash_accepted key
    then Some (rescale_field_output ox, rescale_field_output oy) else None)
    : option (Ty.tySem (Ty.Prod (Word 8) (Word 8)))).
  assert (FinalR : finv m bd base bw outedge cursor 512 bi mf
      (match result with Some _ => true | None => false end)
      (match result with Some value => Simplicity.Translate.encode value | None => [] end)).
  { unfold result. destruct (hash_accepted key); exact Final. }
  destruct (partial_frame_observations (Ty.Prod (Word 8) (Word 8)) m bd base bw outedge cursor 512 bi mf
    result FinalR Frame) as [Observe Loads].
  exists mf. split; [exact Call|]. split; [exact (hash_return_agreement_iff key _ flag ox oy SpecEq)|].
  split; [|split; [exact Loads|]].
  - intros Accepted Finite. rewrite SpecEq in Finite |- *. rewrite Accepted in Finite |- *.
    destruct (Int.eq flag Int.zero); [|contradiction].
    unfold result in Observe. rewrite Accepted in Observe. exact Observe.
  - destruct RO as [Forward Unchanged].
    assert (VD : Mem.valid_block m secp_sha_dispatch_block) by exact (proj1 Extent).
    assert (Sep : bw <> secp_sha_dispatch_block)
      by exact (small_block_write_separate m _ 8 bd base bw outedge cursor 512
        ltac:(lia) ltac:(lia) (proj2 Extent) Output).
    pose proof (proj1 Output) as BaseD. unfold frame_base_valid in BaseD.
    split; [|split; [eapply swu_startup_preserved; [exact SWU|split; assumption]|split]].
    + apply (secp_sha_startup_loads m mf SHA Forward).
      * apply Loads; [exact VD|right; left; change (size_chunk Mptr) with 8; lia|left; intro Same; exact (Sep (eq_sym Same))].
      * destruct SHA as [[_ Counter] [NoWrite _]].
        apply Mem.load_valid_access in Counter as CounterAccess.
        assert (VC : Mem.valid_block m secp_sha_counter_block)
          by (eapply Mem.valid_access_valid_block; eapply Mem.valid_access_implies;
              [exact CounterAccess|constructor]).
        rewrite Counter. eapply Mem.load_unchanged_on; [exact Unchanged| |exact Counter].
        intros i _. split; [exact VC|exact (NoWrite i)].
    + intro prefix. eapply generator_sha_prefix_preserved; [exact (Prefixes prefix)|split; assumption].
    + split; [exact (proj1 (Forward _ VD))|].
      eapply block_extent_forward; [exact VD|exact (proj2 Extent)|exact Forward].
Qed.

(** Equivalence with the frozen specification, conditional on the open
    property (a hypothesis, not an axiom). *)
Theorem hash_to_curve_initialized_local_spec_if_finite :
  hash_to_curve_accepted_finite ->
  secp_jet_initialized_partial_local_spec hash_ready f_simplicity_hash_to_curve (Word 8)
    (Ty.Prod (Word 8) (Word 8)) (@literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero)).
Proof.
  intros Finite env m bd base bs sbase bi bw edge outedge cursor rc key Ready Base Align Source RC Max Input Output.
  change (rc + 256 <= Int64.max_unsigned) in Max.
  change (write_frame_at m bd base bw outedge cursor 512) in Output.
  destruct (hash_to_curve_public_compared env m bd base bs sbase bi bw edge outedge cursor rc key
    Ready Base Align Source RC Max Input Output) as (mf & Call & Agree & Observe & Loads & ReadyF).
  exists mf. split.
  - rewrite <- (proj2 Agree (Finite key)). exact Call.
  - split; [|split; [exact Loads|exact ReadyF]].
    destruct (hash_accepted key) eqn:Accepted.
    + exact (Observe eq_refl (Finite key Accepted)).
    + assert (Fail : @literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero) key = None).
      { pose proof (proj2 Agree (fun H => ltac:(discriminate H))) as R.
        destruct (@literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero) key); [|reflexivity].
        exfalso. cbn [jet_partial_return cmov_int] in R.
        exact (Int.one_not_zero (eq_sym (f_equal (fun v => match v with Vint i => i | _ => Int.zero end) R))). }
      rewrite Fail. exact I.
Qed.

(** Divergence at any key with accepted digests and failing specification:
    the proved original call returns success, the specification failure. *)
Theorem hash_to_curve_differs_if_infinite env m bd base bs sbase bi bw edge outedge cursor rc
    (key : Ty.tySem (Word 8)) :
  hash_accepted key = true -> @literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero) key = None ->
  hash_ready m -> frame_base_valid sbase -> (8|sbase) -> frame_fields_at m bs sbase bi edge rc ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  frame_input_cells_at m bi edge rc (Simplicity.Translate.encode key) ->
  write_frame_at m bd base bw outedge cursor 512 ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_simplicity_hash_to_curve)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
    jet_partial_return (@literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero) key) = Vint Int.zero.
Proof.
  intros Accepted Fail Ready Base Align Source RC Max Input Output.
  destruct (hash_to_curve_public_compared env m bd base bs sbase bi bw edge outedge cursor rc key
    Ready Base Align Source RC Max Input Output) as (mf & Call & _).
  exists mf. rewrite Accepted in Call. split; [exact Call|]. rewrite Fail. reflexivity.
Qed.
End Public.
