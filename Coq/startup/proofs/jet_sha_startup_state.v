(** One startup invariant for every SHA-unit jet.

    The archived startup work ([JetStartupReview], the unaccepted sources of
    [proof-work/sha-support], and its restatement [jet_sha_startup_globals])
    derives the dispatch pointer and the maximum counter from the program's
    own initializers and preserves them through the context jets.  The remaining consumers ([tapdata_init], the taproot
    builders and the hash jets composed from them) also read three static
    tag-name arrays.  This module

    - derives those arrays' contents and extents from [Genv.init_mem] of the
      actual SHA translation unit;
    - packages them with the persistent global state as [sha_startup_state];
    - shows the state survives any call whose effect is the public jet frame
      contract with an output wider than one word, without any separation
      premise supplied by the caller: two of the arrays are *writable* C
      objects, so their disjointness from the output frame is derived from
      the frame's own extent (an 8- or 10-byte object cannot hold two frame
      words or a frame record);
    - turns the accepted contract shapes into contracts that take the
      invariant as their only state premise and re-establish it. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Globalenvs Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_partial C.jet_frame_spec C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_write_layout C.jet_encoding C.jet_application_sep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local.
Require Import C.jet_sha_uchars_exec C.jet_sha_add_n_exec C.jet_sha_ctx8_add_jets.
Require Import C.jet_sha_tapdata_spec C.jet_sha_tapdata_jet.
Require Import C.jet_bitcoin_make_tapleaf_exec C.jet_bitcoin_make_tapbranch_exec.
Require Import JetStartupReview.jet_clight_forward JetStartupReview.jet_sha_initial_globals.
Require Import JetStartup.jet_sha_startup_globals.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 30.

(** ** Initial contents and extent of the tag arrays *)

Lemma sha_tagName_var_info :
  Genv.find_var_info (Genv.globalenv jets_sha.prog) (sha_symbol_block _tagName) =
    Some v_tagName.
Proof. vm_compute; reflexivity. Qed.

Lemma sha_tapleaf_tag_var_info :
  Genv.find_var_info (Genv.globalenv jets_sha.prog) (sha_symbol_block _tagName__1) =
    Some v_tagName__1.
Proof. vm_compute; reflexivity. Qed.

Lemma sha_tapbranch_tag_var_info :
  Genv.find_var_info (Genv.globalenv jets_sha.prog) (sha_symbol_block _tagName__2) =
    Some v_tagName__2.
Proof. vm_compute; reflexivity. Qed.

Local Opaque jets_sha.prog.

Definition sha_tag_extents (m : mem) : Prop :=
  (forall ofs p, Mem.perm m (sha_symbol_block _tagName) ofs Max p -> 0 <= ofs < 8) /\
  (forall ofs p, Mem.perm m (sha_symbol_block _tagName__1) ofs Max p -> 0 <= ofs < 8) /\
  (forall ofs p, Mem.perm m (sha_symbol_block _tagName__2) ofs Max p -> 0 <= ofs < 10).

Definition sha_tags_state (m : mem) : Prop :=
  sha_tag_ok m /\ sha_tapleaf_tag_ok m /\ sha_tapbranch_tag_ok m /\ sha_tag_extents m.

Theorem sha_tag_initialized m :
  Genv.init_mem jets_sha.prog = Some m -> sha_tag_ok m.
Proof.
  intros HInit.
  destruct (Genv.init_mem_characterization jets_sha.prog
    (sha_symbol_block _tagName) sha_tagName_var_info HInit) as [_ [_ [HLoad _]]].
  specialize (HLoad eq_refl).
  destruct HLoad as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & _).
  intros i Hi.
  destruct i as [|[|[|[|[|[|[|i]]]]]]];
    [exact H0|exact H1|exact H2|exact H3|exact H4|exact H5|exact H6|lia].
Qed.

Theorem sha_tapleaf_tag_initialized m :
  Genv.init_mem jets_sha.prog = Some m -> sha_tapleaf_tag_ok m.
Proof.
  intros HInit.
  destruct (Genv.init_mem_characterization jets_sha.prog
    (sha_symbol_block _tagName__1) sha_tapleaf_tag_var_info HInit) as [_ [_ [HLoad _]]].
  specialize (HLoad eq_refl).
  destruct HLoad as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & _).
  intros i Hi.
  destruct i as [|[|[|[|[|[|[|i]]]]]]];
    [exact H0|exact H1|exact H2|exact H3|exact H4|exact H5|exact H6|lia].
Qed.

Theorem sha_tapbranch_tag_initialized m :
  Genv.init_mem jets_sha.prog = Some m -> sha_tapbranch_tag_ok m.
Proof.
  intros HInit.
  destruct (Genv.init_mem_characterization jets_sha.prog
    (sha_symbol_block _tagName__2) sha_tapbranch_tag_var_info HInit) as [_ [_ [HLoad _]]].
  specialize (HLoad eq_refl).
  destruct HLoad as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _).
  intros i Hi.
  destruct i as [|[|[|[|[|[|[|[|[|i]]]]]]]]];
    [exact H0|exact H1|exact H2|exact H3|exact H4|exact H5|exact H6|exact H7|exact H8|lia].
Qed.

Theorem sha_tag_extents_initialized m :
  Genv.init_mem jets_sha.prog = Some m -> sha_tag_extents m.
Proof.
  intros HInit. split; [|split]; intros ofs p HP.
  - destruct (Genv.init_mem_characterization jets_sha.prog
      (sha_symbol_block _tagName) sha_tagName_var_info HInit) as [_ [HOnly _]].
    exact (proj1 (HOnly ofs Max p HP)).
  - destruct (Genv.init_mem_characterization jets_sha.prog
      (sha_symbol_block _tagName__1) sha_tapleaf_tag_var_info HInit) as [_ [HOnly _]].
    exact (proj1 (HOnly ofs Max p HP)).
  - destruct (Genv.init_mem_characterization jets_sha.prog
      (sha_symbol_block _tagName__2) sha_tapbranch_tag_var_info HInit) as [_ [HOnly _]].
    exact (proj1 (HOnly ofs Max p HP)).
Qed.

Theorem sha_tags_state_initialized m :
  Genv.init_mem jets_sha.prog = Some m -> sha_tags_state m.
Proof.
  intros HInit. split; [|split; [|split]].
  - exact (sha_tag_initialized m HInit).
  - exact (sha_tapleaf_tag_initialized m HInit).
  - exact (sha_tapbranch_tag_initialized m HInit).
  - exact (sha_tag_extents_initialized m HInit).
Qed.

(** ** The invariant *)

Definition sha_startup_state (m : mem) : Prop :=
  sha_persistent_global_state m /\ sha_tags_state m.

Theorem sha_startup_state_initialized m :
  Genv.init_mem jets_sha.prog = Some m -> sha_startup_state m.
Proof.
  intros HInit. split.
  - exact (sha_persistent_globals_initialized m HInit).
  - exact (sha_tags_state_initialized m HInit).
Qed.

Lemma sha_startup_state_globals m : sha_startup_state m -> sha_globals_ok m.
Proof. intros [[H _] _]; exact H. Qed.

Lemma sha_startup_state_dispatch m : sha_startup_state m -> sha_dispatch_ok m.
Proof. intros H; exact (proj1 (sha_startup_state_globals m H)). Qed.

Lemma sha_startup_state_tapdata m :
  sha_startup_state m -> sha_globals_ok m /\ sha_tag_ok m.
Proof. intros [[H _] [HT _]]; split; assumption. Qed.

Lemma sha_startup_state_tapleaf m :
  sha_startup_state m -> sha_globals_ok m /\ sha_tapleaf_tag_ok m.
Proof. intros [[H _] [_ [HT _]]]; split; assumption. Qed.

Lemma sha_startup_state_tapbranch m :
  sha_startup_state m -> sha_globals_ok m /\ sha_tapbranch_tag_ok m.
Proof. intros [[H _] [_ [_ [HT _]]]]; split; assumption. Qed.

(** ** Separation derived from the frame's own extent *)

(** An object of at most 10 bytes is neither the frame record nor the word
    buffer of an output frame of more than 64 cells. *)
Lemma small_object_not_wide_frame m b bound bf base bw edge cursor count :
  (forall ofs p, Mem.perm m b ofs Max p -> 0 <= ofs < bound) -> bound <= 10 ->
  64 < count -> write_frame_at m bf base bw edge cursor count ->
  bf <> b /\ bw <> b.
Proof.
  intros HBounds HSmall HCount (HBase & _ & _ & _ & _ & HRecord & HCells).
  split; intro HSame; subst b.
  - destruct HRecord as [HRange _].
    assert (HP : Mem.perm m bf (base + 8 + 7) Cur Writable).
    { apply HRange. cbn. lia. }
    pose proof (HBounds _ _ (Mem.perm_cur_max _ _ _ _ HP)) as HIn.
    destruct HBase as [HBase _]. lia.
  - destruct (HCells 0 ltac:(lia)) as (_ & _ & _ & [HRange0 _] & _).
    destruct (HCells 64 ltac:(lia)) as (HLow & _ & _ & _ & _).
    unfold write_cell_address in HRange0, HLow.
    assert (HDiv : (cursor - 1 - 64) / 64 = (cursor - 1 - 0) / 64 - 1).
    { replace (cursor - 1 - 64) with (cursor - 1 - 0 + (-1) * 64) by lia.
      rewrite Z.div_add by lia. lia. }
    rewrite HDiv in HLow.
    assert (HP : Mem.perm m bw (edge + 8 * ((cursor - 1 - 0) / 64) + 7) Cur Writable).
    { apply HRange0. cbn. lia. }
    pose proof (HBounds _ _ (Mem.perm_cur_max _ _ _ _ HP)) as HIn.
    lia.
Qed.

Lemma tag_block_valid m b ofs v :
  Mem.load Mint8unsigned m b ofs = Some v -> Mem.valid_block m b.
Proof.
  intros HL. eapply Mem.perm_valid_block with (ofs := ofs) (k := Cur) (p := Readable).
  eapply (Mem.valid_access_perm m Mint8unsigned b ofs Cur Readable).
  eapply Mem.load_valid_access; exact HL.
Qed.

Section FrameCall.
Variables (m mf : mem) (bf : block) (base : Z) (bw : block) (edge cursor count : Z).
Hypothesis HForward : mem_forward m mf.
Hypothesis HCount : 64 < count.
Hypothesis HFrame : write_frame_at m bf base bw edge cursor count.
Hypothesis HLoads : forall chunk b ofs, Mem.valid_block m b ->
  (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
  (b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cursor - count) / 64) \/
    write_word_address edge cursor + 8 <= ofs) ->
  Mem.load chunk mf b ofs = Mem.load chunk m b ofs.

Lemma small_object_loads_preserved b bound ofs v :
  (forall o p, Mem.perm m b o Max p -> 0 <= o < bound) -> bound <= 10 ->
  Mem.load Mint8unsigned m b ofs = Some v ->
  Mem.load Mint8unsigned mf b ofs = Some v.
Proof.
  intros HBounds HSmall HL.
  destruct (small_object_not_wide_frame m b bound bf base bw edge cursor count
    HBounds HSmall HCount HFrame) as [HF HW].
  rewrite HLoads; [exact HL| |left; congruence|left; congruence].
  eapply tag_block_valid; exact HL.
Qed.

Lemma small_object_extent_preserved b bound v :
  Mem.load Mint8unsigned m b 0 = Some v ->
  (forall o p, Mem.perm m b o Max p -> 0 <= o < bound) ->
  (forall o p, Mem.perm mf b o Max p -> 0 <= o < bound).
Proof.
  intros HL HBounds o p HP. apply (HBounds o p).
  exact (proj2 (HForward b (tag_block_valid m b 0 v HL)) o p HP).
Qed.

Theorem sha_tags_state_frame_call : sha_tags_state m -> sha_tags_state mf.
Proof.
  intros (HT & HL & HB & HE1 & HE2 & HE3).
  split; [|split; [|split; [|split; [|split]]]].
  - intros i Hi. eapply small_object_loads_preserved; [exact HE1|lia|exact (HT i Hi)].
  - intros i Hi. eapply small_object_loads_preserved; [exact HE2|lia|exact (HL i Hi)].
  - intros i Hi. eapply small_object_loads_preserved; [exact HE3|lia|exact (HB i Hi)].
  - eapply small_object_extent_preserved; [exact (HT 0%nat ltac:(lia))|exact HE1].
  - eapply small_object_extent_preserved; [exact (HL 0%nat ltac:(lia))|exact HE2].
  - eapply small_object_extent_preserved; [exact (HB 0%nat ltac:(lia))|exact HE3].
Qed.

Theorem sha_startup_state_frame_call : sha_startup_state m -> sha_startup_state mf.
Proof.
  intros [HGlobals HTags]. split.
  - eapply sha_persistent_globals_forward; [exact HGlobals|exact HForward|].
    eapply sha_globals_from_public_frame_observations;
      [apply sha_persistent_globals_original; exact HGlobals| |exact HFrame|exact HLoads].
    lia.
  - exact (sha_tags_state_frame_call HTags).
Qed.
End FrameCall.

(** ** Contracts over the invariant *)

(** Total jets: the accepted conclusion plus the invariant in the final
    memory; the invariant is the only state premise. *)
Definition sha_startup_total_spec (f : function) (A B : Ty) (spec : A -> B) : Prop :=
  forall env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A),
    sha_startup_state m ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    exists mf,
      Clight2.eval_funcall sha_ge m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
        E0 mf (Vint Int.one) /\
      frame_output_cells_at mf bw outedge cursor (encode (spec a)) /\
      write_prefix_at m mf bw outedge cursor /\
      frame_fields_at mf bd dbase bw outedge (cursor - Z.of_nat (bitSize B)) /\
      (forall chunk b ofs, Mem.valid_block m b ->
        (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
        (b <> bw \/
          ofs + size_chunk chunk <= outedge + 8 * ((cursor - Z.of_nat (bitSize B)) / 64) \/
          write_word_address outedge cursor + 8 <= ofs) ->
        Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
      sha_startup_state mf.

Theorem sha_startup_total_from_pre (pre : mem -> Prop) f A B spec :
  64 < Z.of_nat (bitSize B) ->
  (forall m, sha_startup_state m -> pre m) ->
  sha_jet_local_spec_pre pre f A B spec ->
  sha_startup_total_spec f A B spec.
Proof.
  intros HWide HPre HLocal env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HState HBase HAlign HFields HCursor HMax HInput HOutput.
  destruct (HLocal env m bd dbase bs sbase bi bw edge outedge cursor rc a
    (HPre m HState) HBase HAlign HFields HCursor HMax HInput HOutput)
    as [mf [HCall [HOut [HPrefix [HFinal HLoads]]]]].
  exists mf. repeat (split; [assumption|]).
  eapply sha_startup_state_frame_call; [|exact HWide|exact HOutput|exact HLoads|exact HState].
  exact (proj2 (clight_exec_forward sha_ge) _ _ _ _ _ _ HCall).
Qed.

Theorem sha_startup_total_from_local f A B spec :
  64 < Z.of_nat (bitSize B) ->
  sha_jet_local_spec f A B spec ->
  sha_startup_total_spec f A B spec.
Proof.
  intros HWide HLocal env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HState HBase HAlign HFields HCursor HMax HInput HOutput.
  destruct (HLocal env m bd dbase bs sbase bi bw edge outedge cursor rc a
    (sha_startup_state_dispatch m HState) HBase HAlign HFields HCursor HMax HInput HOutput)
    as [mf [HCall [HOut [HPrefix [HFinal HLoads]]]]].
  exists mf. repeat (split; [assumption|]).
  eapply sha_startup_state_frame_call; [|exact HWide|exact HOutput|exact HLoads|exact HState].
  exact (proj2 (clight_exec_forward sha_ge) _ _ _ _ _ _ HCall).
Qed.

(** Partial (assertion) jets: the invariant is re-established on success and
    on failure. *)
Definition sha_startup_partial_spec (f : function) (A B : Ty) (spec : A -> option B) : Prop :=
  forall env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A),
    sha_startup_state m ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    exists mf,
      Clight2.eval_funcall sha_ge m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
        E0 mf (jet_partial_return (spec a)) /\
      (match spec a with
       | Some b => frame_output_cells_at mf bw outedge cursor (encode b) /\
           write_prefix_at m mf bw outedge cursor /\
           frame_fields_at mf bd dbase bw outedge (cursor - Z.of_nat (bitSize B))
       | None => True
       end) /\
      (forall chunk b ofs, Mem.valid_block m b ->
        (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
        (b <> bw \/
          ofs + size_chunk chunk <= outedge + 8 * ((cursor - Z.of_nat (bitSize B)) / 64) \/
          write_word_address outedge cursor + 8 <= ofs) ->
        Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
      sha_startup_state mf.

Theorem sha_startup_partial_from_local f A B spec :
  64 < Z.of_nat (bitSize B) ->
  sha_jet_partial_local_spec f A B spec ->
  sha_startup_partial_spec f A B spec.
Proof.
  intros HWide HLocal env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HState HBase HAlign HFields HCursor HMax HInput HOutput.
  destruct (HLocal env m bd dbase bs sbase bi bw edge outedge cursor rc a
    (sha_startup_state_globals m HState) HBase HAlign HFields HCursor HMax HInput HOutput)
    as [mf [HCall [HResult HLoads]]].
  exists mf. repeat (split; [assumption|]).
  eapply sha_startup_state_frame_call; [|exact HWide|exact HOutput|exact HLoads|exact HState].
  exact (proj2 (clight_exec_forward sha_ge) _ _ _ _ _ _ HCall).
Qed.

(** Environment-reading jets: the accepted application contract (logical
    environment, representation relation and its separation footprint are
    unchanged) with the invariant carried through. *)
Definition sha_startup_application_spec (f : function) (E : Set) (A B : Ty)
    (env_rep : mem -> val -> E -> list (block * Z * Z) -> Prop)
    (spec : A -> E -> option B) : Prop :=
  forall logical_env env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A) fp,
    sha_startup_state m ->
    env_rep m env logical_env fp ->
    Forall (fun '(b, lo, hi) => out_sep bd dbase bw outedge cursor (Z.of_nat (bitSize B)) b lo hi) fp ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    exists mf value,
      spec a logical_env = Some value /\
      Clight2.eval_funcall sha_ge m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
        E0 mf (Vint Int.one) /\
      frame_output_cells_at mf bw outedge cursor (encode value) /\
      write_prefix_at m mf bw outedge cursor /\
      frame_fields_at mf bd dbase bw outedge (cursor - Z.of_nat (bitSize B)) /\
      (forall chunk b ofs, Mem.valid_block m b ->
        (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
        (b <> bw \/
          ofs + size_chunk chunk <= outedge + 8 * ((cursor - Z.of_nat (bitSize B)) / 64) \/
          write_word_address outedge cursor + 8 <= ofs) ->
        Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
      sha_startup_state mf.

Theorem sha_startup_application_from_sep f (E : Set) A B env_rep spec :
  64 < Z.of_nat (bitSize B) ->
  application_jet_local_spec_sep f sha_ge E A B env_rep spec ->
  sha_startup_application_spec f E A B env_rep spec.
Proof.
  intros HWide HLocal logical_env env m bd dbase bs sbase bi bw edge outedge cursor rc a fp
    HState HRep HSep HBase HAlign HFields HCursor HMax HInput HOutput.
  destruct (HLocal logical_env env m bd dbase bs sbase bi bw edge outedge cursor rc a fp
    HRep HSep HBase HAlign HFields HCursor HMax HInput HOutput)
    as [mf [value [HSpec [HCall [HOut [HPrefix [HFinal HLoads]]]]]]].
  exists mf, value. repeat (split; [assumption|]).
  eapply sha_startup_state_frame_call; [|exact HWide|exact HOutput|exact HLoads|exact HState].
  exact (proj2 (clight_exec_forward sha_ge) _ _ _ _ _ _ HCall).
Qed.
