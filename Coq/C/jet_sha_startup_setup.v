(** The startup invariant through the memory operations of a caller.

    [sha_startup_state] depends on five global objects only.  It survives any
    memory transition that is forward (no block is invalidated, maximal
    permissions do not grow) and leaves loads from those five blocks
    unchanged.  The standard operations a caller uses to build and discard
    frames satisfy this whenever they do not write the five blocks, and a
    freshly allocated block is never one of them.  Together with
    [sha_startup_state_initialized] and the per-jet contracts, this gives the
    invariant at every jet call of an execution that starts in the program's
    initial memory and whose setup writes only memory it allocated. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Globalenvs Events.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local.
Require Import C.jet_sha_uchars_exec C.jet_sha_add_n_exec.
Require Import C.jet_sha_tapdata_spec C.jet_sha_tapdata_jet.
Require Import C.jet_bitcoin_make_tapleaf_exec C.jet_bitcoin_make_tapbranch_exec.
Require Import C.jet_clight_forward C.jet_sha_initial_globals.
Require Import C.jet_sha_startup_globals C.jet_sha_startup_state.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 30.

Definition sha_state_blocks : list block :=
  [sha_symbol_block _simplicity_sha256_compression; sha_symbol_block _sha256_max_counter;
   sha_symbol_block _tagName; sha_symbol_block _tagName__1; sha_symbol_block _tagName__2].

Lemma sha_state_blocks_valid m b :
  sha_startup_state m -> In b sha_state_blocks -> Mem.valid_block m b.
Proof.
  intros [[[HD HC] _] (HT & HL & HB & _)] HIn.
  destruct HIn as [<-|[<-|[<-|[<-|[<-|[]]]]]].
  - eapply Mem.perm_valid_block with (ofs := 0) (k := Cur) (p := Readable).
    eapply (Mem.valid_access_perm m Mptr _ 0 Cur Readable).
    eapply Mem.load_valid_access; exact HD.
  - eapply Mem.perm_valid_block with (ofs := 0) (k := Cur) (p := Readable).
    eapply (Mem.valid_access_perm m Mint64 _ 0 Cur Readable).
    eapply Mem.load_valid_access; exact HC.
  - exact (tag_block_valid m _ _ _ (HT 0%nat ltac:(lia))).
  - exact (tag_block_valid m _ _ _ (HL 0%nat ltac:(lia))).
  - exact (tag_block_valid m _ _ _ (HB 0%nat ltac:(lia))).
Qed.

Theorem sha_startup_state_preserved m mf :
  sha_startup_state m -> mem_forward m mf ->
  (forall chunk b ofs, In b sha_state_blocks ->
    Mem.load chunk mf b ofs = Mem.load chunk m b ofs) ->
  sha_startup_state mf.
Proof.
  intros HState HForward HLoads.
  pose proof (sha_state_blocks_valid m) as HValid.
  destruct HState as [HGlobals (HT & HL & HB & HE1 & HE2 & HE3)].
  split.
  - eapply sha_persistent_globals_forward; [exact HGlobals|exact HForward|].
    destruct HGlobals as [[HD HC] _]. split.
    + unfold sha_dispatch_ok in *. rewrite HLoads; [exact HD|cbn; tauto].
    + rewrite HLoads; [exact HC|cbn; tauto].
  - assert (HV : forall b, In b sha_state_blocks -> Mem.valid_block m b).
    { intros b HIn. apply HValid; [|exact HIn].
      exact (conj HGlobals (conj HT (conj HL (conj HB (conj HE1 (conj HE2 HE3)))))). }
    split; [|split; [|split; [|split; [|split]]]].
    + intros i Hi. rewrite HLoads; [exact (HT i Hi)|cbn; tauto].
    + intros i Hi. rewrite HLoads; [exact (HL i Hi)|cbn; tauto].
    + intros i Hi. rewrite HLoads; [exact (HB i Hi)|cbn; tauto].
    + intros o p HP. apply (HE1 o p).
      exact (proj2 (HForward _ (HV (sha_symbol_block _tagName) ltac:(cbn; tauto))) o p HP).
    + intros o p HP. apply (HE2 o p).
      exact (proj2 (HForward _ (HV (sha_symbol_block _tagName__1) ltac:(cbn; tauto))) o p HP).
    + intros o p HP. apply (HE3 o p).
      exact (proj2 (HForward _ (HV (sha_symbol_block _tagName__2) ltac:(cbn; tauto))) o p HP).
Qed.

(** Allocation: the invariant holds afterwards and the new block is not one
    of the state objects. *)
Theorem sha_startup_state_alloc m mf lo hi fresh :
  sha_startup_state m -> Mem.alloc m lo hi = (mf, fresh) ->
  sha_startup_state mf /\ ~ In fresh sha_state_blocks.
Proof.
  intros HState HA. split.
  - eapply sha_startup_state_preserved; [exact HState|eapply alloc_forward; exact HA|].
    intros chunk b ofs HIn. eapply Mem.load_alloc_unchanged; [exact HA|].
    exact (sha_state_blocks_valid m b HState HIn).
  - intros HIn. exact (Mem.fresh_block_alloc _ _ _ _ _ HA
      (sha_state_blocks_valid m fresh HState HIn)).
Qed.

Theorem sha_startup_state_store m mf chunk b ofs value :
  sha_startup_state m -> ~ In b sha_state_blocks ->
  Mem.store chunk m b ofs value = Some mf -> sha_startup_state mf.
Proof.
  intros HState HOther HS.
  eapply sha_startup_state_preserved; [exact HState|eapply store_forward; exact HS|].
  intros chunk' b' ofs' HIn. eapply Mem.load_store_other; [exact HS|].
  left. intros ->. exact (HOther HIn).
Qed.

Theorem sha_startup_state_storebytes m mf b ofs bytes :
  sha_startup_state m -> ~ In b sha_state_blocks ->
  Mem.storebytes m b ofs bytes = Some mf -> sha_startup_state mf.
Proof.
  intros HState HOther HS.
  eapply sha_startup_state_preserved; [exact HState|eapply storebytes_forward; exact HS|].
  intros chunk' b' ofs' HIn. eapply Mem.load_storebytes_other; [exact HS|].
  left. intros ->. exact (HOther HIn).
Qed.

Theorem sha_startup_state_free m mf b lo hi :
  sha_startup_state m -> ~ In b sha_state_blocks ->
  Mem.free m b lo hi = Some mf -> sha_startup_state mf.
Proof.
  intros HState HOther HF.
  eapply sha_startup_state_preserved; [exact HState|eapply free_forward; exact HF|].
  intros chunk' b' ofs' HIn. eapply Mem.load_free; [exact HF|].
  left. intros ->. exact (HOther HIn).
Qed.

(** A setup that starts in the initial memory of the SHA translation unit and
    only allocates, writes blocks it allocated, and frees blocks it
    allocated.  Each step is an actual CompCert memory operation. *)
Inductive sha_owned_setup : mem -> list block -> Prop :=
| sha_owned_initial : forall m,
    Genv.init_mem jets_sha.prog = Some m -> sha_owned_setup m []
| sha_owned_alloc : forall m owned lo hi mf fresh,
    sha_owned_setup m owned -> Mem.alloc m lo hi = (mf, fresh) ->
    sha_owned_setup mf (fresh :: owned)
| sha_owned_store : forall m owned chunk b ofs value mf,
    sha_owned_setup m owned -> In b owned ->
    Mem.store chunk m b ofs value = Some mf -> sha_owned_setup mf owned
| sha_owned_storebytes : forall m owned b ofs bytes mf,
    sha_owned_setup m owned -> In b owned ->
    Mem.storebytes m b ofs bytes = Some mf -> sha_owned_setup mf owned
| sha_owned_free : forall m owned b lo hi mf,
    sha_owned_setup m owned -> In b owned ->
    Mem.free m b lo hi = Some mf -> sha_owned_setup mf owned.

Theorem sha_owned_setup_state m owned :
  sha_owned_setup m owned ->
  sha_startup_state m /\ (forall b, In b owned -> ~ In b sha_state_blocks).
Proof.
  intros HSetup. induction HSetup as
    [m HInit|m owned lo hi mf fresh HSetup IH HA|
     m owned chunk b ofs value mf HSetup IH HOwned HS|
     m owned b ofs bytes mf HSetup IH HOwned HS|
     m owned b lo hi mf HSetup IH HOwned HF].
  - split; [exact (sha_startup_state_initialized m HInit)|intros b []].
  - destruct IH as [HState HOwners].
    destruct (sha_startup_state_alloc m mf lo hi fresh HState HA) as [HFinal HFresh].
    split; [exact HFinal|].
    intros b [<-|HB]; [exact HFresh|exact (HOwners b HB)].
  - destruct IH as [HState HOwners]. split; [|exact HOwners].
    eapply sha_startup_state_store; [exact HState|exact (HOwners b HOwned)|exact HS].
  - destruct IH as [HState HOwners]. split; [|exact HOwners].
    eapply sha_startup_state_storebytes; [exact HState|exact (HOwners b HOwned)|exact HS].
  - destruct IH as [HState HOwners]. split; [|exact HOwners].
    eapply sha_startup_state_free; [exact HState|exact (HOwners b HOwned)|exact HF].
Qed.
