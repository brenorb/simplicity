(** Entry, by-value copy and local release for the unchanged public function. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout C.jet_encoding C.jet_frame_inv.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Translate.
Require Import C.jet_secp_gej_public_entry C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_canonical_normalize.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma gej_public_blocks bl ba :
  blocks_of_env secp_ge (gej_public_env bl ba) = [(bl,0,16);(ba,0,128)].
Proof. reflexivity. Qed.

Lemma gej_alloc_lframe P m ma bl ba mb :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 128 = (mb,ba) -> lframe P m mb.
Proof.
  intros HA HB; eapply lframe_trans;
    apply lframe_unchanged; eapply Mem.alloc_unchanged_on; eassumption.
Qed.

Lemma gej_alloc_fresh m ma bl ba mb :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 128 = (mb,ba) ->
  ~ Mem.valid_block m bl /\ ~ Mem.valid_block m ba /\ ba <> bl.
Proof.
  intros HA HB; split; [eapply Mem.fresh_block_alloc; exact HA|]; split.
  - intro HV; apply (Mem.fresh_block_alloc _ _ _ _ _ HB).
    eapply Mem.valid_block_alloc; eassumption.
  - intro HE; apply (Mem.fresh_block_alloc _ _ _ _ _ HB).
    rewrite HE; eapply Mem.valid_new_block; exact HA.
Qed.

Lemma gej_alloc_freeable m ma bl ba mb :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 128 = (mb,ba) ->
  Mem.range_perm mb bl 0 16 Cur Freeable /\ Mem.range_perm mb ba 0 128 Cur Freeable.
Proof.
  intros HA HB; split; intros pos HPos.
  - eapply Mem.perm_alloc_1; [exact HB|]; eapply Mem.perm_alloc_2; eassumption.
  - eapply Mem.perm_alloc_2; eassumption.
Qed.

Lemma gej_alloc_source_fields m ma bl ba mb bs base bi edge rc :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 128 = (mb,ba) ->
  frame_fields_at m bs base bi edge rc -> frame_fields_at mb bs base bi edge rc.
Proof.
  intros HA HB [HE HC].
  pose proof (load_valid m Mptr bs base _ HE) as HV.
  destruct (gej_alloc_lframe (fun _ _ => True) m ma bl ba mb HA HB) as [HL _].
  split; rewrite HL by auto; assumption.
Qed.

Lemma gej_free_public_locals m bl ba :
  ba <> bl -> Mem.range_perm m bl 0 16 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
  exists mf, Mem.free_list m (blocks_of_env secp_ge (gej_public_env bl ba)) = Some mf /\
    lframe (fun b _ => b <> ba /\ b <> bl) m mf.
Proof.
  intros HSeparate HL HA.
  destruct (free_list_exists [(bl,0,16);(ba,0,128)] m) as [mf [HFree HUnchanged]].
  - cbn; repeat constructor; cbn; intuition congruence.
  - intros b lo hi [H|[H|H]]; [inversion H; subst; exact HL|inversion H; subst; exact HA|contradiction].
  - exists mf; split; [rewrite gej_public_blocks; exact HFree|].
    eapply lframe_implies; [apply lframe_unchanged; exact HUnchanged|].
    intros b pos [HA' HL'] HValid; cbn; intuition congruence.
Qed.

Lemma exec_gej_public_copy m mc bl ba bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!jets_secp._src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt secp_ge (gej_public_env bl ba) le m
    (Sassign (Evar jets_secp._src (Tstruct jets_secp._frameItem noattr))
      (Etempvar jets_secp._src (Tstruct jets_secp._frameItem noattr))) E0 le mc Out_normal.
Proof.
  intros HBase HAlign HSeparate HTemp HLoad HStore.
  assert (HUnsigned : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr; unfold frame_base_valid in HBase; lia. }
  eapply exec_Sassign_copy.
  - apply eval_Evar_local; reflexivity.
  - apply eval_Etempvar; exact HTemp.
  - reflexivity.
  - eapply assign_loc_copy with (b' := bs) (ofs' := Ptrofs.repr sbase) (bytes := bytes).
    + reflexivity.
    + intros _; change (8 | Ptrofs.unsigned (Ptrofs.repr sbase)); rewrite HUnsigned; exact HAlign.
    + intros _; change (8 | 0); exists 0; reflexivity.
    + left; congruence.
    + change (Mem.loadbytes m bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16 = Some bytes).
      rewrite HUnsigned; exact HLoad.
    + exact HStore.
Qed.
