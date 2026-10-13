(** Shared public local lifecycle with actual object type and allocation size. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout C.jet_output_layout C.jet_encoding C.jet_frame_inv.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_local_regions.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition owned_public_env (ty : type) (bl ba : block) : env :=
  PTree.set _a (ba,ty) (PTree.set _src (bl,secp_frame_type) empty_env).

Lemma owned_public_blocks ty size bl ba :
  sizeof (genv_cenv secp_ge) ty = size ->
  blocks_of_env secp_ge (owned_public_env ty bl ba) = [(bl,0,16);(ba,0,size)].
Proof.
  intro HSize.
  change ([(bl,0,16);(ba,0,sizeof (genv_cenv secp_ge) ty)] = [(bl,0,16);(ba,0,size)]).
  rewrite HSize;reflexivity.
Qed.

Lemma owned_public_alloc_lframe size P m ma bl ba mb :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 size = (mb,ba) -> lframe P m mb.
Proof.
  intros HA HB; eapply lframe_trans;
    apply lframe_unchanged; eapply Mem.alloc_unchanged_on; eassumption.
Qed.

Lemma owned_public_alloc_fresh size m ma bl ba mb :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 size = (mb,ba) ->
  ~ Mem.valid_block m bl /\ ~ Mem.valid_block m ba /\ ba <> bl.
Proof.
  intros HA HB; split; [eapply Mem.fresh_block_alloc;exact HA|]; split.
  - intro HV; apply (Mem.fresh_block_alloc _ _ _ _ _ HB).
    eapply Mem.valid_block_alloc;eassumption.
  - intro HE; apply (Mem.fresh_block_alloc _ _ _ _ _ HB).
    rewrite HE;eapply Mem.valid_new_block;exact HA.
Qed.

Lemma owned_public_alloc_freeable size m ma bl ba mb :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 size = (mb,ba) ->
  Mem.range_perm mb bl 0 16 Cur Freeable /\ Mem.range_perm mb ba 0 size Cur Freeable.
Proof.
  intros HA HB;split;intros pos HPos.
  - eapply Mem.perm_alloc_1;[exact HB|];eapply Mem.perm_alloc_2;eassumption.
  - eapply Mem.perm_alloc_2;eassumption.
Qed.

Lemma owned_public_alloc_source_fields size m ma bl ba mb bs base bi edge rc :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 size = (mb,ba) ->
  frame_fields_at m bs base bi edge rc -> frame_fields_at mb bs base bi edge rc.
Proof.
  intros HA HB [HE HC].
  pose proof (load_valid m Mptr bs base _ HE) as HV.
  destruct (owned_public_alloc_lframe size (fun _ _ => True) m ma bl ba mb HA HB) as [HL _].
  split;rewrite HL by auto;assumption.
Qed.

Lemma owned_public_free_locals ty size m bl ba :
  sizeof (genv_cenv secp_ge) ty = size ->
  ba <> bl -> Mem.range_perm m bl 0 16 Cur Freeable -> Mem.range_perm m ba 0 size Cur Freeable ->
  exists mf, Mem.free_list m (blocks_of_env secp_ge (owned_public_env ty bl ba)) = Some mf /\
    lframe (fun b _ => b <> ba /\ b <> bl) m mf.
Proof.
  intros HSize HSeparate HL HA.
  destruct (free_list_exists [(bl,0,16);(ba,0,size)] m) as [mf [HFree HUnchanged]].
  - cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi [H|[H|H]];
      [inversion H;subst;exact HL|inversion H;subst;exact HA|contradiction].
  - exists mf;split;[rewrite (owned_public_blocks ty size bl ba HSize);exact HFree|].
    eapply lframe_implies;[apply lframe_unchanged;exact HUnchanged|].
    intros b pos [HA' HL'] HValid;cbn;intuition congruence.
Qed.

Lemma exec_owned_public_copy ty m mc bl ba bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt secp_ge (owned_public_env ty bl ba) le m
    (Sassign (Evar _src secp_frame_type) (Etempvar _src secp_frame_type)) E0 le mc Out_normal.
Proof.
  intros HBase HAlign HSeparate HTemp HLoad HStore.
  assert (HUnsigned : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr;unfold frame_base_valid in HBase;lia. }
  eapply exec_Sassign_copy.
  - apply eval_Evar_local;reflexivity.
  - apply eval_Etempvar;exact HTemp.
  - reflexivity.
  - eapply assign_loc_copy with (b' := bs) (ofs' := Ptrofs.repr sbase) (bytes := bytes).
    + reflexivity.
    + intros _;change (8 | Ptrofs.unsigned (Ptrofs.repr sbase));rewrite HUnsigned;exact HAlign.
    + intros _;change (8 | 0);exists 0;reflexivity.
    + left;congruence.
    + change (Mem.loadbytes m bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16 = Some bytes).
      rewrite HUnsigned;exact HLoad.
    + exact HStore.
Qed.
Print Assumptions owned_public_free_locals.
Print Assumptions exec_owned_public_copy.
