(** Original predicate body: derive every call from the legitimate frame contract. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_exec C.jet_readBit_layout C.jet_sx_expr C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_encoding C.jet_frame_inv.
Require Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg Simplicity.Translate.
Require Import C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_wrapper_run C.jet_secp_local_regions.
Require Import C.jet_secp_read_fe_capacity C.jet_secp_field_predicates C.jet_secp_canonical_odd C.jet_secp_bit_writer C.jet_secp_odd_body.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma canonical_odd_encoded (value : Ty.tySem (Word.Word 8)) :
  Simplicity.Translate.encode (@canonical_fe_is_odd Alg.CoreFunSem value) =
    [Some (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem value))].
Proof. destruct (@canonical_fe_is_odd Alg.CoreFunSem value); reflexivity. Qed.
Local Opaque canonical_fe_is_odd Simplicity.Translate.encode.

Theorem exec_secp_fe_odd_rest_canonical le m0 bd dbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word.Word 8)) m ba bl :
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 1
    (read_fe_rho (frame_input_word_bits value) rc) [] m ->
  exists mw,
    Clight2.exec_stmt secp_ge (secp_public_env bl ba) le m secp_fe_odd_rest E0
      (PTree.set jets_secp._t'1 (Vint (bit_int (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem value)))) le)
      mw (Out_return (Some (Vint Int.one, tint))) /\
    finv m0 bd dbase bw outedge cursor N bi mw true
      (Simplicity.Translate.encode (@canonical_fe_is_odd Alg.CoreFunSem value)) /\
    Mem.range_perm mw ba 0 40 Cur Freeable /\ Mem.range_perm mw bl 0 16 Cur Freeable /\
    lframe (secp_locals_outside m0 bd bw bi ba bl) m mw.
Proof.
  intros HDst HOutput HInput HCursor HMax HFieldFree HFrameFree HFields HSeparate HSep HInv.
  destruct (eval_local_read_fe_canonical_capacity m0 bd dbase bw outedge cursor N 1 bi edge rc value m ba bl
    HOutput HInput HCursor HMax HFieldFree HFrameFree HFields HSeparate HSep HInv)
    as [mr [HRead [HField [HFreeA [HFreeL [HReadInv HReadFrame]]]]]].
  destruct (eval_field_odd_canonical mr ba value HField HFreeA)
    as [mp [HPredicate [HPredFreeA HPredFrame]]].
  assert (HFreeLValid : Mem.valid_block mr bl).
  { eapply Mem.perm_valid_block with (ofs := 0) (k := Cur) (p := Freeable); apply HFreeL; lia. }
  assert (HPredFreeL : Mem.range_perm mp bl 0 16 Cur Freeable).
  { intros pos HPos; apply (proj1 (proj2 HPredFrame)); [exact HFreeLValid|congruence|apply HFreeL; exact HPos]. }
  assert (HPredExt : eqext m0 bd bw bi mr mp).
  { eapply lframe_implies; [exact HPredFrame|].
    intros b pos HExt HValid HEqual; subst b.
    exact (HSep 0%nat ltac:(cbn; lia) HExt). }
  destruct HReadInv as [_ [HReadFinal [HCapacity _]]].
  change (finv m0 bd dbase bw outedge cursor N bi mr false []) in HReadFinal.
  assert (HPredFinal : finv m0 bd dbase bw outedge cursor N bi mp false []).
  { eapply finv_stable; eassumption. }
  set (bit := Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem value)).
  change (1 <= N) in HCapacity.
  assert (HValidDst : Mem.valid_block m0 bd).
  { pose proof HOutput as [_ [[HEdge _] _]]. exact (load_valid _ _ _ _ _ HEdge). }
  assert (HValidWords : Mem.valid_block m0 bw).
  { destruct (write_frame_at_head m0 bd dbase bw outedge cursor N ltac:(lia) HOutput)
      as [_ [_ [_ [w HLoad]]]]. exact (load_valid _ _ _ _ _ HLoad). }
  destruct (eval_secp_writeBit_from_invariant m0 bd dbase bw outedge cursor N bi mp bit HOutput HCapacity HPredFinal)
    as [mw [HWrite [HFinal [HWriteFrame HWritePerms]]]].
  exists mw; split.
  - unfold secp_fe_odd_rest.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le).
    + apply exec_secp_public_read; exact HRead.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mw)
        (le1 := PTree.set jets_secp._t'1 (Vint (bit_int bit)) le).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mp)
          (le1 := PTree.set jets_secp._t'1 (Vint (bit_int bit)) le).
        -- apply exec_secp_public_odd; exact HPredicate.
        -- apply exec_secp_public_bit_write with (bd := bd) (dbase := dbase) (bit := bit).
           ++ rewrite PTree.gso by discriminate; exact HDst.
           ++ apply PTree.gss.
           ++ exact HWrite.
      * apply exec_Sreturn_some; constructor.
  - split.
    + rewrite canonical_odd_encoded; exact HFinal.
    + split.
      { intros pos HPos; apply HWritePerms; apply HPredFreeA; exact HPos. }
      split.
      { intros pos HPos; apply HWritePerms; apply HPredFreeL; exact HPos. }
      eapply lframe_trans.
      * eapply lframe_implies; [exact HReadFrame|].
        intros b pos [HA [HL HE]] HValid; split; [exact HValid|]; split; [|exact HE].
        apply no_local_read_foot; assumption.
      * eapply lframe_trans.
        -- eapply lframe_implies; [exact HPredFrame|].
           intros b pos [HA _] HValid; exact HA.
        -- eapply lframe_implies; [exact HWriteFrame|].
           intros b pos [HA [HL HE]] HValid.
           unfold extA, fext in HE.
           split; intro HEqual; subst b; apply HE; split;
             [left; reflexivity|exact HValidDst|right; left; reflexivity|exact HValidWords].
Qed.
