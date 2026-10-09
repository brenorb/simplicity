(** Isolated original secp single-bit writer, transported from its checked body. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_encoding C.jet_frame_inv C.jet_bitcoin_effects.
Require Import C.jet_writeBit_layout_total C.jet_secp_linkage.
Require C.jets.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge ge0.

Lemma secp_writeBit_step m bf base bw edge cursor (bit : bool) :
  write_frame_at m bf base bw edge cursor 1 ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal jets.f_writeBit)
      [Vptr bf (Ptrofs.repr base); Vint (if bit then Int.one else Int.zero)]
      E0 mf (Vint (if bit then Int.one else Int.zero)) /\
    write_effect m mf bf base bw edge cursor 1 [Some bit].
Proof.
  intros HF. pose proof HF as [_ [_ [_ [HC _]]]].
  destruct (eval_writeBit_layout m bf base bw edge cursor bit HF)
    as (mf & w & HCall & HLoad & HBit & HPrefix & HFields & HLoads & HPerm & HValid).
  exists mf. split.
  - eapply secp_transport_call; [|exact HCall].
    unfold secp_core_helpers. simpl. tauto.
  - split.
    + intros i c Hi. destruct i as [|i]; [|destruct i; discriminate].
      simpl in Hi. injection Hi as Hc. subst c. cbn [cell_matches].
      split; [lia|]. exists w. split.
      * replace (cursor - 1 - Z.of_nat 0) with (cursor - 1) by lia. exact HLoad.
      * replace (cursor - 1 - Z.of_nat 0) with (cursor - 1) by lia. symmetry. exact HBit.
    + split; [exact HPrefix|]. split.
      * replace (cursor - 1) with (cursor - 1) by lia. exact HFields.
      * split; [|split; assumption].
        replace (edge + 8 * ((cursor - 1) / 64)) with (write_word_address edge cursor)
          by (unfold write_word_address; reflexivity).
        exact HLoads.
Qed.

Require Import C.jet_sx_mem.
Theorem eval_secp_writeBit_from_invariant m0 bd base bw edge cursor N bi m (bit : bool) :
  write_frame_at m0 bd base bw edge cursor N -> 1 <= N ->
  finv m0 bd base bw edge cursor N bi m false [] ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal jets.f_writeBit)
      [Vptr bd (Ptrofs.repr base); Vint (if bit then Int.one else Int.zero)]
      E0 mf (Vint (if bit then Int.one else Int.zero)) /\
    finv m0 bd base bw edge cursor N bi mf true [Some bit] /\
    lframe (fun b _ => b <> bd /\ b <> bw) m mf /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mf b ofs k p).
Proof.
  intros HOutput HCapacity HInv.
  pose proof (finv_wframe m0 bd base bw edge cursor N bi HOutput m false [] HInv) as HCurrent.
  change (write_frame_at m bd base bw edge (cursor - 0) (N - 0)) in HCurrent.
  rewrite !Z.sub_0_r in HCurrent.
  assert (HOne : write_frame_at m bd base bw edge cursor 1).
  { eapply write_frame_at_le with (count := N); [lia|exact HCurrent]. }
  destruct (secp_writeBit_step m bd base bw edge cursor bit HOne) as [mf [HCall HEffect]].
  exists mf; split; [exact HCall|]; split.
  - replace [Some bit] with ([] ++ [Some bit]) by reflexivity.
    eapply finv_write with (n2 := 1); [exact HOutput|exact HInv|reflexivity|exact HCapacity|].
    change (write_effect m mf bd base bw edge (cursor - 0) 1 [Some bit]).
    rewrite Z.sub_0_r; exact HEffect.
  - destruct HEffect as (_ & _ & _ & HLoads & HPerms & HValid).
    split; [|intros; apply HPerms; assumption].
    split.
    + intros chunk b ofs HV HP.
      destruct (HP ofs ltac:(pose proof (size_chunk_pos chunk); lia)) as [HBD HBW].
      apply HLoads; left; assumption.
    + split; [intros; apply HPerms; assumption|exact HValid].
Qed.
