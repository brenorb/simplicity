(** Complete original C lbtc_asset call against the canonical scribe program.
    Its constant is local, not a global-initialization or cached-value premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Memory Events.
From compcert Require Import ClightBigstep.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Simplicity.Alg.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_encoding.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_application_sep.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage C.jet_elements_effects.
Require Import C.jet_elements_wrapper C.jet_elements_hash_write C.jet_elements_hash_helpers.
Require Import C.jet_haskell_word_conversion C.jet_haskell_hash_word C.jet_u32_local_init.
Require Import C.jet_uint32_array_init.
Require Import C.jet_bitmachine_rep.
Require Import C.jet_elements_lbtc_asset_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

(** Literal [review (over le256)] followed by [integerHash256/toWord256]. *)
Definition lbtc_asset_le_integer : Z :=
  0x6f0279e9ed041c3d710a9f57d0c02928416460c4b722ae3457a11eec381c526d.
Definition lbtc_asset_bytes : list byte :=
  map (fun i => Byte.repr (lbtc_asset_le_integer / 2 ^ (8 * Z.of_nat i))) (List.seq 0 32).
Definition haskell_word64_be_bytes (w : Z) : list byte :=
  map (fun i => Byte.repr (w / 2 ^ (8 * (7 - Z.of_nat i)))) (List.seq 0 8).
Definition haskell_word256_be_bytes (w : haskell_word256) : list byte :=
  concat (map haskell_word64_be_bytes [hw3 w; hw2 w; hw1 w; hw0 w]).
Definition lbtc_asset_literal : tySem Word256 :=
  haskell_to_word 8 (haskell_integer_hash256 lbtc_asset_bytes).
Definition lbtc_asset_spec {term : Alg.Core.Algebra} : @Alg.Core.domain term Ty.Unit Word256 :=
  Alg.scribe lbtc_asset_literal.

Lemma lbtc_asset_spec_parametric : Alg.Core.Parametric (@lbtc_asset_spec).
Proof. intros alg1 alg2 R. apply Alg.scribe_Parametric. Qed.

Lemma byte_unsigned_list_inj (xs ys : list byte) :
  map Byte.unsigned xs = map Byte.unsigned ys -> xs = ys.
Proof.
  intro H.
  assert (HD : forall zs : list byte, map Byte.repr (map Byte.unsigned zs) = zs).
  { induction zs as [|b zs IH]; cbn; [reflexivity|]. rewrite Byte.repr_unsigned, IH. reflexivity. }
  rewrite <- (HD xs), <- (HD ys). rewrite H. reflexivity.
Qed.

(** The native Word256 big-endian serialization, reversed by [le256]. *)
Lemma lbtc_asset_review_le_bytes :
  lbtc_asset_bytes = rev (haskell_word256_be_bytes (haskell_word256_from_integer lbtc_asset_le_integer)).
Proof. apply byte_unsigned_list_inj. vm_compute; reflexivity. Qed.

(** Closed computation only: no symbolic memory or execution is reduced. *)
Lemma lbtc_asset_spec_cells :
  hash_cells lbtc_asset_words = encode (@lbtc_asset_spec Alg.CoreFunSem tt).
Proof. vm_compute; reflexivity. Qed.

Theorem elements_lbtc_asset_local_spec :
  application_jet_local_spec_sep f_simplicity_lbtc_asset elements_ge Elements.env Ty.Unit Word256
    (fun _ _ _ fp => fp = [])
    (fun a _ => Some (@lbtc_asset_spec Alg.CoreFunSem a)).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor rc [] fp
    _ _ HSbase HSAlign [HSE HSO] _ _ _ HFrame.
  change (write_frame_at m bd dbase bw outedge cursor 256) in HFrame.
  destruct (frame_loadbytes_at m bs sbase _ _ HSE HSO) as [bytes HBytes].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HBytes) as HLen.
  pose proof HFrame as [HB [[HDE HDO] HRest]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor 256 ltac:(lia) HFrame)
    as [_ [_ [_ [old HOld]]]].
  assert (Vs : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  assert (Vd : Mem.valid_block m bd) by (eapply load_valid_block; exact HDE).
  assert (Vw : Mem.valid_block m bw) by (eapply load_valid_block; exact HOld).
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:A1.
  destruct (Mem.alloc ma 0 32) as [mb bh] eqn:A2.
  assert (Fl : forall b, Mem.valid_block m b -> bl <> b).
  { intros b Hv Eq. subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ A1 Hv). }
  assert (Fh : forall b, Mem.valid_block m b -> bh <> b).
  { intros b Hv Eq. subst b. apply (Mem.fresh_block_alloc _ _ _ _ _ A2).
    eapply Mem.valid_block_alloc; eauto. }
  assert (Hhl : bh <> bl).
  { intro Eq. subst bh. apply (Mem.fresh_block_alloc _ _ _ _ _ A2).
    eapply Mem.valid_new_block; exact A1. }
  assert (HBytesB : Mem.loadbytes mb bs sbase 16 = Some bytes).
  { erewrite Mem.loadbytes_alloc_unchanged; [|exact A2|eapply Mem.valid_block_alloc; eauto].
    erewrite Mem.loadbytes_alloc_unchanged; eauto. }
  assert (PL : Mem.range_perm mb bl 0 16 Cur Freeable).
  { intros ofs Ho. eapply Mem.perm_alloc_1; [exact A2|]. eapply Mem.perm_alloc_2; eauto. }
  assert (PH : Mem.range_perm mb bh 0 32 Cur Freeable)
    by (intros ofs Ho; eapply Mem.perm_alloc_2; eauto).
  assert (PLW : Mem.range_perm mb bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite HLen. change (Mem.range_perm mb bl 0 16 Cur Writable).
    intros ofs Ho. eapply Mem.perm_implies; [apply PL; exact Ho|constructor]. }
  destruct (Mem.range_perm_storebytes mb bl 0 bytes PLW) as [mc SC].
  assert (Kcopy : forall chunk b ofs, Mem.valid_block m b ->
    Mem.load chunk mc b ofs = Mem.load chunk m b ofs).
  { intros chunk b ofs Hv. erewrite Mem.load_storebytes_other;
      [|exact SC|left; intro Eq; subst b; exact (Fl bl Hv eq_refl)].
    erewrite Mem.load_alloc_unchanged; [|exact A2|eapply Mem.valid_block_alloc; eauto].
    eapply Mem.load_alloc_unchanged; eauto. }
  assert (Pcopy : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mc b ofs kind p).
  { intros b ofs kind p Hp. eapply Mem.perm_storebytes_1; [exact SC|].
    eapply Mem.perm_alloc_1; [exact A2|]. eapply Mem.perm_alloc_1; eauto. }
  set (e := lbtc_locals bl bh).
  set (le := elements_wrapper_temps f_simplicity_lbtc_asset env bd dbase bs sbase).
  destruct (exec_u32_local_prefix elements_ge e le mc lbtc_array_expr bh 0 0 lbtc_asset_words
    ltac:(intros m' j Hj; apply lbtc_lhs_eval; [unfold e, lbtc_locals; apply PTree.gss|exact Hj])
    ltac:(lia) ltac:(change (32 <= 18446744073709551615); lia)
    ltac:(exists 0; reflexivity)
    ltac:(change (Mem.range_perm mc bh 0 32 Cur Writable); intros ofs Ho;
      eapply Mem.perm_storebytes_1; [exact SC|]; eapply Mem.perm_implies; [apply PH; exact Ho|constructor]))
    as (mi & HArray & HILoads & HIPerm & HIValid & HContinue).
  change (uint32_array_at mi bh 0 lbtc_asset_words) in HArray.
  assert (Kinit : forall chunk b ofs, Mem.valid_block m b ->
    Mem.load chunk mi b ofs = Mem.load chunk m b ofs).
  { intros chunk b ofs Hv. rewrite HILoads; [apply Kcopy; exact Hv|left; intro Eq; subst b; exact (Fh bh Hv eq_refl)]. }
  assert (Pinit : forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mi b ofs kind p)
    by (intros; apply HIPerm, Pcopy; assumption).
  assert (HFrameI : write_frame_at mi bd dbase bw outedge cursor 256).
  { eapply write_frame_at_preserved with (m := m).
    - intros chunk b ofs v _ HL. rewrite Kinit; [exact HL|eapply load_valid_block; exact HL].
    - exact Pinit.
    - exact HFrame. }
  assert (HSep : out_sep bd dbase bw outedge cursor 256 bh 0 32).
  { split; left; [apply Fh; exact Vd|apply Fh; exact Vw]. }
  destruct (eval_elements_writeHash_layout mi bh 0 bd dbase bw outedge cursor lbtc_asset_words
    ltac:(reflexivity) ltac:(lia) ltac:(change (32 <= 18446744073709551615); lia)
    HSep HArray HFrameI) as (me & HWrite & HEffect).
  destruct HEffect as (HOutput & HPrefix & HFields & HLoads & HPerm & HValid).
  assert (PLE : Mem.range_perm me bl 0 16 Cur Freeable).
  { intros ofs Ho. apply HPerm, HIPerm. eapply Mem.perm_storebytes_1; [exact SC|apply PL; exact Ho]. }
  assert (PHE : Mem.range_perm me bh 0 32 Cur Freeable).
  { intros ofs Ho. apply HPerm, HIPerm. eapply Mem.perm_storebytes_1; [exact SC|apply PH; exact Ho]. }
  destruct (Mem.range_perm_free me bl 0 16 PLE) as [mx F1].
  assert (PHX : Mem.range_perm mx bh 0 32 Cur Freeable).
  { intros ofs Ho. eapply Mem.perm_free_1; [exact F1|left; exact Hhl|apply PHE; exact Ho]. }
  destruct (Mem.range_perm_free mx bh 0 32 PHX) as [mf F2].
  assert (Kfree : forall chunk b ofs, Mem.valid_block m b ->
    Mem.load chunk mf b ofs = Mem.load chunk me b ofs).
  { intros chunk b ofs Hv. erewrite Mem.load_free; [|exact F2|left; intro Eq; subst b; exact (Fh bh Hv eq_refl)].
    erewrite Mem.load_free; [reflexivity|exact F1|left; intro Eq; subst b; exact (Fl bl Hv eq_refl)]. }
  exists mf, (@lbtc_asset_spec Alg.CoreFunSem tt). split; [reflexivity|]. split.
  - eapply eval_funcall_internal with (e := e) (le1 := le) (le2 := le)
      (m1 := mb) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
    + eapply lbtc_entry with (ma := ma); [exact A1|exact A2].
    + rewrite lbtc_body_shape. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
      * eapply lbtc_copy with (bs := bs) (sbase := sbase) (bytes := bytes);
          [exact HSbase|exact HSAlign|apply Fl; exact Vs| |exact HBytesB|exact SC].
        unfold le, elements_wrapper_temps. rewrite PTree.gso by discriminate. apply PTree.gss.
      * apply HContinue. apply exec_elements_simple_rest. apply lbtc_write_call with (bh := bh) (bd := bd) (dbase := dbase).
        -- unfold e, lbtc_locals. apply PTree.gss.
        -- unfold e, lbtc_locals. rewrite !PTree.gso by discriminate. reflexivity.
        -- unfold le, elements_wrapper_temps. rewrite !PTree.gso by discriminate. apply PTree.gss.
        -- exact HWrite.
    + cbn. split; [discriminate|reflexivity].
    + change (Mem.free_list me (blocks_of_env elements_ge (lbtc_locals bl bh)) = Some mf).
      rewrite lbtc_blocks. cbn. rewrite F1, F2. reflexivity.
  - split.
    + rewrite <- lbtc_asset_spec_cells. eapply frame_output_cells_load_preserved; [|exact HOutput].
      intros ofs w HL. rewrite Kfree; [exact HL|exact Vw].
    + split.
      * eapply write_prefix_at_preserved with (mr := mi) (me := me).
        -- intros ofs w HL. rewrite Kinit; [exact HL|exact Vw].
        -- intros ofs w HL. rewrite Kfree; [exact HL|exact Vw].
        -- exact HPrefix.
      * split.
        -- destruct HFields as [HE HO]. split; rewrite Kfree by exact Vd; assumption.
        -- intros chunk b ofs Hv Hbd Hbw. rewrite Kfree by exact Hv.
           rewrite (HLoads chunk b ofs Hbd Hbw). apply Kinit; exact Hv.
Qed.
