(** Whole original challenge function for the public jets' 32-byte message.
    Actual entry, tagged constructor, copy, seven calls and four frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_exec C.jet_sx_mem C.jet_memcpy_model C.jet_secp_linkage
 C.jet_secp_sha_startup C.jet_clight_internal_preserve
 C.jet_secp_schnorr_challenge_entry C.jet_secp_schnorr_challenge_owned
 C.jet_secp_schnorr_challenge_hash C.jet_secp_schnorr_challenge_absorb
 C.jet_secp_schnorr_challenge_finish C.jet_secp_scalar_limb_bridge
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_canonical_scalar C.jet_secp_scalar_overflow_numeric C.jet_secp_scalar_add_reader_support.
Require Import C.jets_secp.
Import ListNotations Ctypes Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Local Ltac allocated_valid := first [assumption |
 match goal with A:Mem.alloc _ _ _=(?mm,?bb) |- Mem.valid_block ?mm ?bb =>
  eapply Mem.valid_new_block;exact A end |
 match goal with A:Mem.alloc _ _ _=(?mm,_) |- Mem.valid_block ?mm _ =>
  eapply Mem.valid_block_alloc;[exact A|allocated_valid] end].
Local Ltac allocated_distinct := first [assumption |
 match goal with A:Mem.alloc _ _ _=(_,?bb) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ A);
   rewrite <-Eq;allocated_valid end |
 match goal with A:Mem.alloc _ _ _=(_,?ba) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ A);
   rewrite Eq;allocated_valid end].
Local Ltac allocated_perm Range := first [
 match goal with A:Mem.alloc _ _ _=(?mm,?bb) |- Mem.perm ?mm ?bb _ _ _ =>
  eapply Mem.perm_alloc_2;[exact A|exact Range] end |
 match goal with A:Mem.alloc _ _ _=(?mm,_) |- Mem.perm ?mm _ _ _ _ =>
  eapply Mem.perm_alloc_1;[exact A|allocated_perm Range] end].
Local Ltac allocated_frame := lazymatch goal with |- lframe _ ?ma ?mb =>
 tryif constr_eq ma mb then apply lframe_refl else
 match goal with A:Mem.alloc ma _ _=(?mi,_) |- _ =>
  eapply lframe_trans with (m2:=mi);
   [apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact A|allocated_frame] end end.
Theorem schnorr_challenge_entry_storage m be ba oa bm om bp op:exists mi bb bs bc br,
 function_entry2 secp_ge f_secp256k1_schnorrsig_challenge
 [Vptr be Ptrofs.zero;Vptr ba oa;Vptr bm om;Vlong (Int64.repr 32);Vptr bp op] m
 (schnorr_challenge_env bb bs bc br) (schnorr_challenge_temps be ba oa bm om bp op) mi /\
 NoDup [bb;bs;bc;br] /\
 (forall b,Mem.valid_block m b ->~In b [bb;bs;bc;br]) /\
 (forall b hi,In (b,hi) [(bb,32);(bs,32);(bc,88);(br,88)] ->Mem.range_perm mi b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 32) as (m1,bb) eqn:AB.
 destruct (Mem.alloc m1 0 32) as (m2,bs) eqn:AS.
 destruct (Mem.alloc m2 0 88) as (m3,bc) eqn:AC.
 destruct (Mem.alloc m3 0 88) as (mi,br) eqn:AR.
 assert (Entry:function_entry2 secp_ge f_secp256k1_schnorrsig_challenge
 [Vptr be Ptrofs.zero;Vptr ba oa;Vptr bm om;Vlong (Int64.repr 32);Vptr bp op] m
 (schnorr_challenge_env bb bs bc br) (schnorr_challenge_temps be ba oa bm om bp op) mi)
 by (eapply schnorr_challenge_entry;[exact AB|exact AS|exact AC|exact AR]).
 exists mi,bb,bs,bc,br;split;[exact Entry|];split.
 - repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;
   repeat split;try apply NoDup_nil;try apply in_nil;allocated_distinct.
 - split.
   + intros b Valid;repeat rewrite not_in_cons;repeat split;try apply in_nil;allocated_distinct.
   + split.
     * intros b hi Slot;cbn [In] in Slot.
       destruct Slot as [Slot|[Slot|[Slot|[Slot|Slot]]]];try contradiction;
       inversion Slot;subst b hi;intros pos Range;allocated_perm Range.
     * split;[allocated_frame|eapply entry_preserved;exact Entry].
Qed.
Lemma schnorr_challenge_free_storage m bb bs bc br:
 NoDup [bb;bs;bc;br] ->
 (forall b hi,In (b,hi) [(bb,32);(bs,32);(bc,88);(br,88)] ->Mem.range_perm m b 0 hi Cur Freeable) ->exists mf,
 Mem.free_list m (blocks_of_env secp_ge (schnorr_challenge_env bb bs bc br))=Some mf /\
 lframe (fun b _=>~In b [bb;bs;bc;br]) m mf /\readonly_preserved m mf.
Proof.
 intros Separate Owned.
 destruct (free_list_exists [(bs,0,32);(bc,0,88);(br,0,88);(bb,0,32)] m) as (mf & Free & Frame).
 - repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;
   cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi Slot;cbn [In] in Slot.
   destruct Slot as [Slot|[Slot|[Slot|[Slot|Slot]]]];try contradiction;
   inversion Slot;subst b lo hi;apply Owned;cbn [In];tauto.
 - exists mf;split;[rewrite schnorr_challenge_blocks;exact Free|];split.
   + eapply lframe_implies;[apply lframe_unchanged;exact Frame|].
     intros b ofs Outside Valid;cbn [map fst In] in *;intuition congruence.
   + eapply freelist_preserved;exact Free.
Qed.
Lemma schnorr_scalar_storage m be rho:
 Mem.range_perm m be 0 32 Cur Freeable ->
 (forall i,(i<4)%nat ->Mem.load Mint64 m be (8*Z.of_nat i)=Some (Vlong (rho i))) ->
 scalar_at m be 0 (map Int64.repr (scalar_limbs_of (scalar_limb_value rho))).
Proof.
 intros Owned Limbs;unfold scalar_limb_value;rewrite scalar_limbs_of_four_words.
 cbn [map];rewrite !Int64.repr_unsigned.
 unfold scalar_at;split;[reflexivity|];split;[lia|];split;[exists 0;reflexivity|];split;
 [change (32<=18446744073709551615);lia|];split.
 - intros pos Range;eapply Mem.perm_implies;[apply Owned;exact Range|constructor].
 - intros i v Nth.
   assert (Index:(i<4)%nat).
   { change (i<length [rho 0%nat;rho 1%nat;rho 2%nat;rho 3%nat])%nat.
     apply nth_error_Some;rewrite Nth;discriminate. }
   rewrite Z.add_0_l.
   destruct i as [|[|[|[|i]]]];try lia;cbn [nth_error] in Nth;injection Nth as <-;
   apply Limbs;lia.
Qed.
Theorem eval_schnorr_challenge_word (Model:memcpy_model)
 (r pk msg:Ty.tySem (Word 8)) m be ba oa bm om bp op:
 secp_sha_startup m ->Mem.range_perm m be 0 32 Cur Freeable ->
 Ptrofs.unsigned oa+32<=Ptrofs.max_unsigned ->Ptrofs.unsigned op+32<=Ptrofs.max_unsigned ->
 Ptrofs.unsigned om+32<=Ptrofs.max_unsigned ->
 schnorr_bytes_at m ba oa (schnorr_word_bytes r) ->
 schnorr_bytes_at m bp op (schnorr_word_bytes pk) ->
 schnorr_bytes_at m bm om (schnorr_word_bytes msg) ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_schnorrsig_challenge)
 [Vptr be Ptrofs.zero;Vptr ba oa;Vptr bm om;Vlong (Int64.repr 32);Vptr bp op] E0 mf Vundef /\
 scalar_at mf be 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem (schnorr_challenge_hash_word r pk msg))))) /\
 Mem.range_perm mf be 0 32 Cur Freeable /\lframe (fun b _=>b<>be) m mf /\
 readonly_preserved m mf /\secp_sha_startup mf.
Proof.
 intros Ready FE HiA HiP HiM BytesA BytesP BytesM.
 assert (VE:Mem.valid_block m be) by (eapply Mem.perm_valid_block;apply (FE 0);lia).
 assert (VA:Mem.valid_block m ba) by (eapply schnorr_bytes_valid;[rewrite schnorr_word_bytes_length;lia|exact BytesA]).
 assert (VP:Mem.valid_block m bp) by (eapply schnorr_bytes_valid;[rewrite schnorr_word_bytes_length;lia|exact BytesP]).
 assert (VM:Mem.valid_block m bm) by (eapply schnorr_bytes_valid;[rewrite schnorr_word_bytes_length;lia|exact BytesM]).
 destruct (schnorr_challenge_entry_storage m be ba oa bm om bp op) as
 (mi & bb & bs & bc & br & Entry & Separate & Old & OwnedI & FrameI & ReadI).
 assert (OutsideE:~In be [bb;bs;bc;br]) by (apply Old;exact VE).
 assert (Distinct:NoDup [bb;bs;bc;br;be]).
 { clear -Separate OutsideE;repeat rewrite NoDup_cons_iff in *;cbn [In] in *;
   repeat split;try apply NoDup_nil;intuition congruence. }
 assert (Sources:forall b,In b [ba;bp;bm] ->~In b [bb;bs;bc;br]).
 { intros b [B|[B|[B|B]]];try contradiction;subst b;apply Old;assumption. }
 assert (ReadyI:secp_sha_startup mi).
 { eapply secp_sha_startup_preserved;[exact Ready|exact ReadI|exact FrameI|intros;exact I]. }
 assert (FEI:Mem.range_perm mi be 0 32 Cur Freeable).
 { eapply schnorr_owner_framed;[lia|exact FrameI|intros;exact I|exact FE]. }
 assert (StorageI:forall b hi,In (b,hi) (schnorr_challenge_storage bb bs bc br be) ->Mem.range_perm mi b 0 hi Cur Freeable).
 { intros b hi Slot;unfold schnorr_challenge_storage in Slot;cbn [In] in Slot.
   destruct Slot as [Slot|[Slot|[Slot|[Slot|[Slot|Slot]]]]];try contradiction;
   inversion Slot;subst b hi;try exact FEI;apply OwnedI;cbn [In];tauto. }
 destruct (exec_schnorr_challenge_owned Model r pk msg mi bb bs bc br be ba oa bm om bp op
  Distinct Sources StorageI ReadyI HiA HiP HiM) as
 (mu & Body & Limbs & Value & OwnedU & FrameU & ReadU & ReadyU).
 - eapply schnorr_bytes_framed;[exact FrameI|exact VA|intros;exact I|exact BytesA].
 - eapply schnorr_bytes_framed;[exact FrameI|exact VP|intros;exact I|exact BytesP].
 - eapply schnorr_bytes_framed;[exact FrameI|exact VM|intros;exact I|exact BytesM].
 - assert (ScalarU:scalar_at mu be 0 (map Int64.repr (scalar_limbs_of
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem (schnorr_challenge_hash_word r pk msg)))))).
   { rewrite <-Value;apply schnorr_scalar_storage;[apply OwnedU;unfold schnorr_challenge_storage;cbn [In];tauto|exact Limbs]. }
   assert (FEU:Mem.range_perm mu be 0 32 Cur Freeable).
   { apply OwnedU;unfold schnorr_challenge_storage;cbn [In];tauto. }
   destruct (schnorr_challenge_free_storage mu bb bs bc br Separate) as (mf & Free & FrameF & ReadF).
   { intros b hi Slot;apply OwnedU;unfold schnorr_challenge_storage;cbn [In] in Slot |- *;tauto. }
   assert (ReadyF:secp_sha_startup mf).
   { eapply secp_sha_startup_preserved;[exact ReadyU|exact ReadF|exact FrameF|].
     assert (Safe:forall b hi,In (b,hi) [(bb,32);(bs,32);(bc,88);(br,88)] ->b<>secp_sha_dispatch_block).
     { intros b hi Slot.
       assert (Positive:0<hi).
       { clear -Slot;cbn [In] in Slot;destruct Slot as [H|[H|[H|[H|H]]]];try contradiction;inversion H;lia. }
       assert (Owned:Mem.range_perm mu b 0 hi Cur Freeable).
       { apply OwnedU;unfold schnorr_challenge_storage;cbn [In] in Slot |- *;tauto. }
       exact (proj1 (secp_sha_startup_separate mu b hi ReadyU Positive Owned)). }
     intros pos Equal;cbn [In] in Equal.
     destruct Equal as [E|[E|[E|[E|E]]]];try contradiction.
     - exact (Safe bb 32 (or_introl eq_refl) E).
     - exact (Safe bs 32 (or_intror (or_introl eq_refl)) E).
     - exact (Safe bc 88 (or_intror (or_intror (or_introl eq_refl))) E).
     - exact (Safe br 88 (or_intror (or_intror (or_intror (or_introl eq_refl)))) E). }
   exists mf;split.
   + eapply eval_funcall_internal with (e:=schnorr_challenge_env bb bs bc br)
      (le1:=schnorr_challenge_temps be ba oa bm om bp op)
      (le2:=schnorr_challenge_temps be ba oa bm om bp op) (m1:=mi) (m2:=mu) (out:=Out_normal).
     * exact Entry.
     * exact Body.
     * reflexivity.
     * exact Free.
   + split.
     * eapply scalar_at_lframe;[exact ScalarU|exact FrameF|intros;exact OutsideE].
     * split.
       -- eapply schnorr_owner_framed;[lia|exact FrameF|intros;exact OutsideE|exact FEU].
       -- split.
          ++ eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\b<>be).
             ** eapply lframe_trans.
                --- eapply lframe_implies;[exact FrameI|intros;exact I].
                --- eapply lframe_trans.
                    +++ eapply lframe_implies;[exact FrameU|].
                        intros b ofs [Valid Other] ValidI;pose proof (Old b Valid) as Outside;clear -Other Outside;cbn [In] in Outside |- *;intuition congruence.
                    +++ eapply lframe_implies;[exact FrameF|intros b ofs [Valid Other] ValidU;apply Old;exact Valid].
             ** intros b ofs Other Valid;split;assumption.
          ++ split;[eapply preserved_trans;[exact ReadI|];eapply preserved_trans;[exact ReadU|exact ReadF]|exact ReadyF].
Qed.
