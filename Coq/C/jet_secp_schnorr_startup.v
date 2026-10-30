(** Actual program initialization and preservation required by Schnorr callers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Memory Globalenvs Values.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_clight_forward
 C.jet_secp_linear_startup C.jet_secp_modinfo_fe_caller C.jet_secp_modinfo_fe_transport
 C.jet_secp_sha_startup C.jet_secp_sha_dispatch.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition schnorr_startup m:=linear_startup m /\modinfo_fe_state m /\secp_sha_startup m.
Theorem schnorr_startup_initial m:Genv.init_mem jets_secp.prog=Some m ->schnorr_startup m.
Proof.
 intro Init;split;[apply linear_startup_initializes;exact Init|];split;
 [apply modinfo_fe_state_initial|apply secp_sha_startup_initial];exact Init.
Qed.
Theorem schnorr_startup_exists:exists m,Genv.init_mem jets_secp.prog=Some m /\schnorr_startup m.
Proof.
 destruct linear_startup_exists as (m & Init & _);exists m;split;[exact Init|apply schnorr_startup_initial;exact Init].
Qed.
Theorem secp_sha_startup_framed_forward m mf P:
 secp_sha_startup m ->mem_forward m mf ->lframe P m mf ->
 (forall ofs,P secp_sha_dispatch_block ofs /\P secp_sha_counter_block ofs) ->secp_sha_startup mf.
Proof.
 intros [[Dispatch Counter] [NoWrite NoFree]] Forward [Loads _] Cover.
 assert (VD:Mem.valid_block m secp_sha_dispatch_block).
 { apply Mem.load_valid_access in Dispatch;eapply Mem.valid_access_valid_block;
   eapply Mem.valid_access_implies;[exact Dispatch|constructor]. }
 assert (VC:Mem.valid_block m secp_sha_counter_block).
 { apply Mem.load_valid_access in Counter;eapply Mem.valid_access_valid_block;
   eapply Mem.valid_access_implies;[exact Counter|constructor]. }
 split.
 - split.
   + unfold secp_sha_dispatch_ok in *.
     change (Mem.load Mptr mf secp_sha_dispatch_block 0=Some (Vptr
      (secp_symbol_block jets_secp._sha256_compression_portable) Ptrofs.zero)).
     rewrite (Loads Mptr secp_sha_dispatch_block 0 VD);
     [exact Dispatch|intros;exact (proj1 (Cover _))].
   + rewrite (Loads Mint64 secp_sha_counter_block 0 VC);[exact Counter|intros;exact (proj2 (Cover _))].
 - split.
   + intros ofs Perm;apply (NoWrite ofs);exact (proj2 (Forward _ VC) ofs Writable Perm).
   + intros ofs Perm;apply (NoFree ofs);exact (proj2 (Forward _ VD) ofs Freeable Perm).
Qed.
Theorem schnorr_startup_framed m mf:schnorr_startup m ->mem_forward m mf ->
 lframe (fun _ _=>True) m mf ->schnorr_startup mf.
Proof.
 intros (Linear & Modulus & SHA) Forward Frame;split.
 - eapply linear_startup_lframe;[exact Linear|exact Forward|exact Frame|intros;exact I].
 - split.
   + eapply modinfo_fe_state_framed_forward;[exact Modulus|exact Forward|exact Frame|intros;exact I].
   + eapply secp_sha_startup_framed_forward;[exact SHA|exact Forward|exact Frame|intros;split;exact I].
Qed.
Lemma schnorr_owned_slots_exclude m (slots:list (block*Z)) global:
 (forall b hi,In (b,hi) slots ->0<hi /\Mem.range_perm m b 0 hi Cur Freeable) ->
 (forall pos,~Mem.perm m global pos Max Freeable) ->~In global (map fst slots).
Proof.
 intros Owned NoFree Member;apply in_map_iff in Member as ([b hi] & Same & Slot);cbn in Same;subst b.
 destruct (Owned global hi Slot) as [Positive Free];apply (NoFree 0);apply Mem.perm_cur_max;apply Free;lia.
Qed.
Theorem schnorr_startup_owned_forward m mf (slots:list (block*Z)):
 schnorr_startup m ->mem_forward m mf ->
 (forall b hi,In (b,hi) slots ->0<hi /\Mem.range_perm m b 0 hi Cur Freeable) ->
 lframe (fun b _=>~In b (map fst slots)) m mf ->schnorr_startup mf.
Proof.
 intros (Linear & Modulus & SHA) Forward Owned Frame;split.
 - eapply linear_startup_lframe;[exact Linear|exact Forward|exact Frame|].
   intros b Member pos;eapply schnorr_owned_slots_exclude;[exact Owned|].
   intros p Free;apply (linear_startup_not_writable m Linear b Member p).
   eapply Mem.perm_implies;[exact Free|constructor].
 - split.
   + eapply modinfo_fe_state_owned_frame;[exact Modulus|exact Forward|exact Owned|exact Frame].
   + eapply secp_sha_startup_framed_forward;[exact SHA|exact Forward|exact Frame|].
     intros pos;split;intro Member;apply in_map_iff in Member as ([b hi] & Same & Slot);cbn in Same;subst b;
      destruct (Owned _ hi Slot) as [Positive Free].
     * exact (proj1 (secp_sha_startup_separate m secp_sha_dispatch_block hi SHA Positive Free) eq_refl).
     * exact (proj2 (secp_sha_startup_separate m secp_sha_counter_block hi SHA Positive Free) eq_refl).
Qed.
