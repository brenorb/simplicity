(** Preserve actual initialized globals through the original 256-bit output write.
    Small-global separation is derived from capacity, not an added API premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Memory Values Events Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_sx_mem C.jet_frame_spec C.jet_frame_layout C.jet_frame_inv
 C.jet_output_layout C.jet_write_layout C.jet_bitcoin_effects C.jet_clight_forward C.jet_clight_internal_frame C.jet_clight_internal_preserve
 C.jet_secp_taptweak_tag C.jet_secp_schnorr_startup C.jet_secp_linear_startup
 C.jet_secp_modinfo_fe_caller C.jet_secp_modinfo_fe_transport C.jet_secp_modinfo_fe_global
 C.jet_secp_sha_startup C.jet_secp_sha_dispatch.
Require C.jets.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition block_extent m bg hi:=forall pos kind p,Mem.perm m bg pos kind p ->0<=pos<hi.
Definition taptweak_dispatch_extent m:=Mem.valid_block m secp_sha_dispatch_block /\block_extent m secp_sha_dispatch_block 8.
Definition taptweak_ready m:=taptweak_startup m /\taptweak_dispatch_extent m.
Lemma taptweak_dispatch_extent_initial m:Genv.init_mem jets_secp.prog=Some m ->taptweak_dispatch_extent m.
Proof.
 intro Init;destruct (Genv.init_mem_characterization jets_secp.prog _ secp_sha_dispatch_info Init)
 as (Perm & Bounds & Loads & _).
 change (Mem.range_perm m secp_sha_dispatch_block 0 8 Cur Writable) in Perm;split.
 - eapply Mem.perm_valid_block;apply (Perm 0);clear;lia.
 - intros pos kind p Permission;exact (proj1 (Bounds pos kind p Permission)).
Qed.
Lemma block_extent_forward m mf b hi:Mem.valid_block m b ->block_extent m b hi ->mem_forward m mf ->block_extent mf b hi.
Proof.
 intros Valid Bounds Forward pos kind p Permission;apply (Bounds pos Max p).
 apply (proj2 (Forward b Valid));eapply Mem.perm_max;exact Permission.
Qed.
Theorem taptweak_ready_initial m:Genv.init_mem jets_secp.prog=Some m ->taptweak_ready m.
Proof. intro Init;split;[apply taptweak_startup_initial|apply taptweak_dispatch_extent_initial];exact Init. Qed.
Theorem taptweak_ready_exists:exists m,Genv.init_mem jets_secp.prog=Some m /\taptweak_ready m.
Proof.
 destruct taptweak_startup_exists as (m & Init & _);exists m;split;[exact Init|apply taptweak_ready_initial;exact Init].
Qed.
Theorem taptweak_ready_forward m mf:taptweak_ready m ->taptweak_startup mf ->mem_forward m mf ->taptweak_ready mf.
Proof.
 intros [Startup [Valid Bounds]] StartupF Forward;split;[exact StartupF|];split.
 - exact (proj1 (Forward _ Valid)).
 - eapply block_extent_forward;[exact Valid|exact Bounds|exact Forward].
Qed.
Theorem small_block_output_separate m bg hi bd base bw edge cursor:
 hi<=9 ->block_extent m bg hi ->write_frame_at m bd base bw edge cursor 256 ->bd<>bg /\bw<>bg.
Proof.
 intros Small Bounds (Base & Fields & Edge & Count & Max & WriteCursor & Writes);split.
 - intro Same;subst bd.
   pose proof (proj1 WriteCursor (base+15) ltac:(change (base+8<=base+15<base+8+8);lia)) as Last.
   pose proof (Bounds _ Cur Writable Last) as Bound;unfold frame_base_valid in Base;lia.
 - intro Same;subst bw.
   destruct (Writes 0 ltac:(lia)) as (A0 & High0 & Apart0 & Write0 & Word0).
   destruct (Writes 64 ltac:(lia)) as (A64 & High64 & Apart64 & Write64 & Word64).
   pose proof (proj1 Write0 (write_cell_address edge cursor 0+7) ltac:(change
    (write_cell_address edge cursor 0<=write_cell_address edge cursor 0+7<write_cell_address edge cursor 0+8);lia)) as Top.
   pose proof (proj1 Write64 (write_cell_address edge cursor 64) ltac:(change
    (write_cell_address edge cursor 64<=write_cell_address edge cursor 64<write_cell_address edge cursor 64+8);lia)) as Bottom.
   pose proof (Bounds _ Cur Writable Top) as TopBound;pose proof (Bounds _ Cur Writable Bottom) as BottomBound.
   assert (Delta:write_cell_address edge cursor 0=write_cell_address edge cursor 64+8).
   { unfold write_cell_address;replace (cursor-1-0) with (cursor-1) by lia.
     replace (cursor-1-64) with ((cursor-1)+(-1)*64) by lia.
     rewrite Z.div_add by lia;lia. }
   lia.
Qed.
Definition secp_write8_internal_table:=
 [(C.jets._LSBclear,C.jets.f_LSBclear);(C.jets._LSBkeep,C.jets.f_LSBkeep);
 (C.jets._simplicity_write8,C.jets.f_simplicity_write8);(C.jets._write8s,C.jets.f_write8s)].
Lemma secp_write8_internal_ok:internal_table_ok secp_ge secp_write8_internal_table.
Proof.
 intros id fd Lookup;apply internal_lookup_in in Lookup;cbn [secp_write8_internal_table In] in Lookup.
 repeat destruct Lookup as [Same|Lookup];try contradiction;inversion Same;subst id fd;clear Same.
 all:split.
 all:try solve[match goal with |-exists b,Genv.find_symbol _ ?id=Some b /\ _=>
 exists (secp_symbol_block id) end;split;vm_compute;reflexivity].
 all:split;vm_compute;reflexivity.
Qed.
Local Opaque secp_ge.
Theorem secp_write8s_preserved m args t mf result:
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_write8s) args t mf result ->readonly_preserved m mf.
Proof.
 intro Run;eapply (proj2 (internal_exec_preserved _ _ secp_write8_internal_ok));[exact Run|].
 exists C.jets._write8s,C.jets.f_write8s;split;reflexivity.
Qed.
Lemma write_effect_lframe m mf bd base bw edge cursor count cells:
 write_effect m mf bd base bw edge cursor count cells ->lframe (fun b _=>b<>bd /\b<>bw) m mf.
Proof.
 intros (_ & _ & _ & Loads & Perms & Valid);split.
 - intros chunk b ofs Old Outside;apply Loads;
 [left;exact (proj1 (Outside ofs ltac:(pose proof (size_chunk_pos chunk);lia)))|
  left;exact (proj2 (Outside ofs ltac:(pose proof (size_chunk_pos chunk);lia)))].
 - split;[intros;apply Perms;assumption|exact Valid].
Qed.
Theorem taptweak_ready_after_write m mf bd base bw edge cursor cells:
 taptweak_ready m ->write_frame_at m bd base bw edge cursor 256 ->
 readonly_preserved m mf ->write_effect m mf bd base bw edge cursor 256 cells ->taptweak_ready mf.
Proof.
 intros [Startup [ValidD BoundsD]] Frame Read Effect.
 pose proof (write_effect_lframe m mf bd base bw edge cursor 256 cells Effect) as Changes.
 destruct Startup as [(Linear & Modulus & SHA) Tag].
 assert (SeparateD:bd<>secp_sha_dispatch_block /\bw<>secp_sha_dispatch_block).
 { eapply small_block_output_separate with (hi:=8);[clear;lia|exact BoundsD|exact Frame]. }
 assert (SeparateT:bd<>taptweak_tag_block /\bw<>taptweak_tag_block).
 { eapply small_block_output_separate with (hi:=9);[clear;lia| |exact Frame].
 intros pos kind p Permission;exact (proj1 (proj2 (proj2 Tag) pos kind p Permission)). }
 destruct SeparateD as [DD WD];destruct SeparateT as [DT WT].
 assert (SchnorrF:schnorr_startup mf).
 { split;[eapply linear_startup_readonly;[exact Linear|exact Read]|];split.
 - eapply modinfo_fe_state_unchanged;[exact Modulus|].
   eapply Mem.unchanged_on_implies;[exact (proj2 Read)|].
   intros b pos Same Old;subst b;split;[exact (proj1 (proj1 Modulus))|exact (proj2 Modulus pos)].
 - eapply secp_sha_startup_preserved;[exact SHA|exact Read|exact Changes|intros;split;congruence]. }
 split;[split;[exact SchnorrF|]|].
 - eapply taptweak_tag_framed;[exact Tag|exact (proj1 Read)|exact Changes|intros;split;congruence].
 - split;[exact (proj1 (proj1 Read _ ValidD))|].
   eapply block_extent_forward;[exact ValidD|exact BoundsD|exact (proj1 Read)].
Qed.
