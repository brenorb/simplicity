(** Actual initialized scalar-modulus words and exact readonly permissions.
    This is startup readiness for the EXISTING initialized jet contract, not
    a replacement for the arbitrary-memory contract or a new C assumption. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight Integers Values Memory Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_scalar_inverse_caller
 C.jet_secp_modinfo_scalar_global C.jet_secp_scalar_lambda_init_exists C.jet_clight_readonly_frame.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge scalar_inv_modinfo_block.

Definition modinfo_scalar_initialized (m:mem) := modinfo_scalar_global_rep m /\
 readonly_region_bounds m scalar_inv_modinfo_block 0 48.

Lemma modinfo_scalar_initial_bounds m : Genv.init_mem jets_secp.prog=Some m ->
 readonly_region_bounds m scalar_inv_modinfo_block 0 48.
Proof.
 intro Init;pose proof modinfo_scalar_global_info as Info;rewrite modinfo_scalar_genv_projection in Info.
 destruct(Genv.init_mem_characterization jets_secp.prog scalar_inv_modinfo_block Info Init) as(Read & Bounds & _).
 change(Mem.range_perm m scalar_inv_modinfo_block 0 48 Cur Readable) in Read.
 unfold readonly_region_bounds;intros ofs k p;split.
 - intro Perm;exact(Bounds ofs k p Perm).
 - intros(Range & Order);eapply Mem.perm_implies;[|exact Order].
   destruct k;[apply Mem.perm_cur_max;exact(Read ofs Range)|exact(Read ofs Range)].
Qed.
Theorem modinfo_scalar_initialized_from_init m : Genv.init_mem jets_secp.prog=Some m ->
 modinfo_scalar_initialized m.
Proof. intro Init;split;[apply modinfo_scalar_global_initializes|apply modinfo_scalar_initial_bounds];exact Init. Qed.
Theorem modinfo_scalar_initialized_exists :
 exists m,Genv.init_mem jets_secp.prog=Some m /\ modinfo_scalar_initialized m.
Proof.
 destruct secp_initial_memory_exists as[m Init];exists m;split;[exact Init|].
 apply modinfo_scalar_initialized_from_init;exact Init.
Qed.
Lemma modinfo_scalar_initialized_state m : modinfo_scalar_initialized m -> modinfo_scalar_state m.
Proof. intros(Global & Bounds);split;[exact Global|exact(readonly_bounds_not_writable _ _ _ _ Bounds)]. Qed.

Lemma modinfo_scalar_words_readable m :
 (forall i w,nth_error modinfo_scalar_words i=Some w ->
  Mem.load Mint64 m scalar_inv_modinfo_block (8*Z.of_nat i)=Some(Vlong w)) ->
 Mem.range_perm m scalar_inv_modinfo_block 0 48 Cur Readable.
Proof.
 intros Loads ofs Range.
 assert(Cases:0<=ofs<8 \/ 8<=ofs<16 \/ 16<=ofs<24 \/ 24<=ofs<32 \/ 32<=ofs<40 \/ 40<=ofs<48) by lia.
 destruct Cases as[Case|[Case|[Case|[Case|[Case|Case]]]]];
 [pose proof(Loads 0%nat _ eq_refl) as Load|pose proof(Loads 1%nat _ eq_refl) as Load|
  pose proof(Loads 2%nat _ eq_refl) as Load|pose proof(Loads 3%nat _ eq_refl) as Load|
  pose proof(Loads 4%nat _ eq_refl) as Load|pose proof(Loads 5%nat _ eq_refl) as Load];
 apply Mem.load_valid_access in Load;apply(proj1 Load);exact Case.
Qed.

(** The old-block facts returned by fresh-frame construction suffice: no
    separation of an input buffer from the modulus block is added here. *)
Theorem modinfo_scalar_initialized_old_blocks m mf : modinfo_scalar_initialized m ->
 (forall b,Mem.valid_block m b -> Mem.valid_block mf b /\
  (forall chunk ofs,Mem.load chunk mf b ofs=Mem.load chunk m b ofs) /\
  (forall ofs k p,Mem.perm mf b ofs k p -> Mem.perm m b ofs k p)) ->
 modinfo_scalar_initialized mf.
Proof.
 intros((Valid & Read & Loads) & Bounds) Old.
 destruct(Old scalar_inv_modinfo_block Valid) as(ValidF & LoadSame & PermBack).
 assert(LoadsF:forall i w,nth_error modinfo_scalar_words i=Some w ->
  Mem.load Mint64 mf scalar_inv_modinfo_block (8*Z.of_nat i)=Some(Vlong w)).
 { intros i w At;rewrite LoadSame;exact(Loads i w At). }
 pose proof(modinfo_scalar_words_readable mf LoadsF) as ReadF.
 split;[exact(conj ValidF (conj ReadF LoadsF))|].
 unfold readonly_region_bounds;intros ofs k p;split.
 - intro Perm;apply(proj1(Bounds ofs k p));exact(PermBack ofs k p Perm).
 - intros(Range & Order);eapply Mem.perm_implies;[|exact Order].
   destruct k;[apply Mem.perm_cur_max;exact(ReadF ofs Range)|exact(ReadF ofs Range)].
Qed.
