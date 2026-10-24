(** The original scalar-order modulus global: its actual initialized words,
    readonly status, and preservation through scalar inverse preparation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Values Integers Memory Globalenvs Clight ClightBigstep Ctypes Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_sx_mem C.jet_secp_scalar_inverse_caller.
Require Import C.jet_secp_canonical_scalar C.jet_secp_scalar_signed62 C.jet_secp_signed62_numeric.
Require Import C.jet_secp_fe_nv C.jet_secp_scalar_add_initial C.jet_secp_scalar_get_b32_storage.
Require Import C.jet_secp_scalar_overflow_numeric C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_scalar_lambda_init_exists.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition modinfo_scalar_words : list Int64.int :=
  [Int64.repr 4598842128380346689;Int64.repr 3079181878673178862;
   Int64.repr (-21);Int64.zero;Int64.repr 256;Int64.repr 3815112494326173377].
Definition modinfo_scalar_global_rep (m:mem) : Prop :=
  Mem.valid_block m scalar_inv_modinfo_block /\
  Mem.range_perm m scalar_inv_modinfo_block 0 48 Cur Readable /\
  forall i w,nth_error modinfo_scalar_words i=Some w ->
    Mem.load Mint64 m scalar_inv_modinfo_block (8*Z.of_nat i)=Some(Vlong w).
Definition modinfo_scalar_state (m:mem) : Prop := modinfo_scalar_global_rep m /\
  forall ofs,~Mem.perm m scalar_inv_modinfo_block ofs Max Writable.

Lemma modinfo_scalar_global_info : Genv.find_var_info (Clight.genv_genv secp_ge) scalar_inv_modinfo_block=
  Some v_secp256k1_const_modinfo_scalar.
Proof. vm_compute;reflexivity. Qed.
Lemma modinfo_scalar_genv_projection : Clight.genv_genv secp_ge=Genv.globalenv jets_secp.prog.
Proof. reflexivity. Qed.
Lemma modinfo_scalar_modulus_value :
  Int64.signed(Int64.repr 4598842128380346689)+2^62*Int64.signed(Int64.repr 3079181878673178862)+
    2^124*Int64.signed(Int64.repr (-21))+2^248*Int64.signed(Int64.repr 256)=canonical_group_order.
Proof. vm_compute;reflexivity. Qed.
Lemma modinfo_scalar_inverse62 : (4598842128380346689*3815112494326173377) mod 2^62=1.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge scalar_inv_modinfo_block.

Theorem modinfo_scalar_global_initializes m : Genv.init_mem jets_secp.prog=Some m -> modinfo_scalar_global_rep m.
Proof.
  intro Init;pose proof modinfo_scalar_global_info as Info;rewrite modinfo_scalar_genv_projection in Info.
  pose proof(Genv.init_mem_characterization jets_secp.prog scalar_inv_modinfo_block Info Init)
    as (Read & Bounds & Loads & Bytes).
  assert(Valid:Mem.valid_block m scalar_inv_modinfo_block) by (eapply Genv.find_var_info_not_fresh;eassumption).
  change(Mem.range_perm m scalar_inv_modinfo_block 0 48 Cur Readable) in Read.
  specialize(Loads eq_refl).
  change(Mem.load Mint64 m scalar_inv_modinfo_block 0=Some(Vlong(Int64.repr 4598842128380346689)) /\
    Mem.load Mint64 m scalar_inv_modinfo_block 8=Some(Vlong(Int64.repr 3079181878673178862)) /\
    Mem.load Mint64 m scalar_inv_modinfo_block 16=Some(Vlong(Int64.repr (-21))) /\
    Mem.load Mint64 m scalar_inv_modinfo_block 24=Some(Vlong Int64.zero) /\
    Mem.load Mint64 m scalar_inv_modinfo_block 32=Some(Vlong(Int64.repr 256)) /\
    Mem.load Mint64 m scalar_inv_modinfo_block 40=Some(Vlong(Int64.repr 3815112494326173377)) /\ True) in Loads.
  unfold modinfo_scalar_global_rep;split;[exact Valid|];split;[exact Read|].
  intros i w At;destruct i as [|[|[|[|[|[|i]]]]]];
    cbn [modinfo_scalar_words nth_error] in At;
    try(destruct i;discriminate At);injection At as Same;subst w;
    cbn [Z.of_nat Z.mul];tauto.
Qed.

Theorem modinfo_scalar_readonly_initial m : Genv.init_mem jets_secp.prog=Some m ->
  forall ofs,~Mem.perm m scalar_inv_modinfo_block ofs Max Writable.
Proof.
  intros Init ofs Write;pose proof modinfo_scalar_global_info as Info;rewrite modinfo_scalar_genv_projection in Info.
  pose proof(Genv.init_mem_characterization jets_secp.prog scalar_inv_modinfo_block Info Init) as (_ & Bounds & _).
  destruct(Bounds ofs Max Writable Write) as (_ & Order).
  change(perm_order Readable Writable) in Order;inversion Order.
Qed.

Lemma modinfo_scalar_state_initial m : Genv.init_mem jets_secp.prog=Some m -> modinfo_scalar_state m.
Proof. intro Init;split;[apply modinfo_scalar_global_initializes|apply modinfo_scalar_readonly_initial];exact Init. Qed.

Theorem modinfo_scalar_initial_state_exists :
  exists m,Genv.init_mem jets_secp.prog=Some m /\ modinfo_scalar_state m.
Proof.
  destruct secp_initial_memory_exists as [m Init];exists m;split;[exact Init|].
  apply modinfo_scalar_state_initial;exact Init.
Qed.

Lemma modinfo_scalar_global_lframe m mf P : modinfo_scalar_global_rep m ->
  lframe P m mf -> (forall pos,P scalar_inv_modinfo_block pos) -> modinfo_scalar_global_rep mf.
Proof.
  intros (Valid & Read & Loads) Frame Outside;unfold modinfo_scalar_global_rep.
  split;[apply(proj2(proj2 Frame));exact Valid|];split.
  - intros pos Range;apply(proj1(proj2 Frame));[exact Valid|apply Outside|apply Read;exact Range].
  - intros i w At;rewrite(proj1 Frame) by auto;apply Loads;exact At.
Qed.

(** The actual packed caller state has the real modulus contents, not just
    the correct address. No disjointness from globals is imposed on inputs. *)
Theorem scalar_inv_entry_with_modinfo w m bd bx :
  modinfo_scalar_state m -> scalar_at m bx 0 (scalar_add_values w 0) ->
  Mem.range_perm m bx 0 32 Cur Freeable -> Mem.range_perm m bd 0 32 Cur Freeable ->
  exists bs mi mp,
  function_entry2 secp_ge f_secp256k1_scalar_inverse_var [Vptr bd Ptrofs.zero;Vptr bx Ptrofs.zero]
    m (scalar_inv_env bs) (scalar_inv_temps bd bx) mi /\
  Clight2.exec_stmt secp_ge (scalar_inv_env bs) (scalar_inv_temps bd bx) mi scalar_inv_pack
    E0 (scalar_inv_temps bd bx) mp Out_normal /\
  eval_exprlist secp_ge (scalar_inv_env bs) (scalar_inv_temps bd bx) mp
    [scalar_inv_s_address;scalar_inv_modinfo_address]
    (type_of_params(fn_params f_secp256k1_modinv64_var))
    [Vptr bs Ptrofs.zero;Vptr scalar_inv_modinfo_block Ptrofs.zero] /\
  modinfo_scalar_global_rep mp /\ fe_at mp bs 0 (words5(scalar62_words true w)) /\
  signed62_normalized(scalar62_words true w) /\
  signed62_unsigned_value(scalar62_words true w)=scalar_limb_value w /\
  scalar_at mp bx 0 (scalar_add_values w 0) /\
  Mem.range_perm mp bs 0 40 Cur Freeable /\ Mem.range_perm mp bx 0 32 Cur Freeable /\
  Mem.range_perm mp bd 0 32 Cur Freeable /\ bs<>bx /\ bd<>bs /\ ~Mem.valid_block m bs /\
  lframe (fun b _=>b<>bs /\ b<>bx) m mp.
Proof.
  intros [Global Readonly] Input FX FD.
  destruct(scalar_inv_entry_to_core w m bd bx Input FX FD)
    as (bs & mi & mp & Entry & Pack & Args & Packed & Normal & Value & Source & FS & FXP & FDP & SX & DS & Fresh & Frame).
  assert(NotPrivate:scalar_inv_modinfo_block<>bs).
  { intro Same;apply Fresh;rewrite <-Same;exact(proj1 Global). }
  assert(NotInput:scalar_inv_modinfo_block<>bx).
  { intro Same;apply(Readonly 0);rewrite Same;apply Mem.perm_cur_max.
    eapply Mem.perm_implies;[apply(FX 0);lia|constructor]. }
  assert(GlobalP:modinfo_scalar_global_rep mp).
  { eapply modinfo_scalar_global_lframe;[exact Global|exact Frame|];intros;split;assumption. }
  exists bs,mi,mp;repeat first[assumption|split].
Qed.
