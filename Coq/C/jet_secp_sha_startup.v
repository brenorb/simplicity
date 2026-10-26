(** Establish the SHA globals from the frozen secp program's real initial
    memory. Separate the mutable dispatch cell from owned caller storage;
    readonly preservation alone cannot preserve that mutable cell. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Globalenvs Values Events.
Require sha.SHA256 sha.common_lemmas.
Require Import C.jet_sx_mem C.jet_clight_forward C.jet_clight_internal_preserve
  C.jet_secp_linkage C.jet_secp_sha_dispatch C.jet_sha_initial_globals
  C.jet_sha_uchars_exec C.jet_secp_scalar_lambda_init_exists C.jet_uint32_array_init
  C.jet_sha_ctx8_model C.jet_sha_be32_exec.
Require C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition secp_sha_dispatch_block := secp_symbol_block jets_secp._simplicity_sha256_compression.
Definition secp_sha_counter_block := secp_symbol_block jets_secp._sha256_max_counter.
Definition secp_sha_globals_ok m := secp_sha_dispatch_ok m /\
  Mem.load Mint64 m secp_sha_counter_block 0=Some (Vlong sha_max_counter).
Definition secp_sha_startup m := secp_sha_globals_ok m /\
  (forall ofs,~Mem.perm m secp_sha_counter_block ofs Max Writable) /\
  (forall ofs,~Mem.perm m secp_sha_dispatch_block ofs Max Freeable).

Lemma secp_sha_dispatch_info : Genv.find_var_info (Genv.globalenv jets_secp.prog)
  secp_sha_dispatch_block=Some jets_secp.v_simplicity_sha256_compression.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_counter_info : Genv.find_var_info (Genv.globalenv jets_secp.prog)
  secp_sha_counter_block=Some jets_secp.v_sha256_max_counter.
Proof. vm_compute;reflexivity. Qed.
Lemma secp_sha_compression_ast_symbol : Genv.find_symbol (Genv.globalenv jets_secp.prog)
  jets_secp._sha256_compression_portable=
    Some (secp_symbol_block jets_secp._sha256_compression_portable).
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge secp_sha_dispatch_block secp_sha_counter_block.

Theorem secp_sha_startup_initial m : Genv.init_mem jets_secp.prog=Some m -> secp_sha_startup m.
Proof.
  intro Init.
  destruct (Genv.init_mem_characterization jets_secp.prog _ secp_sha_counter_info Init)
    as (_ & CounterBounds & CounterLoad & _).
  destruct (Genv.init_mem_characterization jets_secp.prog _ secp_sha_dispatch_info Init)
    as (_ & DispatchBounds & _).
  split.
  - split.
    + exact (@scalar_pointer_global_initialized Clight.fundef type jets_secp.prog
        secp_sha_dispatch_block (gvar_info jets_secp.v_simplicity_sha256_compression)
        jets_secp._sha256_compression_portable (secp_symbol_block jets_secp._sha256_compression_portable)
        Ptrofs.zero m false secp_sha_dispatch_info secp_sha_compression_ast_symbol Init).
    + exact (proj1 (CounterLoad eq_refl)).
  - split.
    + intros ofs Perm;pose proof (proj2 (CounterBounds ofs Max Writable Perm)) as Order.
      change (perm_order Readable Writable) in Order;inversion Order.
    + intros ofs Perm;pose proof (proj2 (DispatchBounds ofs Max Freeable Perm)) as Order.
      change (perm_order Writable Freeable) in Order;inversion Order.
Qed.

Theorem secp_sha_startup_exists : exists m,Genv.init_mem jets_secp.prog=Some m /\ secp_sha_startup m.
Proof.
  destruct secp_initial_memory_exists as (m & Init);exists m;split;[exact Init|apply secp_sha_startup_initial;exact Init].
Qed.

Lemma secp_sha_startup_separate m b size : secp_sha_startup m -> 0<size ->
  Mem.range_perm m b 0 size Cur Freeable -> b<>secp_sha_dispatch_block /\ b<>secp_sha_counter_block.
Proof.
  intros [_ [Counter Dispatch]] Size Owned;split;intro Same;subst b.
  - apply (Dispatch 0);apply Mem.perm_cur_max;apply Owned;lia.
  - apply (Counter 0);apply Mem.perm_cur_max;eapply Mem.perm_implies;[apply Owned;lia|constructor].
Qed.

Lemma secp_sha_startup_preserved m mf P : secp_sha_startup m ->
  readonly_preserved m mf -> lframe P m mf ->
  (forall ofs,P secp_sha_dispatch_block ofs) -> secp_sha_startup mf.
Proof.
  intros [[Dispatch Counter] [NoWrite NoFree]] [Forward Unchanged] [Loads _] Outside.
  assert (VD:Mem.valid_block m secp_sha_dispatch_block).
  { unfold secp_sha_dispatch_ok in Dispatch;apply Mem.load_valid_access in Dispatch.
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Dispatch|constructor]. }
  assert (VC:Mem.valid_block m secp_sha_counter_block).
  { apply Mem.load_valid_access in Counter.
    eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact Counter|constructor]. }
  split.
  - split.
    + unfold secp_sha_dispatch_ok in *.
      change (Mem.load Mptr mf secp_sha_dispatch_block 0=
        Some (Vptr (secp_symbol_block jets_secp._sha256_compression_portable) Ptrofs.zero)).
      rewrite Loads;[exact Dispatch|exact VD|intros;apply Outside].
    + eapply Mem.load_unchanged_on;[exact Unchanged| |exact Counter].
      intros ofs Range;split;[exact VC|apply NoWrite].
  - split.
    + intros ofs Perm;apply (NoWrite ofs);exact (proj2 (Forward _ VC) ofs Writable Perm).
    + intros ofs Perm;apply (NoFree ofs);exact (proj2 (Forward _ VD) ofs Freeable Perm).
Qed.

Theorem eval_secp_sha_compression_uchar_owned regs bytes m bs bb :
  length regs=8%nat -> length bytes=64%nat -> secp_sha_startup m ->
  uint32_array_at m bs 0 regs -> Mem.range_perm m bs 0 32 Cur Freeable ->
  (forall i,(i<64)%nat -> Mem.load Mint8unsigned m bb (Z.of_nat i)=Some (Vint (nth i bytes Int.zero))) ->
  exists mf,Clight2.eval_funcall secp_ge m (Internal jets_secp.f_sha256_compression_uchar)
    [Vptr bs Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef /\
  uint32_array_at mf bs 0 (SHA256.hash_block regs (be_words bytes)) /\
  Mem.range_perm mf bs 0 32 Cur Freeable /\ lframe (fun b _=>b<>bs) m mf /\
  readonly_preserved m mf /\ secp_sha_startup mf.
Proof.
  intros LR LB Startup State Owned Bytes.
  assert (Access:forall i,(i<8)%nat ->Mem.valid_access m Mint32 bs (4*Z.of_nat i) Writable).
  { intros i Index;split.
    - intros pos Range;eapply Mem.perm_implies with (p1:=Freeable).
      + apply Owned;change (4*Z.of_nat i<=pos<4*Z.of_nat i+4) in Range;lia.
      + apply Memtype.perm_F_any.
    - change (4|4*Z.of_nat i);exists (Z.of_nat i);lia. }
  destruct (eval_secp_sha_compression_uchar m bs Ptrofs.zero bb Ptrofs.zero regs bytes LR LB
    ltac:(change (32<=18446744073709551615);lia) ltac:(change (64<=18446744073709551615);lia)
    (proj1 (proj1 Startup))
    ltac:(intros i Index;split;
      [apply State;apply nth_error_nth';rewrite LR;exact Index|apply Access;exact Index]) Bytes)
    as (mf & Call & Output & Loads & Perm & Valid & Preserved).
  assert (Frame:lframe (fun b _=>b<>bs) m mf).
  { split.
    - intros ch b ofs Old Outside;apply Loads;[exact Old|left;apply (Outside ofs);pose proof (size_chunk_pos ch);lia].
    - split;[intros;apply Perm;assumption|exact Valid]. }
  exists mf;split;[exact Call|];split.
  - intros i value Nth.
    assert (Index:(i<8)%nat).
    { rewrite <-(sha.common_lemmas.length_hash_block regs (be_words bytes) LR).
      - apply nth_error_Some;rewrite Nth;discriminate.
      - apply be_words_length;rewrite LB;reflexivity. }
    pose proof (Output i Index) as Load.
    apply nth_error_nth with (d:=Int.zero) in Nth;rewrite Nth in Load;exact Load.
  - split.
    + intros pos Range;apply Perm;[eapply Mem.perm_valid_block;apply (Owned 0);lia|apply Owned;exact Range].
    + split;[exact Frame|];split;[exact Preserved|].
      eapply secp_sha_startup_preserved;[exact Startup|exact Preserved|exact Frame|].
      intros ofs;destruct (secp_sha_startup_separate m bs 32 Startup ltac:(lia) Owned) as [Other _];congruence.
Qed.
