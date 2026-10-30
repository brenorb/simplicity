(** Exact-memory transport of existing pure SHA helper executions into the
    closed Elements TapTweak linked artifact. No library calls are transported. *)
From Coq Require Import List ZArith Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Globalenvs Memory Values Events.
Require Import C.jet_elements_taptweak_program C.jet_transport C.jet_secp_linkage
 C.jet_secp_sha_pure_transport C.jet_secp_sha_owned C.jet_sx_mem C.jet_sha256_iv_init C.jet_uint32_array_init C.jet_clight_internal_preserve.
Require C.jets_secp C.jets_sha.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition elements_taptweak_ge:=Clight.globalenv elements_taptweak_linked_program.
Lemma elements_taptweak_sha_pure_lookup:
 map (secp_helper_lookup elements_taptweak_ge) secp_sha_pure_helpers=
 map (fun p=>Some (Internal (snd p))) secp_sha_pure_helpers.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_sha_pure_checked:
 forallb (fun p=>fundef_okb secp_ge elements_taptweak_ge (map fst secp_sha_pure_helpers)
 (Internal (snd p))) secp_sha_pure_helpers=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge secp_ge.
Lemma elements_taptweak_sha_pure_entries id f:In (id,f) secp_sha_pure_helpers ->
 exists b1 b2,
 Genv.find_symbol secp_ge id=Some b1 /\ Genv.find_funct_ptr secp_ge b1=Some (Internal f) /\
 Genv.find_symbol elements_taptweak_ge id=Some b2 /\ Genv.find_funct_ptr elements_taptweak_ge b2=Some (Internal f).
Proof.
 intro Member.
 destruct (secp_helper_lookup_exists secp_ge id f
 (secp_map_eq_in _ _ _ secp_sha_lookup_secp (id,f) Member)) as (b1 & S1 & F1).
 destruct (secp_helper_lookup_exists elements_taptweak_ge id f
 (secp_map_eq_in _ _ _ elements_taptweak_sha_pure_lookup (id,f) Member)) as (b2 & S2 & F2).
 exists b1,b2;repeat split;assumption.
Qed.
Lemma elements_taptweak_sha_pure_ok id f:In (id,f) secp_sha_pure_helpers ->
 fundef_okb secp_ge elements_taptweak_ge (map fst secp_sha_pure_helpers) (Internal f)=true.
Proof.
 intro Member;pose proof elements_taptweak_sha_pure_checked as Checked.
 rewrite forallb_forall in Checked;exact (Checked (id,f) Member).
Qed.
Theorem elements_taptweak_sha_transport id f m args trace mf result:
 In (id,f) secp_sha_pure_helpers ->
 Clight2.eval_funcall secp_ge m (Internal f) args trace mf result ->
 Clight2.eval_funcall elements_taptweak_ge m (Internal f) args trace mf result.
Proof.
 intros Member Run;exact (transport_funcall secp_ge elements_taptweak_ge secp_sha_pure_helpers
 elements_taptweak_sha_pure_entries elements_taptweak_sha_pure_ok id f Member m args trace mf result Run).
Qed.
Theorem eval_elements_taptweak_sha_init_owned m bc bs:bc<>bs ->
 Mem.range_perm m bc 0 88 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal jets_secp.f_sha256_init)
 [Vptr bc Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef /\
 Mem.load Mptr mf bc 0=Some (Vptr bs Ptrofs.zero) /\
 Mem.load Mint64 mf bc 8=Some (Vlong Int64.zero) /\
 Mem.load Mint8unsigned mf bc 80=Some (Vint Int.zero) /\
 uint32_array_at mf bs 0 sha256_iv_words /\
 Mem.range_perm mf bc 0 88 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bc /\b<>bs) m mf /\readonly_preserved m mf.
Proof.
 intros Separate Context State.
 destruct (eval_secp_sha_init_owned m bc bs Separate Context State) as (mf & Call & Memory).
 exists mf;split;[|exact Memory].
 exact (elements_taptweak_sha_transport jets_sha._sha256_init jets_sha.f_sha256_init
 m _ _ mf _ ltac:(right;left;reflexivity) Call).
Qed.

Theorem eval_elements_taptweak_sha_digest_owned regs m bb bs:
 length regs=8%nat ->bb<>bs ->uint32_array_at m bs 0 regs ->
 Mem.range_perm m bb 0 32 Cur Freeable ->Mem.range_perm m bs 0 32 Cur Freeable ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal jets_secp.f_sha256_fromMidstate)
 [Vptr bb Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef /\
 (forall i,(i<32)%nat ->Mem.load Mint8unsigned mf bb (Z.of_nat i)=
 Some (Vint (Int.repr (nth i (secp_sha_digest_bytes regs) 0)))) /\
 uint32_array_at mf bs 0 regs /\
 Mem.range_perm mf bb 0 32 Cur Freeable /\Mem.range_perm mf bs 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bb) m mf /\readonly_preserved m mf.
Proof.
 intros Len Separate State Dest Source.
 destruct (eval_secp_sha_digest_owned regs m bb bs Len Separate State Dest Source) as (mf & Call & Memory).
 exists mf;split;[|exact Memory].
 exact (elements_taptweak_sha_transport jets_sha._sha256_fromMidstate jets_sha.f_sha256_fromMidstate
 m _ _ mf _ ltac:(do 5 right;left;reflexivity) Call).
Qed.
