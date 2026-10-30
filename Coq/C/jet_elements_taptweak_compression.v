(** Exact-memory transport of the verified portable SHA round chain. *)
Require sha.SHA256 sha.common_lemmas.
From Coq Require Import List ZArith Bool Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Globalenvs Memory Values Events.
Require Import C.jet_elements_taptweak_program C.jet_transport C.jet_secp_linkage C.jet_sha_linkage
 C.jet_sha_compress_call C.jet_clight_internal_frame
 C.jet_secp_sha_pure_transport C.jet_secp_sha_compression C.jet_elements_taptweak_pure C.jet_sx_mem C.jet_sha256_iv_init C.jet_uint32_array_init C.jet_clight_internal_preserve.
Require C.jets_secp C.jets_sha.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma elements_taptweak_sha_round_lookup:
 map (secp_helper_lookup elements_taptweak_ge) secp_sha_compression_helpers=
 map (fun p=>Some (Internal (snd p))) secp_sha_compression_helpers.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_sha_round_checked:
 forallb (fun p=>fundef_okb sha_ge elements_taptweak_ge (map fst secp_sha_compression_helpers)
 (Internal (snd p))) secp_sha_compression_helpers=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge secp_ge.
Lemma elements_taptweak_sha_round_entries id f:In (id,f) secp_sha_compression_helpers ->
 exists b1 b2,
 Genv.find_symbol sha_ge id=Some b1 /\ Genv.find_funct_ptr sha_ge b1=Some (Internal f) /\
 Genv.find_symbol elements_taptweak_ge id=Some b2 /\ Genv.find_funct_ptr elements_taptweak_ge b2=Some (Internal f).
Proof.
 intro Member.
 destruct (secp_helper_lookup_exists sha_ge id f
 (secp_map_eq_in _ _ _ secp_sha_compression_lookup_source (id,f) Member)) as (b1 & S1 & F1).
 destruct (secp_helper_lookup_exists elements_taptweak_ge id f
 (secp_map_eq_in _ _ _ elements_taptweak_sha_round_lookup (id,f) Member)) as (b2 & S2 & F2).
 exists b1,b2;repeat split;assumption.
Qed.
Lemma elements_taptweak_sha_round_ok id f:In (id,f) secp_sha_compression_helpers ->
 fundef_okb sha_ge elements_taptweak_ge (map fst secp_sha_compression_helpers) (Internal f)=true.
Proof.
 intro Member;pose proof elements_taptweak_sha_round_checked as Checked.
 rewrite forallb_forall in Checked;exact (Checked (id,f) Member).
Qed.
Theorem elements_taptweak_sha_round_transport id f m args trace mf result:
 In (id,f) secp_sha_compression_helpers ->
 Clight2.eval_funcall sha_ge m (Internal f) args trace mf result ->
 Clight2.eval_funcall elements_taptweak_ge m (Internal f) args trace mf result.
Proof.
 intros Member Run;exact (transport_funcall sha_ge elements_taptweak_ge secp_sha_compression_helpers
 elements_taptweak_sha_round_entries elements_taptweak_sha_round_ok id f Member m args trace mf result Run).
Qed.
Lemma elements_taptweak_sha_round_table_ok:internal_table_ok elements_taptweak_ge secp_sha_compression_helpers.
Proof.
 intros id f Lookup;pose proof (internal_lookup_in _ _ _ Lookup) as Member.
 destruct (elements_taptweak_sha_round_entries id f Member) as (b1 & b2 & S1 & F1 & S2 & F2).
 pose proof secp_sha_compression_closed as Checked;rewrite forallb_forall in Checked.
 specialize (Checked (id,f) Member);apply Bool.andb_true_iff in Checked;destruct Checked as [Body Vars].
 split;[exists b2;split;assumption|split;assumption].
Qed.
Theorem elements_taptweak_sha_round_preserved m args trace mf result:
 Clight2.eval_funcall elements_taptweak_ge m (Internal jets_secp.f_sha256_compression_portable) args trace mf result ->
 readonly_preserved m mf.
Proof.
 intro Run;eapply (proj2 (internal_exec_preserved _ _ elements_taptweak_sha_round_table_ok));[exact Run|].
 exists jets_sha._sha256_compression_portable,jets_sha.f_sha256_compression_portable;split;reflexivity.
Qed.
Theorem eval_elements_taptweak_sha_compression_owned regs chunk m bs bb:
 length regs=8%nat ->length chunk=16%nat ->bs<>bb ->
 uint32_array_at m bs 0 regs ->uint32_array_at m bb 0 chunk ->
 Mem.range_perm m bs 0 32 Cur Freeable ->Mem.range_perm m bb 0 64 Cur Freeable ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal jets_secp.f_sha256_compression_portable)
 [Vptr bs Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef /\
 uint32_array_at mf bs 0 (SHA256.hash_block regs chunk) /\uint32_array_at mf bb 0 chunk /\
 Mem.range_perm mf bs 0 32 Cur Freeable /\Mem.range_perm mf bb 0 64 Cur Freeable /\
 lframe (fun b _=>b<>bs) m mf /\readonly_preserved m mf.
Proof.
  intros LR LC Separate State Block FS FB.
  assert (Access:forall i,(i<8)%nat ->
    Mem.valid_access m Mint32 bs (Ptrofs.unsigned Ptrofs.zero+4*Z.of_nat i) Writable).
  { intros i Index;split.
    - intros pos Range;eapply Mem.perm_implies with (p1:=Freeable).
      + apply FS;change (4*Z.of_nat i<=pos<4*Z.of_nat i+4) in Range;lia.
      + apply Memtype.perm_F_any.
    - change (4|4*Z.of_nat i);exists (Z.of_nat i);lia. }
  destruct (eval_sha_compression m bs Ptrofs.zero bb Ptrofs.zero regs chunk LR LC
    ltac:(change (32<=18446744073709551615);lia) ltac:(change (64<=18446744073709551615);lia)
    (or_introl Separate)
    ltac:(intros i Index;split;
      [apply State;apply nth_error_nth';rewrite LR;exact Index|apply Access;exact Index])
    ltac:(intros i Index;apply Block;apply nth_error_nth';rewrite LC;exact Index))
    as (mf & Run & Output & Loads & Perm & Valid).
  pose proof (elements_taptweak_sha_round_transport jets_sha._sha256_compression_portable jets_sha.f_sha256_compression_portable
    m [Vptr bs Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef ltac:(do 7 right;left;reflexivity) Run) as Call.
  assert (Out:uint32_array_at mf bs 0 (SHA256.hash_block regs chunk)).
  { intros i value Nth.
    assert (Index:(i<8)%nat) by
      (rewrite <-(sha.common_lemmas.length_hash_block regs chunk LR LC);apply nth_error_Some;rewrite Nth;discriminate).
    pose proof (Output i Index) as Load.
    apply nth_error_nth with (d:=Int.zero) in Nth;rewrite Nth in Load;exact Load. }
  assert (Old:Mem.valid_block m bb) by (eapply Mem.perm_valid_block;apply (FB 0);lia).
  exists mf;split;[exact Call|];split;[exact Out|];split.
  - intros i value Nth;rewrite Loads by (first [exact Old|left;congruence]);apply Block;exact Nth.
  - split;[intros pos Range;apply Perm;[eapply Mem.perm_valid_block;apply (FS 0);lia|apply FS;exact Range]|];
      split;[intros pos Range;apply Perm;[exact Old|apply FB;exact Range]|];split.
    + split.
      * intros ch b ofs V Outside;apply Loads;[exact V|left;apply (Outside ofs);pose proof (size_chunk_pos ch);lia].
      * split;[intros;apply Perm;assumption|exact Valid].
    + eapply elements_taptweak_sha_round_preserved;exact Call.
Qed.
