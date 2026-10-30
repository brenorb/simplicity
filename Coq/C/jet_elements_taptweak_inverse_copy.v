(** Actual inverse modulus copy at the linked readonly metadata address.
    The sparse signed limbs are kept exactly as in the frozen initializer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_modinfo_fe_global C.jet_secp_modinfo_fe_copy
 C.jet_secp_signed62_assign C.jet_elements_taptweak_pure C.jet_elements_taptweak_modinfo
 C.jet_elements_taptweak_curve_transport C.jet_elements_taptweak_internal C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_has_signed62_assign:
 In(_secp256k1_modinv64_signed62_assign,f_secp256k1_modinv64_signed62_assign)elements_taptweak_curve_helpers.
Proof.
 assert(Found:find(fun it=>Pos.eqb(fst it)_secp256k1_modinv64_signed62_assign)elements_taptweak_curve_helpers=
 Some(_secp256k1_modinv64_signed62_assign,f_secp256k1_modinv64_signed62_assign))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_modinfo_fe_block.
Theorem eval_elements_taptweak_signed62_assign_modinfo m bd:
 elements_taptweak_modinfo_fe_state m ->Mem.range_perm m bd 0 40 Cur Freeable ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m(Internal f_secp256k1_modinv64_signed62_assign)
 [Vptr bd Ptrofs.zero;Vptr elements_taptweak_modinfo_fe_block Ptrofs.zero]E0 mf Vundef /\
 fe_at mf bd 0(words5 modinfo_fe_limb) /\Mem.range_perm mf bd 0 40 Cur Freeable /\
 elements_taptweak_modinfo_fe_state mf /\lframe(fun b _=>b<>bd)m mf /\readonly_preserved m mf.
Proof.
 intros Ready Free.
 assert(Separate:bd<>elements_taptweak_modinfo_fe_block).
 { exact(elements_taptweak_modinfo_separate m bd 40 Ready ltac:(lia) Free). }
 pose proof(proj1 Ready)as(Valid & Read & Load).
 assert(Input:Mem.range_perm m elements_taptweak_modinfo_fe_block 0 40 Cur Readable).
 { intros pos Range;apply Read;lia. }
 assert(Loads:forall i w,nth_error(words5 modinfo_fe_limb)i=Some w ->
 Mem.load Mint64 m elements_taptweak_modinfo_fe_block(8*Z.of_nat i)=Some(Vlong w)).
 { intros i w At;apply Load.
   destruct i as[|[|[|[|[|i]]]]];
   cbn[words5 modinfo_fe_limb modinfo_fe_words nth nth_error]in At|-*;
   try(destruct i;discriminate At);exact At. }
 destruct(eval_signed62_assign_readable modinfo_fe_limb m bd elements_taptweak_modinfo_fe_block
 Separate Free Input Loads)as(mf & Run & Output & Owned & Frame).
 pose proof(elements_taptweak_curve_transport _ _ m _ E0 mf _ elements_taptweak_has_signed62_assign Run)as RunT.
 assert(Readonly:readonly_preserved m mf).
 { eapply elements_taptweak_internal_preserved;[exact elements_taptweak_has_signed62_assign|exact RunT]. }
 exists mf;split;[exact RunT|];split;[exact Output|];split;[exact Owned|];split.
 - eapply elements_taptweak_modinfo_readonly;[exact Ready|exact Readonly].
 - split;[exact Frame|exact Readonly].
Qed.
