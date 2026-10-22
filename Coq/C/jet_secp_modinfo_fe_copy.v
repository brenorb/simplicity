(** Actual first modular-inverse copy from the readonly sparse modulus.
    The source is not assumed writable or canonically limb-normalized. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_modinfo_fe_global C.jet_secp_signed62_assign.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge modinfo_fe_block.

Definition modinfo_fe_limb i := nth i modinfo_fe_words Int64.zero.
Lemma modinfo_fe_first_five : words5 modinfo_fe_limb=
 [Int64.repr (-4294968273);Int64.zero;Int64.zero;Int64.zero;Int64.repr 256].
Proof. reflexivity. Qed.

Theorem eval_signed62_assign_modinfo m bd : modinfo_fe_global_rep m ->
 bd<>modinfo_fe_block -> Mem.range_perm m bd 0 40 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_signed62_assign)
  [Vptr bd Ptrofs.zero;Vptr modinfo_fe_block Ptrofs.zero] E0 mf Vundef /\
 fe_at mf bd 0 (words5 modinfo_fe_limb) /\
 Mem.range_perm mf bd 0 40 Cur Freeable /\ modinfo_fe_global_rep mf /\
 lframe (fun b _=>b<>bd) m mf.
Proof.
 intros Global Sep Free.
 pose proof Global as (Valid & Read & Load).
 assert (R : Mem.range_perm m modinfo_fe_block 0 40 Cur Readable)
  by (intros pos HP;apply Read;lia).
 assert (L : forall i w,nth_error (words5 modinfo_fe_limb) i=Some w ->
   Mem.load Mint64 m modinfo_fe_block (8*Z.of_nat i)=Some (Vlong w)).
 { intros i w HN;apply Load.
   destruct i as [|[|[|[|[|i]]]]];
     cbn [words5 modinfo_fe_limb modinfo_fe_words nth nth_error] in HN |- *;
     try (destruct i;discriminate HN);exact HN. }
 destruct (eval_signed62_assign_readable modinfo_fe_limb m bd modinfo_fe_block Sep Free R L)
   as (mf & Call & Output & FreeF & Frame).
 exists mf;split;[exact Call|];split;[exact Output|];split;[exact FreeF|];split;[|exact Frame].
 eapply modinfo_fe_global_lframe;[exact Global|exact Frame|];intros;congruence.
Qed.
