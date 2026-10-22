(** Original readonly field-modulus metadata, derived from actual global
    initialization. Signed low limb and inverse coefficient are checked. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Values Integers Memory Globalenvs Clight Ctypes.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math C.jet_sx_mem.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition modinfo_fe_words : list Int64.int :=
 [Int64.repr (-4294968273);Int64.zero;Int64.zero;Int64.zero;
  Int64.repr 256;Int64.repr 2866531139136965327].
Definition modinfo_fe_block : block := secp_symbol_block _secp256k1_const_modinfo_fe.
Definition modinfo_fe_global_rep (m : mem) : Prop :=
 Mem.valid_block m modinfo_fe_block /\
 Mem.range_perm m modinfo_fe_block 0 48 Cur Readable /\
 forall i w,nth_error modinfo_fe_words i=Some w ->
  Mem.load Mint64 m modinfo_fe_block (8*Z.of_nat i)=Some (Vlong w).

Lemma modinfo_fe_global_symbol :
 Genv.find_symbol (Clight.genv_genv secp_ge) _secp256k1_const_modinfo_fe=Some modinfo_fe_block.
Proof. vm_compute;reflexivity. Qed.
Lemma modinfo_fe_global_info :
 Genv.find_var_info (Clight.genv_genv secp_ge) modinfo_fe_block=Some v_secp256k1_const_modinfo_fe.
Proof. vm_compute;reflexivity. Qed.
Lemma modinfo_fe_words_count : length modinfo_fe_words=6%nat.
Proof. reflexivity. Qed.
Lemma modinfo_fe_modulus_value :
 Int64.signed (Int64.repr (-4294968273))+2^248*Int64.signed (Int64.repr 256)=feP.
Proof. vm_compute;reflexivity. Qed.
Lemma modinfo_fe_inverse62 : ((-4294968273)*2866531139136965327) mod 2^62=1.
Proof. vm_compute;reflexivity. Qed.
Lemma modinfo_fe_genv_projection : Clight.genv_genv secp_ge=Genv.globalenv jets_secp.prog.
Proof. reflexivity. Qed.
Local Opaque secp_ge modinfo_fe_block.

Theorem modinfo_fe_global_initializes m :
 Genv.init_mem jets_secp.prog=Some m -> modinfo_fe_global_rep m.
Proof.
 intro HI;pose proof modinfo_fe_global_info as HG.
 rewrite modinfo_fe_genv_projection in HG.
 pose proof (Genv.init_mem_characterization jets_secp.prog modinfo_fe_block HG HI)
  as (HP & HB & HL & Hbytes).
 assert (HV : Mem.valid_block m modinfo_fe_block).
 { eapply Genv.find_var_info_not_fresh;[exact HI|exact HG]. }
 change (Mem.range_perm m modinfo_fe_block 0 48 Cur Readable) in HP.
 specialize (HL eq_refl).
 change (Mem.load Mint64 m modinfo_fe_block 0=Some (Vlong (Int64.repr (-4294968273))) /\
   Mem.load Mint64 m modinfo_fe_block 8=Some (Vlong Int64.zero) /\
   Mem.load Mint64 m modinfo_fe_block 16=Some (Vlong Int64.zero) /\
   Mem.load Mint64 m modinfo_fe_block 24=Some (Vlong Int64.zero) /\
   Mem.load Mint64 m modinfo_fe_block 32=Some (Vlong (Int64.repr 256)) /\
   Mem.load Mint64 m modinfo_fe_block 40=Some (Vlong (Int64.repr 2866531139136965327)) /\ True) in HL.
 unfold modinfo_fe_global_rep;split;[exact HV|];split;[exact HP|].
 intros i w HN;destruct i as [|[|[|[|[|[|i]]]]]];
  cbn [modinfo_fe_words nth_error] in HN;
  try (destruct i;discriminate HN);injection HN as E;subst w;
  cbn [Z.of_nat Z.mul];tauto.
Qed.

Theorem modinfo_fe_global_readonly_initial m :
 Genv.init_mem jets_secp.prog=Some m ->
 forall ofs,~Mem.perm m modinfo_fe_block ofs Max Writable.
Proof.
 intros HI ofs HW;pose proof modinfo_fe_global_info as HG.
 rewrite modinfo_fe_genv_projection in HG.
 pose proof (Genv.init_mem_characterization jets_secp.prog modinfo_fe_block HG HI)
  as (_ & HB & _).
 destruct (HB ofs Max Writable HW) as (_ & HO).
 change (perm_order Readable Writable) in HO;inversion HO.
Qed.

Lemma modinfo_fe_global_unchanged m m' :
 Mem.unchanged_on (fun b _=>b=modinfo_fe_block) m m' ->
 modinfo_fe_global_rep m -> modinfo_fe_global_rep m'.
Proof.
 intros HU (HV & HP & HL);unfold modinfo_fe_global_rep.
 split;[eapply Mem.valid_block_unchanged_on;eauto|];split.
 - intros ofs HO;eapply Mem.perm_unchanged_on;eauto;reflexivity.
 - intros i w HN;eapply Mem.load_unchanged_on;[exact HU| |exact (HL i w HN)].
   intros ofs HO;reflexivity.
Qed.

Lemma modinfo_fe_global_lframe m mf P : modinfo_fe_global_rep m ->
 lframe P m mf -> (forall pos,P modinfo_fe_block pos) -> modinfo_fe_global_rep mf.
Proof.
 intros (HV & HP & HL) Frame Outside;unfold modinfo_fe_global_rep.
 split;[apply (proj2 (proj2 Frame));exact HV|];split.
 - intros pos HPos;apply (proj1 (proj2 Frame));[exact HV|apply Outside|apply HP;exact HPos].
 - intros i w HN;rewrite (proj1 Frame) by (auto);apply HL;exact HN.
Qed.
