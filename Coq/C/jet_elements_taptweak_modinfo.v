(** Original readonly field-modulus metadata, derived from actual global
    initialization. Signed low limb and inverse coefficient are checked. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Values Integers Memory Globalenvs Clight Ctypes.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math C.jet_sx_mem.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Require Import C.jet_secp_modinfo_fe_global C.jet_clight_internal_preserve
 C.jet_clight_internal_permissions C.jet_elements_taptweak_program C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_globals C.jet_elements_taptweak_startup.
Definition elements_taptweak_modinfo_fe_block : block := elements_taptweak_symbol_block _secp256k1_const_modinfo_fe.
Definition elements_taptweak_modinfo_fe_global_rep (m : mem) : Prop :=
 Mem.valid_block m elements_taptweak_modinfo_fe_block /\
 Mem.range_perm m elements_taptweak_modinfo_fe_block 0 48 Cur Readable /\
 forall i w,nth_error modinfo_fe_words i=Some w ->
  Mem.load Mint64 m elements_taptweak_modinfo_fe_block (8*Z.of_nat i)=Some (Vlong w).

Lemma elements_taptweak_modinfo_fe_global_symbol :
 Genv.find_symbol (Clight.genv_genv elements_taptweak_ge) _secp256k1_const_modinfo_fe=Some elements_taptweak_modinfo_fe_block.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_modinfo_fe_global_info :
 Genv.find_var_info (Clight.genv_genv elements_taptweak_ge) elements_taptweak_modinfo_fe_block=Some v_secp256k1_const_modinfo_fe.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_modinfo_fe_genv_projection : Clight.genv_genv elements_taptweak_ge=Genv.globalenv elements_taptweak_linked_program.
Proof. reflexivity. Qed.
Local Opaque elements_taptweak_ge elements_taptweak_modinfo_fe_block.

Theorem elements_taptweak_modinfo_fe_global_initializes m :
 Genv.init_mem elements_taptweak_linked_program=Some m -> elements_taptweak_modinfo_fe_global_rep m.
Proof.
 intro HI;pose proof elements_taptweak_modinfo_fe_global_info as HG.
 rewrite elements_taptweak_modinfo_fe_genv_projection in HG.
 pose proof (Genv.init_mem_characterization elements_taptweak_linked_program elements_taptweak_modinfo_fe_block HG HI)
  as (HP & HB & HL & Hbytes).
 assert (HV : Mem.valid_block m elements_taptweak_modinfo_fe_block).
 { eapply Genv.find_var_info_not_fresh;[exact HI|exact HG]. }
 change (Mem.range_perm m elements_taptweak_modinfo_fe_block 0 48 Cur Readable) in HP.
 specialize (HL eq_refl).
 change (Mem.load Mint64 m elements_taptweak_modinfo_fe_block 0=Some (Vlong (Int64.repr (-4294968273))) /\
   Mem.load Mint64 m elements_taptweak_modinfo_fe_block 8=Some (Vlong Int64.zero) /\
   Mem.load Mint64 m elements_taptweak_modinfo_fe_block 16=Some (Vlong Int64.zero) /\
   Mem.load Mint64 m elements_taptweak_modinfo_fe_block 24=Some (Vlong Int64.zero) /\
   Mem.load Mint64 m elements_taptweak_modinfo_fe_block 32=Some (Vlong (Int64.repr 256)) /\
   Mem.load Mint64 m elements_taptweak_modinfo_fe_block 40=Some (Vlong (Int64.repr 2866531139136965327)) /\ True) in HL.
 unfold elements_taptweak_modinfo_fe_global_rep;split;[exact HV|];split;[exact HP|].
 intros i w HN;destruct i as [|[|[|[|[|[|i]]]]]];
  cbn [modinfo_fe_words nth_error] in HN;
  try (destruct i;discriminate HN);injection HN as E;subst w;
  cbn [Z.of_nat Z.mul];tauto.
Qed.

Theorem elements_taptweak_modinfo_fe_global_readonly_initial m :
 Genv.init_mem elements_taptweak_linked_program=Some m ->
 forall ofs,~Mem.perm m elements_taptweak_modinfo_fe_block ofs Max Writable.
Proof.
 intros HI ofs HW;pose proof elements_taptweak_modinfo_fe_global_info as HG.
 rewrite elements_taptweak_modinfo_fe_genv_projection in HG.
 pose proof (Genv.init_mem_characterization elements_taptweak_linked_program elements_taptweak_modinfo_fe_block HG HI)
  as (_ & HB & _).
 destruct (HB ofs Max Writable HW) as (_ & HO).
 change (perm_order Readable Writable) in HO;inversion HO.
Qed.

Lemma elements_taptweak_modinfo_fe_global_unchanged m m' :
 Mem.unchanged_on (fun b _=>b=elements_taptweak_modinfo_fe_block) m m' ->
 elements_taptweak_modinfo_fe_global_rep m -> elements_taptweak_modinfo_fe_global_rep m'.
Proof.
 intros HU (HV & HP & HL);unfold elements_taptweak_modinfo_fe_global_rep.
 split;[eapply Mem.valid_block_unchanged_on;eauto|];split.
 - intros ofs HO;eapply Mem.perm_unchanged_on;eauto;reflexivity.
 - intros i w HN;eapply Mem.load_unchanged_on;[exact HU| |exact (HL i w HN)].
   intros ofs HO;reflexivity.
Qed.

Lemma elements_taptweak_modinfo_fe_global_lframe m mf P : elements_taptweak_modinfo_fe_global_rep m ->
 lframe P m mf -> (forall pos,P elements_taptweak_modinfo_fe_block pos) -> elements_taptweak_modinfo_fe_global_rep mf.
Proof.
 intros (HV & HP & HL) Frame Outside;unfold elements_taptweak_modinfo_fe_global_rep.
 split;[apply (proj2 (proj2 Frame));exact HV|];split.
 - intros pos HPos;apply (proj1 (proj2 Frame));[exact HV|apply Outside|apply HP;exact HPos].
 - intros i w HN;rewrite (proj1 Frame) by (auto);apply HL;exact HN.
Qed.
Definition elements_taptweak_modinfo_fe_state m:=elements_taptweak_modinfo_fe_global_rep m /\forall ofs,~Mem.perm m elements_taptweak_modinfo_fe_block ofs Max Writable.
Theorem elements_taptweak_modinfo_initial m:
 Genv.init_mem elements_taptweak_linked_program=Some m ->elements_taptweak_modinfo_fe_state m.
Proof. intro Init;split;[apply elements_taptweak_modinfo_fe_global_initializes|apply elements_taptweak_modinfo_fe_global_readonly_initial];exact Init. Qed.
Theorem elements_taptweak_modinfo_initial_memory:
 exists m,Genv.init_mem elements_taptweak_linked_program=Some m /\elements_taptweak_modinfo_fe_state m.
Proof.
 destruct elements_taptweak_initial_memory_exists as(m & Init);exists m;split;
 [exact Init|apply elements_taptweak_modinfo_initial;exact Init].
Qed.
Lemma elements_taptweak_modinfo_separate m b hi:
 elements_taptweak_modinfo_fe_state m ->0<hi ->Mem.range_perm m b 0 hi Cur Freeable ->b<>elements_taptweak_modinfo_fe_block.
Proof.
 intros [_ NotWritable] Positive Free Eq;apply(NotWritable 0);rewrite <-Eq.
 apply Mem.perm_cur_max;eapply Mem.perm_implies;[apply(Free 0);lia|constructor].
Qed.
Theorem elements_taptweak_modinfo_readonly m mf:
 elements_taptweak_modinfo_fe_state m ->readonly_preserved m mf ->elements_taptweak_modinfo_fe_state mf.
Proof.
 intros [Global NotWritable] [Forward Unchanged];pose proof Global as[Valid _].
 assert(Kept:Mem.unchanged_on(fun b _=>b=elements_taptweak_modinfo_fe_block)m mf).
 { eapply Mem.unchanged_on_implies;[exact Unchanged|].
   intros b ofs Eq Valid';subst b;split;[exact Valid|apply NotWritable]. }
 split;[eapply elements_taptweak_modinfo_fe_global_unchanged;[exact Kept|exact Global]|].
 intros ofs Write;apply(NotWritable ofs);exact(proj2(Forward elements_taptweak_modinfo_fe_block Valid)ofs Writable Write).
Qed.
