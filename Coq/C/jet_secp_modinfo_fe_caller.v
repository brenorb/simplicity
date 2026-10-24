(** Initialized modulus data survives the actual point reader and writes
    confined to valid writable frame blocks. No external-call model
    or input/global disjointness premise is introduced. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events Globalenvs.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_modinfo_fe_global.
Require Import C.jet_output_layout C.jet_write_layout C.jet_sx_mem.
Require Import C.jet_clight_forward C.jet_clight_readonly C.jet_clight_internal_frame
  C.jet_clight_internal_permissions.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition modinfo_fe_state (m : mem) : Prop :=
  modinfo_fe_global_rep m /\ forall ofs, ~Mem.perm m modinfo_fe_block ofs Max Writable.

Lemma modinfo_fe_state_initial m : Genv.init_mem jets_secp.prog=Some m -> modinfo_fe_state m.
Proof.
  intro Init;split;[apply modinfo_fe_global_initializes|apply modinfo_fe_global_readonly_initial];exact Init.
Qed.

Local Opaque secp_ge modinfo_fe_block.

Lemma modinfo_fe_state_readback m mf :
  readonly_readback m mf -> keeps_permissions m mf -> modinfo_fe_state m -> modinfo_fe_state mf.
Proof.
  intros [Forward Back] Perms [[Valid [ReadPerm Loads]] Readonly];split.
  - unfold modinfo_fe_global_rep;split;[exact (proj1(Forward _ Valid))|];split.
    + intros ofs Range;apply Perms,ReadPerm;exact Range.
    + intros i w At;pose proof(Loads i w At) as Load.
      destruct(Mem.load_valid_access _ _ _ _ _ Load) as [Access Align].
      assert(FinalAccess:Mem.valid_access mf Mint64 modinfo_fe_block (8*Z.of_nat i) Readable).
      { split;[intros ofs Range;apply Perms,Access;exact Range|exact Align]. }
      destruct(Mem.valid_access_load _ _ _ _ FinalAccess) as [v FinalLoad].
      destruct(Mem.load_loadbytes _ _ _ _ _ FinalLoad) as [bytes [FinalBytes Decode]].
      pose proof(Back _ _ _ _ Valid FinalBytes (fun ofs _=>Readonly ofs)) as InitialBytes.
      pose proof(Mem.loadbytes_load Mint64 m modinfo_fe_block _ bytes InitialBytes Align) as InitialLoad.
      congruence.
  - intros ofs HWritable;apply(Readonly ofs);exact(proj2(Forward _ Valid) ofs Writable HWritable).
Qed.

(** Exactly the real reader's transitive call graph; the tag writer is handled
    separately by its already-proved execution/permission contract. *)
Definition gej_reader_internal_table : list (ident * function) :=
  [(_LSBclear,f_LSBclear);(_LSBkeep,f_LSBkeep);
   (_read8s,f_read8s);(_simplicity_read8,f_simplicity_read8);
   (_read_fe,f_read_fe);(_secp256k1_fe_set_b32,f_secp256k1_fe_set_b32);
   (_secp256k1_fe_normalize_var,f_secp256k1_fe_normalize_var);
   (_secp256k1_fe_is_zero,f_secp256k1_fe_is_zero);(_read_gej,f_read_gej)].

Local Transparent secp_ge.
Lemma gej_reader_internal_table_correct : internal_table_ok secp_ge gej_reader_internal_table.
Proof.
  intros id fd Lookup;apply internal_lookup_in in Lookup.
  cbn [gej_reader_internal_table In] in Lookup.
  repeat destruct Lookup as [Same|Lookup];try contradiction;inversion Same;subst id fd;clear Same.
  all:split.
  all:try solve[match goal with |-exists b,Genv.find_symbol _ ?id=Some b /\ _=>
    exists(secp_symbol_block id) end;split;vm_compute;reflexivity].
  all:split;vm_compute;reflexivity.
Qed.
Local Opaque secp_ge.

Lemma gej_reader_allowed : allowed_call gej_reader_internal_table (Internal f_read_gej).
Proof. exists _read_gej,f_read_gej;split;reflexivity. Qed.

Theorem read_gej_preserves_modinfo m args t mf result :
  Clight2.eval_funcall secp_ge m (Internal f_read_gej) args t mf result ->
  modinfo_fe_state m -> modinfo_fe_state mf.
Proof.
  intro Call;apply modinfo_fe_state_readback.
  - exact(proj2(internal_exec_readback secp_ge gej_reader_internal_table gej_reader_internal_table_correct)
      m _ args t mf result Call gej_reader_allowed).
  - exact(proj2(internal_exec_keeps_permissions secp_ge gej_reader_internal_table gej_reader_internal_table_correct)
      m _ args t mf result Call gej_reader_allowed).
Qed.

Theorem frame_write_keeps_modinfo m mf bd base bw edge cursor count :
  write_frame_at m bd base bw edge cursor count -> 1<=count ->
  lframe (fun b _=>b<>bd /\ b<>bw) m mf ->
  modinfo_fe_state m -> modinfo_fe_global_rep mf.
Proof.
  intros Frame Capacity Outside [Global Readonly].
  pose proof Frame as (_ & _ & _ & _ & _ & Offset & _).
  destruct(write_frame_at_head m bd base bw edge cursor count ltac:(lia) Frame)
    as (_ & _ & Word & _).
  assert(NotDst:modinfo_fe_block<>bd).
  { intro Same;apply(Readonly(base+8));rewrite Same;apply Mem.perm_cur_max.
    apply(proj1 Offset);cbn;lia. }
  assert(NotWord:modinfo_fe_block<>bw).
  { intro Same;apply(Readonly(write_word_address edge cursor));rewrite Same;apply Mem.perm_cur_max.
    apply(proj1 Word);cbn;lia. }
  eapply modinfo_fe_global_lframe;[exact Global|exact Outside|];intros;split;assumption.
Qed.
