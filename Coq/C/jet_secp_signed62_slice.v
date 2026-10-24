(** Original field/signed62 conversions at an output slice. The symbolic
    regions do not claim the slice is a whole allocation; original ownership
    is instead preserved through the actual internal C execution. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_sx_revalue_cells C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv.
Require Import C.jet_secp_signed62_repack C.jet_secp_fe_b32 C.jet_secp_b32_exec C.jet_secp_field_add_initial.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_clight_internal_frame C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition fe_repack_slice_regs := [fe_undef;fe_reg(vars5 0)].
Definition fe_repack_slice_run to62 := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 160
  (fe_repack_function to62) fe_repack_args fe_repack_slice_regs [] 5.
Definition fe_to62_slice_tree := Eval vm_compute in fe_repack_slice_run true.
Definition fe_from62_slice_tree := Eval vm_compute in fe_repack_slice_run false.
Definition fe_repack_slice_tree (to62:bool) := if to62 then fe_to62_slice_tree else fe_from62_slice_tree.
Definition fe_repack_slice_state to62 := match fe_repack_slice_tree to62 with
  | Some(RDone st _)=>st | _=>mkst(PTree.empty sx) [] [] 0 end.
Definition fe_repack_slice_out_regs to62 :=
  [mkreg(u64_cells 0 (fe_repack_out to62)) true None;fe_reg(vars5 0)].

Lemma fe_repack_slice_run_eq to62 : fe_repack_slice_run to62=Some(RDone(fe_repack_slice_state to62) ONormal).
Proof. destruct to62;reflexivity. Qed.
Lemma fe_repack_slice_return to62 : (stemps(fe_repack_slice_state to62))!1%positive=None.
Proof. destruct to62;reflexivity. Qed.
Lemma fe_repack_slice_shape to62 : sregs(fe_repack_slice_state to62)=fe_repack_slice_out_regs to62.
Proof. destruct to62;reflexivity. Qed.

Theorem eval_fe_repack_slice_symbolic to62 rho beta m : rep rho beta fe_repack_slice_regs m -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal(fe_repack_function to62))
    [Vptr(blk beta 0)(Ptrofs.repr(bas beta 0));Vptr(blk beta 1)(Ptrofs.repr(bas beta 1))] E0 mf Vundef /\
  rep rho beta (fe_repack_slice_out_regs to62) mf /\
  lframe (fun b pos=>~foot beta (map rshape fe_repack_slice_regs) b pos) m mf.
Proof.
  intro Initial.
  destruct(xfun_pure secp_ge secp_pure secp_pure_ok 160 (fe_repack_function to62)
    fe_repack_args fe_repack_slice_regs 5 _ (fe_repack_slice_run_eq to62)
    ltac:(destruct to62;reflexivity) rho beta m Initial)
    as (mf & result & Call & Final & Return & Shape & Frame).
  cbn [rsel fst] in Final,Return;rewrite fe_repack_slice_return in Return;subst result.
  change(map(den rho(lay beta))fe_repack_args) with
    [Vptr(blk beta 0)(Ptrofs.repr(bas beta 0+0));Vptr(blk beta 1)(Ptrofs.repr(bas beta 1+0))] in Call.
  rewrite !Z.add_0_r in Call;rewrite fe_repack_slice_shape in Final.
  exists mf;split;[exact Call|];split;assumption.
Qed.

Lemma fe_repack_slice_fields to62 w beta m : rep w beta (fe_repack_slice_out_regs to62) m ->
  fe_at m (blk beta 0)(bas beta 0)(words5(fe_repack_words to62 w)) /\
  fe_at m (blk beta 1)(bas beta 1)(words5 w).
Proof.
  intro Final.
  pose proof(rep_region _ _ _ m 0 _ Final eq_refl) as R0.
  pose proof(rep_region _ _ _ m 1 _ Final eq_refl) as R1.
  pose proof(region_ok_revalue_u64 w beta m 0 (fe_repack_out to62) true None R0
    ltac:(destruct to62;reflexivity)) as V0.
  rewrite(revalue_u64_machine_map _ _ _ _ (fe_repack_output_den to62 w beta)) in V0.
  pose proof(region_ok_revalue_u64 w beta m 1 (vars5 0) true None R1 eq_refl) as V1.
  assert(Den:map(den w(lay beta))(vars5 0)=map Vlong(words5 w)) by reflexivity.
  rewrite(revalue_u64_machine_map _ _ _ _ Den) in V1.
  split;[exact(u64_region_fe_at _ _ _ _ _ _ V0)|exact(u64_region_fe_at _ _ _ _ _ _ V1)].
Qed.

Definition fe_repack_slice_table (to62:bool) :=
  [(if to62 then _secp256k1_fe_to_signed62 else _secp256k1_fe_from_signed62,fe_repack_function to62)].
Lemma fe_repack_slice_table_ok to62 : internal_table_ok secp_ge (fe_repack_slice_table to62).
Proof.
  intros id fd Lookup;apply internal_lookup_in in Lookup.
  destruct Lookup as [Same|Nil];[injection Same as <- <-|contradiction].
  split.
  - apply secp_pure_ok;destruct to62;unfold secp_pure,fe_repack_function;repeat(first[left;reflexivity|right]).
  - destruct to62;split;reflexivity.
Qed.

Lemma fe_repack_slice_foot bout base bin b pos :
  foot [(bout,base);(bin,0)] (map rshape fe_repack_slice_regs) b pos ->
  (b=bout /\ base<=pos<base+40) \/ b=bin.
Proof.
  intros(r & sh & d & ch & At & Cell & Block & Range).
  destruct r as [|[|r]].
  - left;split;[exact Block|].
    cbn [fe_repack_slice_regs map nth_error rshape fe_undef rcells rw rfree] in At;injection At as <-.
    cbn [fst map cshape cofs cchunk] in Cell.
    destruct Cell as [Cell|[Cell|[Cell|[Cell|[Cell|Cell]]]]];try contradiction;
      inversion Cell;subst d ch;cbn [bas lay nth snd] in Range;
      change(size_chunk Mint64) with 8 in Range;lia.
  - right;exact Block.
  - destruct r;discriminate At.
Qed.

Theorem eval_fe_repack_to_slice to62 w m bout base bin :
  bout<>bin -> 0<=base -> (8|base) -> base+40<=Ptrofs.max_unsigned ->
  Mem.range_perm m bout base (base+40) Cur Writable -> fe_at m bin 0 (words5 w) -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal(fe_repack_function to62))
    [Vptr bout(Ptrofs.repr base);Vptr bin Ptrofs.zero] E0 mf Vundef /\
  fe_at mf bout base (words5(fe_repack_words to62 w)) /\ fe_at mf bin 0 (words5 w) /\
  keeps_permissions m mf /\
  lframe (fun b pos=>(b<>bout \/ pos<base \/ base+40<=pos) /\ b<>bin) m mf.
Proof.
  intros Separate Base Align Max Writable Source.
  assert(Initial:rep w [(bout,base);(bin,0)] fe_repack_slice_regs m).
  { apply two_region_rep_separate;[reflexivity|exact Separate| |].
    - apply region_fe_undefined_from_storage;[exact Base|exact Align|exact Max|exact Writable].
    - apply field_region_from_values;exact Source. }
  destruct(eval_fe_repack_slice_symbolic to62 w [(bout,base);(bin,0)] m Initial)
    as (mf & Call & Final & Frame).
  destruct(fe_repack_slice_fields to62 w [(bout,base);(bin,0)] mf Final) as [Out Inp].
  assert(Allowed:allowed_call(fe_repack_slice_table to62)(Internal(fe_repack_function to62))).
  { exists(if to62 then _secp256k1_fe_to_signed62 else _secp256k1_fe_from_signed62),
      (fe_repack_function to62);split;[destruct to62;reflexivity|reflexivity]. }
  assert(Keep:keeps_permissions m mf).
  { exact(proj2(internal_exec_keeps_permissions secp_ge (fe_repack_slice_table to62)
      (fe_repack_slice_table_ok to62)) m _ _ E0 mf Vundef Call Allowed). }
  exists mf;split;[exact Call|];split;[exact Out|];split;[exact Inp|];split;[exact Keep|].
  eapply lframe_implies;[exact Frame|];intros b pos [Outside NotIn] Valid Foot.
  destruct(fe_repack_slice_foot bout base bin b pos Foot) as [[Same Range]|Same];
    [destruct Outside as [NotOut|[Before|After]];[contradiction|lia|lia]|contradiction].
Qed.
