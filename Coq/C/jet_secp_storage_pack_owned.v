(** Memory and canonical-value contract of the original native field packer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Memory Values Ctypes Clight ClightBigstep Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_rep
 C.jet_secp_storage_pack C.jet_secp_storage_unpack C.jet_secp_storage_numeric
 C.jets_secp C.jet_secp_linkage C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_b32_exec
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve
 C.jet_clight_internal_permissions.
Require Import C.jet_secp_storage_pack_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Lemma storage_pack_initial value m bout dbase bin sbase:
 bout<>bin ->0<=dbase ->(8|dbase) ->dbase+32<=Ptrofs.max_unsigned ->
 Mem.range_perm m bout dbase (dbase+32) Cur Writable ->
 fe_at m bin sbase (map Int64.repr (fe_limbs_of value)) ->
 rep (limb_rho value) [(bout,dbase);(bin,sbase)] storage_pack_regs m.
Proof.
 intros Separate Base Align Max Writable Input.
 apply two_region_rep_separate;[reflexivity|exact Separate| |].
 - split;[exact Base|];split.
   + eapply Mem.perm_valid_block;apply (Writable dbase);lia.
   + split;[reflexivity|];split;[|exact I].
     apply Forall_forall;intros c Member.
     cbn [storage_pack_dest rcells In] in Member.
     repeat match goal with H:_\/_|-_=>destruct H as [H|H] end;
      try contradiction;subst c;apply writable_undefined_cell;
      cbn [bas lay nth snd size_chunk align_chunk];try lia.
     all:try (intros pos Range;apply Writable;lia).
     all:apply Z.divide_add_r;[exact Align|].
     all:match goal with |- (8|?n)=>exists (n/8);reflexivity end.
 - apply region_canonical_limbs_from_fe_at;exact Input.
Qed.
Lemma storage_pack_final_readable w beta m:
 rep w beta storage_pack_out_regs m ->
 field_storage_readable m (blk beta 0) (bas beta 0) (storage_pack_words w).
Proof.
 intro Final;pose proof (rep_region _ _ _ _ 0 _ Final eq_refl) as Region.
 pose proof Region as (Base & Valid & Sorted & Cells & Owner).
 cbn [storage_pack_out_regs u64_cells storage_pack_out] in Cells.
 inversion Cells as [|? ? C0 T0];subst.
 inversion T0 as [|? ? C1 T1];subst.
 inversion T1 as [|? ? C2 T2];subst.
 inversion T2 as [|? ? C3 T3];subst.
 cbv beta iota zeta delta [cell_ok cofs cchunk cval den] in C0,C1,C2,C3.
 change (size_chunk Mint64) with 8 in C0,C1,C2,C3.
 change (align_chunk Mint64) with 8 in C0.
 destruct C0 as (M0 & A0 & P0 & V0).
 destruct C1 as (M1 & A1 & P1 & V1).
 destruct C2 as (M2 & A2 & P2 & V2).
 destruct C3 as (M3 & A3 & P3 & V3).
 cbn [rw] in P0,P1,P2,P3.
 split;[exact Base|];split;[rewrite Z.add_0_r in A0;exact A0|];split;[lia|];split.
 - intros pos Range;eapply Mem.perm_implies with (p1:=Writable);[|constructor].
   destruct (Z_lt_dec pos (bas beta 0+8));[apply P0;lia|].
   destruct (Z_lt_dec pos (bas beta 0+16));[apply P1;lia|].
   destruct (Z_lt_dec pos (bas beta 0+24));[apply P2;lia|].
   apply P3;lia.
 - intros i Index;destruct i as [|[|[|[|i]]]];try lia;
   first [exact (proj1 (V0 _ eq_refl))|exact (proj1 (V1 _ eq_refl))|
          exact (proj1 (V2 _ eq_refl))|exact (proj1 (V3 _ eq_refl))].
Qed.
Lemma storage_pack_allowed:allowed_call secp_closed_helpers (Internal f_secp256k1_fe_to_storage).
Proof. exists _secp256k1_fe_to_storage,f_secp256k1_fe_to_storage;split;vm_compute;reflexivity. Qed.
Lemma storage_pack_closed:closed_stmtb secp_closed_helpers (fn_body f_secp256k1_fe_to_storage)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma storage_pack_final_source value bout dbase bin sbase m mf:
 fe_at m bin sbase (map Int64.repr (fe_limbs_of value)) ->keeps_permissions m mf ->
 rep (limb_rho value) [(bout,dbase);(bin,sbase)] storage_pack_out_regs mf ->
 fe_at mf bin sbase (map Int64.repr (fe_limbs_of value)).
Proof.
 intros (Base & Align & Max & Perm & Loads) Keep Final.
 pose proof (rep_region _ _ _ _ 1 _ Final eq_refl) as Source.
 split;[exact Base|];split;[exact Align|];split;[exact Max|];split.
 - intros pos Range;apply Keep,Perm;exact Range.
 - intros i w Nth.
   assert (Bound:(i<5)%nat).
   { assert (Index:(i<length (map Int64.repr (fe_limbs_of value)))%nat)
     by (apply nth_error_Some;congruence).
     change (i<5)%nat in Index;exact Index. }
   assert (Var:nth_error (vars5 0) i=Some (XLv i)).
   { clear -Bound;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity. }
   pose proof (region_load _ _ _ _ _ _ _ _ Source (u64_cells_nth _ 0 i (XLv i) Var)) as Load.
   cbn [blk bas lay nth fst snd den] in Load.
   apply nth_error_nth with (d:=Int64.zero) in Nth.
   change (nth i (map Int64.repr (fe_limbs_of value)) (Int64.repr 0)=w) in Nth.
   rewrite map_nth in Nth;subst w;exact Load.
Qed.
Lemma storage_pack_foot_bounds bout dbase bin sbase b pos:
 foot [(bout,dbase);(bin,sbase)] (map rshape storage_pack_regs) b pos ->
 (b=bout /\dbase<=pos<dbase+32) \/(b=bin /\sbase<=pos<sbase+40).
Proof.
 intros (r & sh & d & ch & Region & Cell & Block & Range).
 destruct r as [|[|r]].
 - left;split;[exact Block|].
   cbn [storage_pack_regs map nth_error rshape storage_pack_dest rcells rw rfree] in Region;
   injection Region as <-.
   cbn [In map cshape cofs cchunk fst snd] in Cell.
   repeat destruct Cell as [Cell|Cell];
    try contradiction;injection Cell as <- <-;
    cbn [bas lay nth snd size_chunk] in Range;lia.
 - right;split;[exact Block|].
   cbn [storage_pack_regs map nth_error rshape rcells rw rfree] in Region;injection Region as <-.
   apply in_map_iff in Cell as (c & Shape & Member).
   destruct (u64_cells_In (vars5 0) 0 c Member) as (i & x & Index & Eq);subst c.
   pose proof (proj1 (vars5_zero_nth _ _ Index)) as Bound.
   inversion Shape;subst d ch.
   change (sbase+8*Z.of_nat i<=pos<sbase+8*Z.of_nat i+8) in Range;lia.
 - destruct r;discriminate Region.
Qed.
Theorem eval_fe_to_storage_owned value m bout dbase bin sbase:
 0<=value<2^256 ->bout<>bin ->0<=dbase ->(8|dbase) ->dbase+32<=Ptrofs.max_unsigned ->
 Mem.range_perm m bout dbase (dbase+32) Cur Freeable ->
 fe_at m bin sbase (map Int64.repr (fe_limbs_of value)) ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_to_storage)
 [Vptr bout (Ptrofs.repr dbase);Vptr bin (Ptrofs.repr sbase)] E0 mf Vundef /\
 field_storage_readable mf bout dbase (storage_pack_words (limb_rho value)) /\
 field_storage_value (storage_pack_words (limb_rho value))=value /\
 fe_at mf bin sbase (map Int64.repr (fe_limbs_of value)) /\
 keeps_permissions m mf /\
 lframe (fun b pos=>~foot [(bout,dbase);(bin,sbase)] (map rshape storage_pack_regs) b pos) m mf /\
 readonly_preserved m mf.
Proof.
 intros Value Separate Base Align Max Free Input.
 destruct (eval_storage_pack_symbolic (limb_rho value) [(bout,dbase);(bin,sbase)] m
  (storage_pack_initial value m bout dbase bin sbase Separate Base Align Max
   ltac:(intros pos Range;eapply Mem.perm_implies;[apply Free;exact Range|constructor]) Input))
 as (mf & Call & Final & Frame).
 pose proof (proj2 (internal_exec_keeps_permissions _ _ secp_closed_helpers_ok)
  _ _ _ _ _ _ Call storage_pack_allowed) as Keep.
 exists mf;split;[exact Call|];split;[exact (storage_pack_final_readable _ _ _ Final)|];split.
 - apply storage_pack_canonical;exact Value.
 - split;[exact (storage_pack_final_source value bout dbase bin sbase m mf Input Keep Final)|].
   split;[exact Keep|];split;[exact Frame|].
   eapply secp_closed_function_preserved;[exact storage_pack_closed|reflexivity|exact Call].
Qed.
