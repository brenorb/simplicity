(** The actual canonical normalizer at affine Y, retaining the enclosing
    allocation's ownership and the untouched X/flag bytes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_fns C.jet_secp_linkage C.jets_secp
 C.jet_secp_point_read_values C.jet_secp_local_regions C.jet_secp_point_mul_storage
 C.jet_sx_zval C.jet_sx_zrep C.jet_secp_multiply_normalize_bridge
 C.jet_secp_square_columns C.jet_secp_multiply_finish_product C.jet_secp_write_fe_wide_values.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition affine_nv_y_regs := [mkreg (u64_cells 40 (vars5 0)) true (Some 88)].
Definition affine_nv_y_run := xfun (genv_cenv secp_ge) [] (int_table secp_pure) 400
 f_secp256k1_fe_normalize_var [XP 0 40] affine_nv_y_regs [] 5.
Definition affine_nv_y_tree := Eval vm_compute in affine_nv_y_run.
Definition affine_nv_y_a := Eval vm_compute in
 match affine_nv_y_tree with Some (RIf _ (RDone a _) _) => a | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition affine_nv_y_b := Eval vm_compute in
 match affine_nv_y_tree with Some (RIf _ _ (RDone b _)) => b | _ => mkst (PTree.empty sx) [] [] 0 end.
Definition affine_nv_y_result := RIf nv_c (RDone affine_nv_y_a ONormal) (RDone affine_nv_y_b ONormal).
Lemma affine_nv_y_run_eq : affine_nv_y_run=Some affine_nv_y_result.
Proof. reflexivity. Qed.
Lemma affine_nv_y_log : leaves_log_nil affine_nv_y_result=true.
Proof. reflexivity. Qed.
Lemma affine_nv_y_cells_a : cells0 affine_nv_y_a=map (point_shift_cell 40) (cells0 nv_a).
Proof. reflexivity. Qed.
Lemma affine_nv_y_cells_b : cells0 affine_nv_y_b=map (point_shift_cell 40) (cells0 nv_b).
Proof. reflexivity. Qed.
Lemma affine_nv_y_return rho layout :
 (stemps (fst (rsel rho layout affine_nv_y_result)))!1%positive=None.
Proof. cbn [affine_nv_y_result rsel];destruct (truth rho layout nv_c);reflexivity. Qed.
Lemma affine_nv_y_selected_cells rho layout :
 cells0 (fst (rsel rho layout affine_nv_y_result))=
 map (point_shift_cell 40) (cells0 (fst (rsel rho layout (RIf nv_c (RDone nv_a ONormal) (RDone nv_b ONormal))))).
Proof.
 cbn [affine_nv_y_result rsel];destruct (truth rho layout nv_c);
  [exact affine_nv_y_cells_a|exact affine_nv_y_cells_b].
Qed.

Lemma affine_nv_y_selected_storage rho layout :
 length (sregs (fst (rsel rho layout affine_nv_y_result)))=1%nat /\
 rfree (nth 0 (sregs (fst (rsel rho layout affine_nv_y_result))) (mkreg [] true None))=Some 88.
Proof. cbn [affine_nv_y_result rsel];destruct (truth rho layout nv_c);split;reflexivity. Qed.

Theorem eval_affine_nv_y_symbolic rho layout m : rep rho layout affine_nv_y_regs m -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_var)
  [Vptr (blk layout 0) (Ptrofs.repr (bas layout 0+40))] E0 mf Vundef /\
 rep rho layout (sregs (fst (rsel rho (lay layout) affine_nv_y_result))) mf /\
 Mem.range_perm mf (blk layout 0) 0 88 Cur Freeable /\
 lframe (fun b pos=>~foot layout (map rshape affine_nv_y_regs) b pos) m mf.
Proof.
 intro Rep.
 destruct (xfun_pure secp_ge secp_pure secp_pure_ok 400 f_secp256k1_fe_normalize_var
  [XP 0 40] affine_nv_y_regs 5 _ affine_nv_y_run_eq affine_nv_y_log rho layout m Rep)
  as (mf & result & Call & Final & Return & Shape & Frame).
 rewrite affine_nv_y_return in Return;subst result.
 pose proof (affine_nv_y_selected_storage rho (lay layout)) as [Length Free].
 pose proof (proj2 (rep_free_region rho layout _ mf 0 88 Final ltac:(rewrite Length;lia) Free)) as Owned.
 exists mf;split;[exact Call|];split;[exact Final|];split;assumption.
Qed.

Definition affine_nv_y_bounds (_ : nat) : Z*Z := (0,2^60).
Lemma affine_nv_y_selected_checked rho layout :
 zreg_okb affine_nv_y_bounds 40 (cells0 (fst (rsel rho layout affine_nv_y_result)))=true.
Proof.
 rewrite affine_nv_y_selected_cells.
 change 40 with (40+0) at 1;rewrite point_shift_zreg_checked.
 cbn [rsel];destruct (truth rho layout nv_c);vm_compute;reflexivity.
Qed.
Lemma affine_nv_y_selected_region rho layout : exists reg,
 nth_error (sregs (fst (rsel rho layout affine_nv_y_result))) 0=Some reg /\
 rcells reg=cells0 (fst (rsel rho layout affine_nv_y_result)) /\ rw reg=true /\
 length (rcells reg)=5%nat.
Proof. cbn [affine_nv_y_result rsel];destruct (truth rho layout nv_c);eexists;repeat split;reflexivity. Qed.

Theorem eval_affine_nv_y_from_storage m b t0 t1 t2 t3 t4 :
 fe_at m b 40 [t0;t1;t2;t3;t4] -> Mem.range_perm m b 0 88 Cur Freeable ->
 Int64.unsigned t0<=2^60 -> Int64.unsigned t1<=2^60 -> Int64.unsigned t2<=2^60 ->
 Int64.unsigned t3<=2^60 -> Int64.unsigned t4<=2^60 -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_var)
  [Vptr b (Ptrofs.repr 40)] E0 mf Vundef /\
 fe_at mf b 40 (map Int64.repr (nvz_list (Int64.unsigned t0) (Int64.unsigned t1)
  (Int64.unsigned t2) (Int64.unsigned t3) (Int64.unsigned t4))) /\
 Mem.range_perm mf b 0 88 Cur Freeable /\
 lframe (fun bx pos=>bx<>b \/ pos<40 \/ 80<=pos) m mf.
Proof.
 intros Fe Free B0 B1 B2 B3 B4.
 set (rho:=rho5 t0 t1 t2 t3 t4).
 assert (Bounds : forall n, fst (affine_nv_y_bounds n)<=Int64.unsigned (rho n)<=snd (affine_nv_y_bounds n)).
 { intros n;unfold affine_nv_y_bounds,rho,rho5;cbn [fst snd].
   do 5 (destruct n as [|n];[cbn [nth];split;[apply Int64.unsigned_range|assumption]|]).
   destruct n;cbn [nth];change (Int64.unsigned Int64.zero) with 0;lia. }
 assert (Initial : rep rho [(b,0)] affine_nv_y_regs m).
 { apply (rep_add _ [] [] m b 0);[apply rep_nil|cbn;tauto|].
   apply owned_field_slice_region;[reflexivity|lia|lia|exact Fe|exact Free]. }
 destruct (eval_affine_nv_y_symbolic rho [(b,0)] m Initial) as (mf & Call & Rep & Owned & Frame).
 destruct (affine_nv_y_selected_region rho (lay [(b,0)])) as (reg & Nth & Cells & Writable & Len).
 pose proof (rep_region _ _ _ _ _ _ Rep Nth) as (_ & _ & _ & CellOK & _).
 rewrite Cells,Writable in CellOK.
 destruct (zreg_load rho affine_nv_y_bounds [(b,0)] Bounds mf 0 true _ 40
  (affine_nv_y_selected_checked rho (lay [(b,0)])) CellOK) as [Loads Perms].
 assert (Values : zcells (zrho rho) (cells0 (fst (rsel rho (lay [(b,0)]) affine_nv_y_result)))=
  nvz_list (Int64.unsigned t0) (Int64.unsigned t1) (Int64.unsigned t2) (Int64.unsigned t3) (Int64.unsigned t4)).
 { rewrite affine_nv_y_selected_cells,point_shift_zcells;cbn [rsel].
   assert (Truth : truth rho (lay [(b,0)]) nv_c=negb (Z.eqb (zval (zrho rho) nv_c) 0)).
   { eapply truth_zval;[exact Bounds|vm_compute;reflexivity|reflexivity]. }
   rewrite Truth.
   assert (Ez : zval (zrho rho) nv_c=zval
    (zrho5 (Int64.unsigned t0) (Int64.unsigned t1) (Int64.unsigned t2) (Int64.unsigned t3) (Int64.unsigned t4)) nv_c).
   { apply zval_ext;exact (zrho_rho5 t0 t1 t2 t3 t4). }
   rewrite Ez.
   rewrite nv_bridge;destruct (negb (Z.eqb (zval _ nv_c) 0));cbn [fst];
    apply zcells_ext;exact (zrho_rho5 t0 t1 t2 t3 t4). }
 rewrite Values in Loads.
 exists mf;split;[exact Call|];split.
 - split;[lia|];split;[exists 5;reflexivity|];split;[change (80<=18446744073709551615);lia|];split.
   + intros pos Range;eapply Mem.perm_implies;[apply Owned;lia|constructor].
   + intros i x NthX;rewrite nth_error_map in NthX.
     destruct (nth_error (nvz_list _ _ _ _ _) i) as [z|] eqn:NthZ;[|discriminate].
     injection NthX as <-;exact (Loads i z NthZ).
 - split;[exact Owned|].
   eapply lframe_implies;[exact Frame|].
   intros bx pos Outside _ (r & sh & d & ch & NS & HC & HB & Range).
   destruct r;[|destruct r;discriminate NS].
   injection NS as <-;cbn [affine_nv_y_regs rshape fst snd rcells u64_cells vars5 map cshape In] in HC.
   repeat destruct HC as [HC|HC];try contradiction;injection HC as <- <-;
    cbn [bas blk lay nth fst snd size_chunk] in HB,Range;
    destruct Outside as [Outside|[Outside|Outside]];congruence || lia.
Qed.

Theorem eval_affine_nv_y_words w m b : square_input_bounds w ->
 fe_at m b 40 (words5 w) -> Mem.range_perm m b 0 88 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_var)
  [Vptr b (Ptrofs.repr 40)] E0 mf Vundef /\
 fe_at mf b 40 (map Int64.repr (fe_limbs_of (radix_value w mod feP))) /\
 Mem.range_perm mf b 0 88 Cur Freeable /\
 lframe (fun bx pos=>bx<>b \/ pos<40 \/ 80<=pos) m mf.
Proof.
 intros Bounds Field Free.
 assert (B : forall i, (i<5)%nat -> Int64.unsigned (w i)<=2^60).
 { intros i HI;pose proof (Bounds i HI);destruct (Nat.eqb i 4);lia. }
 destruct (eval_affine_nv_y_from_storage m b (w 0%nat) (w 1%nat) (w 2%nat) (w 3%nat) (w 4%nat)
  Field Free (B 0%nat ltac:(lia)) (B 1%nat ltac:(lia)) (B 2%nat ltac:(lia))
  (B 3%nat ltac:(lia)) (B 4%nat ltac:(lia))) as (mf & Call & Output & Owned & Frame).
 rewrite wide_normalized_limbs_canonical in Output by (apply B;lia).
 rewrite <-radix_value_matches_normalizer in Output.
 exists mf;split;[exact Call|];split;[exact Output|];split;assumption.
Qed.
