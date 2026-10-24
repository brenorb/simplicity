(** Actual final signed carry stores after the original transition loop. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Cop Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_index.
Require Import C.jet_secp_modinv_fg_iteration C.jet_secp_modinv_fg_iteration_prefix.
Require Import C.jet_secp_u128_shift64_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fg_finish := match fg_rest with Ssequence _ s=>s | _=>Sskip end.
Definition fg_finish_cf := match fg_finish with Ssequence s _=>s | _=>Sskip end.
Definition fg_finish_cg := match fg_finish with Ssequence _ s=>s | _=>Sskip end.
Definition fg_finish_cf_call := match fg_finish_cf with Ssequence s _=>s | _=>Sskip end.
Definition fg_finish_cf_store := match fg_finish_cf with Ssequence _ s=>s | _=>Sskip end.
Definition fg_finish_cg_call := match fg_finish_cg with Ssequence s _=>s | _=>Sskip end.
Definition fg_finish_cg_store := match fg_finish_cg with Ssequence _ s=>s | _=>Sskip end.
Definition fg_finish_index := Ebinop Osub (Etempvar _len tint) (Econst_int Int.one tint) tint.
Definition fg_finish_start len := mkst (fg_iter_temps len) fg_iter_regs [] 19.
Definition fg_finish_cf_state len := mkst (PTree.set _t'5 (XLv 15) (fg_iter_temps len)) fg_iter_regs [] 19.
Definition fg_finish_cf_regs len := match xstore fg_iter_regs 0 (8*(Z.of_nat len-1)) Mint64 (XLv 15) with
 | Some regs=>regs | None=>fg_iter_regs end.
Definition fg_finish_cf_written len := mkst (stemps (fg_finish_cf_state len)) (fg_finish_cf_regs len) [] 19.
Definition fg_finish_cg_state len := mkst (PTree.set _t'6 (XLv 17) (stemps (fg_finish_cf_state len))) (fg_finish_cf_regs len) [] 19.
Definition fg_finish_regs len := match xstore (fg_finish_cf_regs len) 1 (8*(Z.of_nat len-1)) Mint64 (XLv 17) with
 | Some regs=>regs | None=>fg_finish_cf_regs len end.
Definition fg_finish_state len := mkst (stemps (fg_finish_cg_state len)) (fg_finish_regs len) [] 19.

Lemma fg_finish_source : fg_finish=Ssequence
 (Ssequence fg_finish_cf_call fg_finish_cf_store) (Ssequence fg_finish_cg_call fg_finish_cg_store).
Proof. reflexivity. Qed.
Lemma fg_finish_cf_source : fg_finish_cf_store=Sassign (fg_index _f fg_finish_index) (Etempvar _t'5 tlong).
Proof. reflexivity. Qed.
Lemma fg_finish_cg_source : fg_finish_cg_store=Sassign (fg_index _g fg_finish_index) (Etempvar _t'6 tlong).
Proof. reflexivity. Qed.
Lemma fg_finish_cf_call_run len :
 xstmt (genv_cenv secp_ge) [] fg_fast_table 100 (snd fg_alloc) (fg_finish_start len) fg_finish_cf_call=
 Some (RDone (fg_finish_cf_state len) ONormal).
Proof. reflexivity. Qed.
Lemma fg_finish_cg_call_run len : (0<len<=5)%nat ->
 xstmt (genv_cenv secp_ge) [] fg_fast_table 100 (snd fg_alloc) (fg_finish_cf_written len) fg_finish_cg_call=
 Some (RDone (fg_finish_cg_state len) ONormal).
Proof. destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;vm_compute;reflexivity. Qed.
Lemma fg_finish_cf_store_run len : (0<len<=5)%nat ->
 xstore fg_iter_regs 0 (8*(Z.of_nat len-1)) Mint64 (XLv 15)=Some (fg_finish_cf_regs len).
Proof. destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;vm_compute;reflexivity. Qed.
Lemma fg_finish_cg_store_run len : (0<len<=5)%nat ->
 xstore (fg_finish_cf_regs len) 1 (8*(Z.of_nat len-1)) Mint64 (XLv 17)=Some (fg_finish_regs len).
Proof. destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;vm_compute;reflexivity. Qed.

Lemma exec_fg_signed_store e le m mf id b value j tmp :
 0<=j<5 -> le!id=Some (Vptr b Ptrofs.zero) ->
 eval_expr secp_ge e le m fg_finish_index (Vint (Int.repr j)) ->
 le!tmp=Some (Vlong value) -> Mem.store Mint64 m b (8*j) (Vlong value)=Some mf ->
 Clight2.exec_stmt secp_ge e le m (Sassign (fg_index id fg_finish_index) (Etempvar tmp tlong)) E0 le mf Out_normal.
Proof.
 intros J Ptr Index Value Store.
 eapply exec_Sassign with (loc:=b) (ofs:=Ptrofs.repr (8*j)) (bf:=Full)
  (v2:=Vlong value) (v:=Vlong value).
 - apply eval_fg_index;[exact J|reflexivity|exact Ptr|exact Index].
 - apply eval_Etempvar;exact Value.
 - reflexivity.
 - apply assign_loc_value with (chunk:=Mint64);[reflexivity|].
   unfold Mem.storev;rewrite Ptrofs.unsigned_repr;
   [exact Store|change Ptrofs.max_unsigned with (2^64-1);lia].
Qed.

Lemma exec_fg_finish_store rho beta e le m st len id tmp r reg value regs' :
 rep rho beta (sregs st) m -> tmatch rho beta (stemps st) le ->
 nth_error (sregs st) r=Some reg -> rfree reg=Some 40 ->
 (stemps st)!id=Some (XP r 0) -> (stemps st)!tmp=Some (XLv value) ->
 (stemps st)!_len=Some (XL2I (XLv 14)) ->
 Int64.loword (rho 14%nat)=Int.repr (Z.of_nat len) -> (0<len<=5)%nat ->
 xstore (sregs st) r (8*(Z.of_nat len-1)) Mint64 (XLv value)=Some regs' -> exists mf,
 Clight2.exec_stmt secp_ge e le m (Sassign (fg_index id fg_finish_index) (Etempvar tmp tlong)) E0 le mf Out_normal /\
 rep rho beta regs' mf /\ map rshape regs'=map rshape (sregs st) /\
 lframe (fun b ofs=>~foot beta (map rshape (sregs st)) b ofs) m mf.
Proof.
 intros Rep Temps Region Owned Pointer Value Length Len Bound Store.
 pose proof (rep_owned_region_base_zero rho beta _ m r reg 40 Rep Region Owned) as Base.
 pose proof (Temps _ _ Pointer) as Ptr;pose proof (Temps _ _ Value) as Val.
 change (le!id=Some (Vptr (blk beta r) (Ptrofs.repr (bas beta r+0)))) in Ptr.
 rewrite Base,Z.add_0_l in Ptr.
 pose proof (Temps _ _ Length) as PLen.
 change (le!_len=Some (Vint (Int64.loword (rho 14%nat)))) in PLen;rewrite Len in PLen.
 assert (Index : eval_expr secp_ge e le m fg_finish_index (Vint (Int.repr (Z.of_nat len-1)))).
 { unfold fg_finish_index;eapply eval_Ebinop;
   [apply eval_Etempvar;exact PLen|constructor|].
   change (Some (Vint (Int.sub (Int.repr (Z.of_nat len)) Int.one))=
    Some (Vint (Int.repr (Z.of_nat len-1)))).
   unfold Int.sub;rewrite Int.unsigned_repr by (change Int.max_unsigned with (2^32-1);lia);reflexivity. }
 destruct (xstore_sound rho beta _ m r _ Mint64 (XLv value) regs' Rep Store)
  as (mf & Write & Addr & Out & Frame).
 rewrite Base,Z.add_0_l in Write.
 exists mf;split.
 - apply exec_fg_signed_store with (b:=blk beta r) (value:=rho value) (j:=Z.of_nat len-1);
    [lia|exact Ptr|exact Index|exact Val|exact Write].
 - split;[exact Out|];split;[eapply xstore_shape;exact Store|apply lframe_unchanged;exact Frame].
Qed.

Local Opaque xstmt fg_finish_start fg_finish_cf_state fg_finish_cg_state secp_ge.
Theorem exec_fg_finish len rho beta e le m : (0<len<=5)%nat ->
 Int64.loword (rho 14%nat)=Int.repr (Z.of_nat len) ->
 rep rho beta fg_iter_regs m -> tmatch rho beta (fg_iter_temps len) le ->
 ematch beta (snd fg_alloc) e -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m fg_finish E0 lef mf Out_normal /\
 rep rho beta (fg_finish_regs len) mf /\ tmatch rho beta (stemps (fg_finish_state len)) lef /\
 lframe (fun b ofs=>~foot beta (map rshape fg_iter_regs) b ofs) m mf.
Proof.
 intros Bound Len Rep Temps Env.
 destruct (fg_exec_done 100 (fg_finish_start len) fg_finish_cf_call (fg_finish_cf_state len)
  rho beta e le m (fg_finish_cf_call_run len) Rep Temps Env) as (lc & mc & Call & RC & TC & FC).
 destruct (exec_fg_finish_store rho beta e lc mc (fg_finish_cf_state len) len _f _t'5 0
  (hd (mkreg [] false None) fg_iter_regs) 15 (fg_finish_cf_regs len) RC TC
  eq_refl eq_refl eq_refl eq_refl eq_refl Len Bound (fg_finish_cf_store_run len Bound))
  as (ms & Store & RS & Shape & FS).
 assert (TS : tmatch rho beta (stemps (fg_finish_cf_written len)) lc) by exact TC.
 destruct (fg_exec_done 100 (fg_finish_cf_written len) fg_finish_cg_call (fg_finish_cg_state len)
  rho beta e lc ms (fg_finish_cg_call_run len Bound) RS TS Env) as (lg & mg & GCall & RG & TG & FG).
 assert (GRegion : nth_error (sregs (fg_finish_cg_state len)) 1=
  Some (nth 1 fg_iter_regs (mkreg [] false None))).
 { destruct len as [|[|[|[|[|[|len]]]]]];try lia;vm_compute;reflexivity. }
 destruct (exec_fg_finish_store rho beta e lg mg (fg_finish_cg_state len) len _g _t'6 1
  (nth 1 fg_iter_regs (mkreg [] false None)) 17 (fg_finish_regs len) RG TG
  GRegion eq_refl eq_refl eq_refl eq_refl Len Bound (fg_finish_cg_store_run len Bound))
  as (mf & GStore & RF & GShape & GF).
 exists lg,mf;split.
 - rewrite fg_finish_source,fg_finish_cf_source,fg_finish_cg_source.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lc) (m1:=ms).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lc) (m1:=mc);[exact Call|exact Store].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lg) (m1:=mg);[exact GCall|exact GStore].
 - split;[exact RF|];split;[exact TG|].
   change (map rshape (fg_finish_cf_regs len)=map rshape fg_iter_regs) in Shape.
   change (lframe (fun b ofs=>~foot beta (map rshape (fg_finish_cf_regs len)) b ofs) ms mg) in FG.
   change (lframe (fun b ofs=>~foot beta (map rshape (fg_finish_cf_regs len)) b ofs) mg mf) in GF.
   rewrite Shape in FG,GF.
   eapply lframe_trans;[exact FC|];eapply lframe_trans;[exact FS|];eapply lframe_trans;[exact FG|exact GF].
Qed.
