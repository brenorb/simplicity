(** Complete execution of the original inverse transition loop body, at
    each valid nonzero limb index. Computed addresses, masked stores, signed
    accumulations/shifts and framing are derived from initial storage.
    Full-loop induction and the public inversion composition remain open. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_index.
Require Import C.jet_secp_modinv_fg_iteration_prefix.
Require Import C.jet_secp_modinv_fg_store.
Require Import C.jet_secp_statement_prefix.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fg_cf_chunk := nth 6 (fst fg_work_parts) Sskip.
Definition fg_cf_low_call := match fg_cf_chunk with Ssequence call _=>call | _=>Sskip end.
Definition fg_cf_low_store := match fg_cf_chunk with Ssequence _ store=>store | _=>Sskip end.
Definition fg_previous_expr := Ebinop Osub (Etempvar _i tint) (Econst_int Int.one tint) tint.
Definition fg_cf_mask_expr := Ebinop Oand (Etempvar _t'3 tulong) (Etempvar _M62 tulong) tulong.
Lemma fg_cf_low_store_source : fg_cf_low_store=Sassign (fg_index _f fg_previous_expr) fg_cf_mask_expr.
Proof. reflexivity. Qed.

Definition fg_cf_call_run k := xstmt (genv_cenv secp_ge) [] fg_fast_table 100 (snd fg_alloc)
 (fg_iter_prefix_state k) fg_cf_low_call.
Definition fg_cf_call_state (k : nat) := match k with
 | 1%nat=>match fg_cf_call_run 1 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | 2%nat=>match fg_cf_call_run 2 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | 3%nat=>match fg_cf_call_run 3 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | 4%nat=>match fg_cf_call_run 4 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | _=>mkst (PTree.empty sx) [] [] 0 end.
Definition fg_cf_low_term k := XLb Band (fst (fg_iter_cf k)) (XLsh Hshru (XLc (Int64.repr (-1))) 2).
Definition fg_cf_store_regs k := match xstore (sregs (fg_cf_call_state k)) 0
 (8*(Z.of_nat k-1)) Mint64 (fg_cf_low_term k) with
 | Some regs=>regs | None=>sregs (fg_cf_call_state k) end.
Definition fg_cf_store_state k := mkst (stemps (fg_cf_call_state k)) (fg_cf_store_regs k)
 (slog (fg_cf_call_state k)) (snv (fg_cf_call_state k)).

Lemma fg_cf_call_run_eq k : (0<k<5)%nat ->
 fg_cf_call_run k=Some (RDone (fg_cf_call_state k) ONormal).
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.
Lemma fg_cf_store_run_eq k : (0<k<5)%nat ->
 xstore (sregs (fg_cf_call_state k)) 0 (8*(Z.of_nat k-1)) Mint64 (fg_cf_low_term k)=Some (fg_cf_store_regs k).
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.
Lemma fg_cf_mask_run k : (0<k<5)%nat ->
 xexpr (genv_cenv secp_ge) (snd fg_alloc) [] (fg_cf_call_state k) fg_cf_mask_expr=Some (fg_cf_low_term k).
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.
Lemma fg_cf_call_index k : (0<k<5)%nat ->
 (stemps (fg_cf_call_state k))!_i=Some (XIc (Int.repr (Z.of_nat k))).
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.
Lemma fg_cf_call_pointer k : (0<k<5)%nat ->
 (stemps (fg_cf_call_state k))!_f=Some (XP 0 0).
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.
Lemma fg_cf_call_region k : (0<k<5)%nat ->
 nth_error (sregs (fg_cf_call_state k)) 0=Some (hd (mkreg [] false None) fg_regs).
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.

Local Opaque xstmt fg_cf_call_state fg_cf_store_regs fg_iter_prefix_state fg_cf_low_store fg_fast_table fg_alloc secp_ge.
Lemma fg_exec_done fuel st stmt final rho beta e le m :
 xstmt (genv_cenv secp_ge) [] fg_fast_table fuel (snd fg_alloc) st stmt=Some (RDone final ONormal) ->
 rep rho beta (sregs st) m -> tmatch rho beta (stemps st) le -> ematch beta (snd fg_alloc) e ->
 exists le' mf,Clight2.exec_stmt secp_ge e le m stmt E0 le' mf Out_normal /\
 rep rho beta (sregs final) mf /\ tmatch rho beta (stemps final) le' /\
 lframe (fun b ofs=>~foot beta (map rshape (sregs st)) b ofs) m mf.
Proof.
 intros Run Rep Temps Env.
 destruct (fg_iter_sound fuel (snd fg_alloc) st stmt (RDone final ONormal) Run rho beta e le m Rep Temps Env)
  as (le' & mf & out & Exec & Post).
 - split;intros;discriminate.
 - intros r _ [].
 - exact I.
 - apply Forall_forall;intros;exact I.
 - destruct Post as (Out & Match & Normal & Shape & Inv & Frame).
   cbn [rsel fst snd] in Out,Match,Normal;destruct out;cbn [outmatch] in Normal;try contradiction.
   exists le',mf;split;[exact Exec|];split;[exact Out|];split;[exact Match|].
   eapply lframe_implies;[exact Frame|];intros b ofs Outside Valid;
    split;[exact Valid|];split;[exact Outside|tauto].
Qed.

Definition fg_cf_shift := nth 7 (fst fg_work_parts) Sskip.
Definition fg_cf_shift_run k := xstmt (genv_cenv secp_ge) [] fg_fast_table 100 (snd fg_alloc)
 (fg_cf_store_state k) fg_cf_shift.
Definition fg_cf_shift_state (k : nat) := match k with
 | 1%nat=>match fg_cf_shift_run 1 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | 2%nat=>match fg_cf_shift_run 2 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | 3%nat=>match fg_cf_shift_run 3 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | 4%nat=>match fg_cf_shift_run 4 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | _=>mkst (PTree.empty sx) [] [] 0 end.
Definition fg_cg_chunk := nth 8 (fst fg_work_parts) Sskip.
Definition fg_cg_low_call := match fg_cg_chunk with Ssequence call _=>call | _=>Sskip end.
Definition fg_cg_low_store := match fg_cg_chunk with Ssequence _ store=>store | _=>Sskip end.
Definition fg_cg_mask_expr := Ebinop Oand (Etempvar _t'4 tulong) (Etempvar _M62 tulong) tulong.
Definition fg_cg_call_run k := xstmt (genv_cenv secp_ge) [] fg_fast_table 100 (snd fg_alloc)
 (fg_cf_shift_state k) fg_cg_low_call.
Definition fg_cg_call_state (k : nat) := match k with
 | 1%nat=>match fg_cg_call_run 1 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | 2%nat=>match fg_cg_call_run 2 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | 3%nat=>match fg_cg_call_run 3 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | 4%nat=>match fg_cg_call_run 4 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | _=>mkst (PTree.empty sx) [] [] 0 end.
Definition fg_cg_low_term k := XLb Band (fst (fg_iter_cg k)) (XLsh Hshru (XLc (Int64.repr (-1))) 2).
Definition fg_cg_store_regs k := match xstore (sregs (fg_cg_call_state k)) 1
 (8*(Z.of_nat k-1)) Mint64 (fg_cg_low_term k) with
 | Some regs=>regs | None=>sregs (fg_cg_call_state k) end.
Definition fg_cg_store_state k := mkst (stemps (fg_cg_call_state k)) (fg_cg_store_regs k)
 (slog (fg_cg_call_state k)) (snv (fg_cg_call_state k)).
Definition fg_cg_shift := snd fg_work_parts.
Definition fg_cg_shift_run k := xstmt (genv_cenv secp_ge) [] fg_fast_table 100 (snd fg_alloc)
 (fg_cg_store_state k) fg_cg_shift.
Definition fg_iter_final_state (k : nat) := match k with
 | 1%nat=>match fg_cg_shift_run 1 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | 2%nat=>match fg_cg_shift_run 2 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | 3%nat=>match fg_cg_shift_run 3 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | 4%nat=>match fg_cg_shift_run 4 with Some (RDone st _)=>st | _=>mkst (PTree.empty sx) [] [] 0 end
 | _=>mkst (PTree.empty sx) [] [] 0 end.
Lemma fg_cg_low_store_source : fg_cg_low_store=Sassign (fg_index _g fg_previous_expr) fg_cg_mask_expr.
Proof. reflexivity. Qed.
Lemma fg_iteration_suffix_source : fg_work_suffix=Ssequence fg_cf_chunk
 (Ssequence fg_cf_shift (Ssequence fg_cg_chunk fg_cg_shift)).
Proof. reflexivity. Qed.
Lemma fg_cf_shift_run_eq k : (0<k<5)%nat ->
 fg_cf_shift_run k=Some (RDone (fg_cf_shift_state k) ONormal).
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.
Lemma fg_cg_call_run_eq k : (0<k<5)%nat ->
 fg_cg_call_run k=Some (RDone (fg_cg_call_state k) ONormal).
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.
Lemma fg_cg_store_run_eq k : (0<k<5)%nat ->
 xstore (sregs (fg_cg_call_state k)) 1 (8*(Z.of_nat k-1)) Mint64 (fg_cg_low_term k)=Some (fg_cg_store_regs k).
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.
Lemma fg_cg_mask_run k : (0<k<5)%nat ->
 xexpr (genv_cenv secp_ge) (snd fg_alloc) [] (fg_cg_call_state k) fg_cg_mask_expr=Some (fg_cg_low_term k).
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.
Lemma fg_cg_call_index k : (0<k<5)%nat ->
 (stemps (fg_cg_call_state k))!_i=Some (XIc (Int.repr (Z.of_nat k))).
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.
Lemma fg_cg_call_pointer k : (0<k<5)%nat ->
 (stemps (fg_cg_call_state k))!_g=Some (XP 1 0).
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.
Lemma fg_cg_call_region k : (0<k<5)%nat ->
 nth_error (sregs (fg_cg_call_state k)) 1=Some (nth 1 fg_regs (mkreg [] false None)).
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.
Lemma fg_cg_shift_run_eq k : (0<k<5)%nat ->
 fg_cg_shift_run k=Some (RDone (fg_iter_final_state k) ONormal).
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.

Theorem exec_fg_cf_low_store k rho beta e le m : (0<k<5)%nat ->
 rep rho beta (sregs (fg_cf_call_state k)) m -> tmatch rho beta (stemps (fg_cf_call_state k)) le ->
 ematch beta (snd fg_alloc) e -> exists mf,
 Clight2.exec_stmt secp_ge e le m fg_cf_low_store E0 le mf Out_normal /\
 rep rho beta (sregs (fg_cf_store_state k)) mf /\
 lframe (fun b ofs=>~foot beta (map rshape (sregs (fg_cf_call_state k))) b ofs) m mf.
Proof.
 intros K Rep Temps Env.
 pose proof (Temps _ _ (fg_cf_call_index k K)) as Index.
 change (le!_i=Some (Vint (Int.repr (Z.of_nat k)))) in Index.
 assert (Previous : eval_expr secp_ge e le m fg_previous_expr (Vint (Int.repr (Z.of_nat k-1)))).
 { apply eval_fg_previous;[lia|exact Index]. }
 destruct (exec_fg_symbolic_index_store rho beta e le m (fg_cf_call_state k) (snd fg_alloc)
  _f 0 (hd (mkreg [] false None) fg_regs) fg_previous_expr (Z.of_nat k-1)
  fg_cf_mask_expr (fg_cf_low_term k) (fg_cf_store_regs k)
  Rep Temps Env (fg_cf_call_region k K) eq_refl (fg_cf_call_pointer k K)
  ltac:(lia) eq_refl eq_refl Previous (fg_cf_mask_run k K) eq_refl (fg_cf_store_run_eq k K))
  as (mf & Exec & Out & Shape & Frame).
 exists mf;rewrite fg_cf_low_store_source;split;[exact Exec|];split;[exact Out|exact Frame].
Qed.

Local Opaque fg_cg_call_state fg_cg_store_regs fg_cf_shift_state fg_iter_final_state.
Theorem exec_fg_cg_low_store k rho beta e le m : (0<k<5)%nat ->
 rep rho beta (sregs (fg_cg_call_state k)) m -> tmatch rho beta (stemps (fg_cg_call_state k)) le ->
 ematch beta (snd fg_alloc) e -> exists mf,
 Clight2.exec_stmt secp_ge e le m fg_cg_low_store E0 le mf Out_normal /\
 rep rho beta (sregs (fg_cg_store_state k)) mf /\
 lframe (fun b ofs=>~foot beta (map rshape (sregs (fg_cg_call_state k))) b ofs) m mf.
Proof.
 intros K Rep Temps Env.
 pose proof (Temps _ _ (fg_cg_call_index k K)) as Index.
 change (le!_i=Some (Vint (Int.repr (Z.of_nat k)))) in Index.
 assert (Previous : eval_expr secp_ge e le m fg_previous_expr (Vint (Int.repr (Z.of_nat k-1)))).
 { apply eval_fg_previous;[lia|exact Index]. }
 destruct (exec_fg_symbolic_index_store rho beta e le m (fg_cg_call_state k) (snd fg_alloc)
  _g 1 (nth 1 fg_regs (mkreg [] false None)) fg_previous_expr (Z.of_nat k-1)
  fg_cg_mask_expr (fg_cg_low_term k) (fg_cg_store_regs k)
  Rep Temps Env (fg_cg_call_region k K) eq_refl (fg_cg_call_pointer k K)
  ltac:(lia) eq_refl eq_refl Previous (fg_cg_mask_run k K) eq_refl (fg_cg_store_run_eq k K))
  as (mf & Exec & Out & Shape & Frame).
 exists mf;rewrite fg_cg_low_store_source;split;[exact Exec|];split;[exact Out|exact Frame].
Qed.

Lemma fg_iteration_shapes k : (0<k<5)%nat ->
 map rshape (sregs (fg_iter_prefix_state k))=map rshape fg_iter_regs /\
 map rshape (sregs (fg_cf_call_state k))=map rshape fg_iter_regs /\
 map rshape (sregs (fg_cf_store_state k))=map rshape fg_iter_regs /\
 map rshape (sregs (fg_cf_shift_state k))=map rshape fg_iter_regs /\
 map rshape (sregs (fg_cg_call_state k))=map rshape fg_iter_regs /\
 map rshape (sregs (fg_cg_store_state k))=map rshape fg_iter_regs.
Proof.
 destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;repeat split;reflexivity.
Qed.

Lemma fg_cf_store_temps k : stemps (fg_cf_store_state k)=stemps (fg_cf_call_state k).
Proof. unfold fg_cf_store_state;cbn [stemps];reflexivity. Qed.
Lemma fg_cg_store_temps k : stemps (fg_cg_store_state k)=stemps (fg_cg_call_state k).
Proof. unfold fg_cg_store_state;cbn [stemps];reflexivity. Qed.


Local Opaque fg_cf_store_state fg_cg_store_state.

Theorem exec_fg_iteration k rho beta e le m : (0<k<5)%nat ->
 rep rho beta fg_iter_regs m -> tmatch rho beta (fg_iter_temps k) le ->
 ematch beta (snd fg_alloc) e -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m fg_work E0 lef mf Out_normal /\
 rep rho beta (sregs (fg_iter_final_state k)) mf /\
 tmatch rho beta (stemps (fg_iter_final_state k)) lef /\
 lframe (fun b ofs=>~foot beta (map rshape fg_iter_regs) b ofs) m mf.
Proof.
 intros K Rep Temps Env.
 destruct (exec_fg_iter_prefix k rho beta e le m K Rep Temps Env)
  as (lp & mp & Prefix & RP & TP & FP).
 rewrite <-(fg_iter_prefix_outputs k K) in RP.
 destruct (fg_exec_done 100 (fg_iter_prefix_state k) fg_cf_low_call (fg_cf_call_state k)
  rho beta e lp mp (fg_cf_call_run_eq k K) RP TP Env)
  as (lc & mc & CFCall & RC & TC & FC).
 destruct (exec_fg_cf_low_store k rho beta e lc mc K RC TC Env)
  as (ms & CFStore & RS & FS).
 assert (TStore : tmatch rho beta (stemps (fg_cf_store_state k)) lc).
 { rewrite fg_cf_store_temps;exact TC. }
 pose proof (fg_exec_done 100 (fg_cf_store_state k) fg_cf_shift (fg_cf_shift_state k)
  rho beta e lc ms) as Shift.
 specialize (Shift (fg_cf_shift_run_eq k K)).
 destruct (Shift RS TStore Env)
  as (ls & mcs & CFShift & RCS & TCS & FCS).
 destruct (fg_exec_done 100 (fg_cf_shift_state k) fg_cg_low_call (fg_cg_call_state k)
  rho beta e ls mcs (fg_cg_call_run_eq k K) RCS TCS Env)
  as (lg & mg & CGCall & RG & TG & FG).
 destruct (exec_fg_cg_low_store k rho beta e lg mg K RG TG Env)
  as (mt & CGStore & RT & FT).
 assert (TGStore : tmatch rho beta (stemps (fg_cg_store_state k)) lg).
 { rewrite fg_cg_store_temps;exact TG. }
 destruct (fg_exec_done 100 (fg_cg_store_state k) fg_cg_shift (fg_iter_final_state k)
  rho beta e lg mt (fg_cg_shift_run_eq k K) RT TGStore Env)
  as (lef & mf & CGShift & RF & TF & FF).
 exists lef,mf;split.
 - rewrite fg_work_split;eapply exec_statement_prefix_then_last;[exact Prefix|].
   rewrite fg_iteration_suffix_source.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lc) (m1:=ms).
   + change fg_cf_chunk with (Ssequence fg_cf_low_call fg_cf_low_store).
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lc) (m1:=mc);[exact CFCall|exact CFStore].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=ls) (m1:=mcs);[exact CFShift|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lg) (m1:=mt).
     * change fg_cg_chunk with (Ssequence fg_cg_low_call fg_cg_low_store).
       eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lg) (m1:=mg);[exact CGCall|exact CGStore].
     * exact CGShift.
 - split;[exact RF|];split;[exact TF|].
   destruct (fg_iteration_shapes k K) as (SP & SC & SS & SCS & SG & ST).
   rewrite SP in FC;rewrite SC in FS;rewrite SS in FCS;
    rewrite SCS in FG;rewrite SG in FT;rewrite ST in FF.
   eapply lframe_trans;[exact FP|];eapply lframe_trans;[exact FC|];
    eapply lframe_trans;[exact FS|];eapply lframe_trans;[exact FCS|];
    eapply lframe_trans;[exact FG|];eapply lframe_trans;[exact FT|exact FF].
Qed.
