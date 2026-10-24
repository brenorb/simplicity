(** Exact original prefix through the two correction-word assignments. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_known C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix.
Require Import C.jet_secp_modinv_de_exec C.jet_secp_modinv_fg_iteration_prefix C.jet_secp_modinv_fg_prefix.
Require Import C.jet_secp_modinv_fg_prefix_numeric C.jet_secp_modinfo_fe_global.
Require Import C.jet_secp_modinv_normalize62_exec C.jet_secp_modinv_fg_iteration_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition de62_alloc := Eval vm_compute in
 match xalloc (std_cells (genv_cenv secp_ge)) (genv_cenv secp_ge)
 (fn_vars f_secp256k1_modinv64_update_de_62) 4 with Some p=>p | None=>([],[]) end.
Definition de62_temps := PTree.set _modinfo (XP 3 0) (PTree.set _t (XP 2 0)
 (PTree.set _e (XP 1 0) (PTree.set _d (XP 0 0) (PTree.empty sx)))).
Definition de62_initial := mkst de62_temps (de62_regs++fst de62_alloc) [] 14.
Definition de62_source_parts := split_statement_last (fn_body f_secp256k1_modinv64_update_de_62).
Definition de62_correction_prefix := statement_sequence (firstn 25 (fst de62_source_parts)) Sskip.
Definition de62_after_correction := statement_sequence (skipn 25 (fst de62_source_parts)) (snd de62_source_parts).
Definition de62_correction_run := known_stmt (genv_cenv secp_ge) [] fg_fast_table 400
 (snd de62_alloc) de62_initial de62_correction_prefix.
Definition de62_correction_state := match de62_correction_run with
 | Some (RDone st _)=>st | _=>de62_initial end.
Definition de62_correction_ok := match de62_correction_run with Some (RDone _ ONormal)=>true | _=>false end.
Lemma de62_correction_complete : de62_correction_ok=true.
Proof. vm_compute;reflexivity. Qed.
Lemma de62_correction_run_eq : de62_correction_run=Some (RDone de62_correction_state ONormal).
Proof.
 pose proof de62_correction_complete as Run;unfold de62_correction_ok,de62_correction_state in *.
 destruct de62_correction_run as [r|];[|discriminate];destruct r;
 [destruct o;try discriminate;reflexivity|discriminate].
Qed.
Lemma de62_correction_source : fn_body f_secp256k1_modinv64_update_de_62=
 statement_sequence (firstn 25 (fst de62_source_parts)) de62_after_correction.
Proof. reflexivity. Qed.

Definition de62_multiple_sx (high : bool) := XLb Badd
 (XLb Band (XLv (if high then 12 else 10)) (XLsh Hshr (XLv 4) 63))
 (XLb Band (XLv (if high then 13 else 11)) (XLsh Hshr (XLv 9) 63)).
Definition de62_correction_sx high := XLb Bsub (de62_multiple_sx high)
 (XLb Band (XLb Badd (XLb Bmul (XLc (Int64.repr 2866531139136965327))
  (fg_row_lo (XLv (if high then 12 else 10)) (XLv (if high then 13 else 11))))
  (de62_multiple_sx high)) norm62_mask).
Lemma de62_correction_temps (high : bool) : (stemps de62_correction_state)!(if high then _me else _md)=
 Some (de62_correction_sx high).
Proof. destruct high;vm_compute;reflexivity. Qed.

Definition de62_multiple_word (rho : nat->int64) (high : bool) := Int64.add
 (Int64.and (rho (if high then 12%nat else 10%nat)) (Int64.shr (rho 4%nat) (Int64.repr 63)))
 (Int64.and (rho (if high then 13%nat else 11%nat)) (Int64.shr (rho 9%nat) (Int64.repr 63))).
Definition de62_correction_word (rho : nat->int64) (high : bool) :=
 Int64.sub (de62_multiple_word rho high)
 (Int64.and (Int64.add (Int64.mul (Int64.repr 2866531139136965327)
  (fg_row_low rho (if high then 12%nat else 10%nat) (if high then 13%nat else 11%nat)))
  (de62_multiple_word rho high)) (Int64.repr (2^62-1))).
Lemma de62_correction_den rho beta high : den rho beta (de62_correction_sx high)=Vlong (de62_correction_word rho high).
Proof. destruct high;reflexivity. Qed.

Local Opaque known_stmt de62_correction_state de62_initial de62_correction_prefix secp_ge fg_fast_table.
Theorem exec_de62_correction_prefix rho beta e le m :
 rep rho beta (sregs de62_initial) m -> tmatch rho beta (stemps de62_initial) le ->
 ematch beta (snd de62_alloc) e -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m de62_correction_prefix E0 lef mf Out_normal /\
 lef!_md=Some (Vlong (de62_correction_word rho false)) /\
 lef!_me=Some (Vlong (de62_correction_word rho true)) /\
 rep rho beta (sregs de62_correction_state) mf /\ tmatch rho beta (stemps de62_correction_state) lef /\
 lframe (fun b ofs=>~foot beta (map rshape (sregs de62_initial)) b ofs) m mf.
Proof.
 intros Rep Temps Env.
 pose proof (known_stmt_sound secp_ge [] fg_fast_table (fun _ _=>True) (fun _ _ _=>True) (fun _=>False)
  ltac:(auto) ltac:(intros;contradiction) fg_fast_table_correct 400) as Sound.
 specialize (Sound (snd de62_alloc) de62_initial de62_correction_prefix
  (RDone de62_correction_state ONormal) de62_correction_run_eq rho beta e le m Rep Temps Env).
 destruct Sound as (lef & mf & out & Exec & Post).
 - split;intros;discriminate.
 - intros r _ [].
 - exact I.
 - apply Forall_forall;intros;exact I.
 - destruct Post as (Out & Match & Normal & Shape & Inv & Frame).
   cbn [rsel fst snd] in Out,Match,Normal;destruct out;cbn [outmatch] in Normal;try contradiction.
   exists lef,mf;split;[exact Exec|];split.
   + pose proof (Match _ _ (de62_correction_temps false)) as MD;rewrite de62_correction_den in MD;exact MD.
   + split.
     * pose proof (Match _ _ (de62_correction_temps true)) as ME;rewrite de62_correction_den in ME;exact ME.
     * split;[exact Out|];split;[exact Match|];eapply lframe_implies;[exact Frame|];
       intros b ofs Outside Valid;split;[exact Valid|];split;[exact Outside|tauto].
Qed.
