(** Original inverse-loop arithmetic prefix at every valid nonzero limb
    index. Both operand loads and all four actual signed accumulations are
    executed. Masked stores, shifts and full-loop composition remain separate. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values Globalenvs.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_pure C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_statement_prefix.
Require Import C.jet_secp_modinv_fg_prefix C.jet_secp_i128_mul_exec.
Require Import C.jet_sx_void_oracle C.jet_secp_modinv_fg_index.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fg_fast_table := (_secp256k1_i128_accum_mul,
 FOra f_secp256k1_i128_accum_mul (pure_void_oracle secp_ge smul128_functions 300 f_secp256k1_i128_accum_mul))::fg_table.
Definition fg_iter_regs := fg_regs++
 [mkreg (u64_cells 0 [XLv 15;XLv 16]) true (Some 16);
  mkreg (u64_cells 0 [XLv 17;XLv 18]) true (Some 16)].
Definition fg_iter_temps k := PTree.set _i (XIc (Int.repr (Z.of_nat k)))
 (PTree.set _M62 (XLsh Hshru (XLc (Int64.repr (-1))) 2)
 (PTree.set _r (XLv 13) (PTree.set _q (XLv 12)
 (PTree.set _v (XLv 11) (PTree.set _u (XLv 10) fg_temps))))).
Definition fg_iter_initial k := mkst (fg_iter_temps k) fg_iter_regs [] 19.
Definition fg_work_parts := split_statement_last fg_work.
Definition fg_work_prefix := statement_sequence (firstn 6 (fst fg_work_parts)) Sskip.
Definition fg_iter_prefix_run k := xstmt (genv_cenv secp_ge) [] fg_fast_table 500 (snd fg_alloc)
 (fg_iter_initial k) fg_work_prefix.
Definition fg_iter_prefix_state k := match fg_iter_prefix_run k with
 | Some (RDone st _)=>st | _=>fg_iter_initial k end.
Lemma fg_iter_prefix_run_eq k : (0<k<5)%nat ->
 fg_iter_prefix_run k=Some (RDone (fg_iter_prefix_state k) ONormal).
Proof.
 destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity.
Qed.
Definition fg_iter_accum (pair : sx*sx) a b :=
 let low:=XLb Badd (fst pair) (fg_product_lo a b) in
 (low,XLb Badd (snd pair) (XLb Badd (fg_product_hi a b)
  (XI2L Signed (XLcmp Clt Unsigned low (fg_product_lo a b))))).
Definition fg_iter_cf k := fg_iter_accum
 (fg_iter_accum (XLv 15,XLv 16) (XLv 10) (XLv k)) (XLv 11) (XLv (5+k)).
Definition fg_iter_cg k := fg_iter_accum
 (fg_iter_accum (XLv 17,XLv 18) (XLv 12) (XLv k)) (XLv 13) (XLv (5+k)).
Definition fg_iter_prefix_out k := fg_regs++
 [mkreg (u64_cells 0 [fst (fg_iter_cf k);snd (fg_iter_cf k)]) true (Some 16);
  mkreg (u64_cells 0 [fst (fg_iter_cg k);snd (fg_iter_cg k)]) true (Some 16)].
Lemma fg_iter_prefix_outputs k : (0<k<5)%nat ->
 sregs (fg_iter_prefix_state k)=fg_iter_prefix_out k.
Proof. destruct k as [|[|[|[|[|k]]]]];intro Bound;try lia;vm_compute;reflexivity. Qed.
Definition fg_work_suffix := statement_sequence (skipn 6 (fst fg_work_parts)) (snd fg_work_parts).
Lemma fg_work_split : fg_work=statement_sequence (firstn 6 (fst fg_work_parts)) fg_work_suffix.
Proof. reflexivity. Qed.
Lemma fg_fast_table_correct id ent : flookup fg_fast_table id=Some ent ->
 (exists b,Genv.find_symbol secp_ge id=Some b /\
 Genv.find_funct_ptr secp_ge b=Some (Internal (fentry_fd ent))) /\
 match ent with FInt _=>True | FOra fd o=>
 oracle_ok secp_ge (fun _ _=>True) (fun _ _ _=>True) (fun _=>False) fd o end.
Proof.
 unfold fg_fast_table;cbn [flookup].
 destruct (Pos.eqb _secp256k1_i128_accum_mul id) eqn:E.
 - apply Pos.eqb_eq in E;subst id;intro H;inversion H;subst ent;split.
   + apply secp_pure_ok;unfold secp_pure;repeat first [left;reflexivity|right].
   + apply pure_void_oracle_correct;exact smul128_functions_ok.
 - apply fg_table_correct.
Qed.

Local Opaque xstmt fg_iter_prefix_state fg_iter_initial fg_fast_table fg_work_prefix fg_alloc secp_ge.
Lemma fg_iter_sound fuel : sound_rec secp_ge [] (fun _ _=>True) (fun _ _ _=>True) (fun _=>False)
 (xstmt (genv_cenv secp_ge) [] fg_fast_table fuel).
Proof. apply xstmt_sound;[intros;exact I|intros;contradiction|exact fg_fast_table_correct]. Qed.
Theorem exec_fg_iter_prefix k rho beta e le m : (0<k<5)%nat ->
 rep rho beta fg_iter_regs m -> tmatch rho beta (fg_iter_temps k) le ->
 ematch beta (snd fg_alloc) e -> exists le' mf,
 Clight2.exec_stmt secp_ge e le m fg_work_prefix E0 le' mf Out_normal /\
 rep rho beta (fg_iter_prefix_out k) mf /\
 tmatch rho beta (stemps (fg_iter_prefix_state k)) le' /\
 lframe (fun b ofs=>~foot beta (map rshape fg_iter_regs) b ofs) m mf.
Proof.
 intros K Rep Temps Env.
 pose proof (fg_iter_sound 500) as Sound.
 specialize (Sound (snd fg_alloc) (fg_iter_initial k) fg_work_prefix
  (RDone (fg_iter_prefix_state k) ONormal) (fg_iter_prefix_run_eq k K)).
 destruct (Sound rho beta e le m Rep Temps Env) as (le' & mf & out & Exec & Post).
 - split;intros;discriminate.
 - intros r _ [].
 - exact I.
 - apply Forall_forall;intros;exact I.
 - destruct Post as (Out & Match & Normal & Shape & Inv & Frame).
   cbn [rsel fst snd] in Out,Match,Normal;destruct out;cbn [outmatch] in Normal;try contradiction.
   rewrite fg_iter_prefix_outputs in Out by exact K.
   exists le',mf;split;[exact Exec|];split;[exact Out|];split;[exact Match|].
   eapply lframe_implies;[exact Frame|];intros b ofs Outside Valid;
    split;[exact Valid|];split;[exact Outside|tauto].
Qed.
