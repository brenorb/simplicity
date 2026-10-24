(** The original divstep helper's four matrix stores and eta return.
    These stores use Clight directly, with no external-call premise. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_div62_count C.jet_secp_statement_prefix.
Require Import C.jet_secp_local_regions C.jet_secp_b32_exec.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition div62_finish := statement_sequence (skipn 8 (fst div62_parts)) (snd div62_parts).
Lemma div62_finish_source : fn_body f_secp256k1_modinv64_divsteps_62_var =
  statement_sequence (firstn 7 (fst div62_parts)) (Ssequence div62_loop div62_finish).
Proof. reflexivity. Qed.
Definition div62_finish_regs := [mkreg
  [mkcell 0 Mint64 None;mkcell 8 Mint64 None;mkcell 16 Mint64 None;mkcell 24 Mint64 None] true (Some 32)].
Definition div62_finish_temps := PTree.set _t (XP 0 0)
  (PTree.set _eta (XLv 4) (PTree.set _r (XLv 3) (PTree.set _q (XLv 2)
    (PTree.set _v (XLv 1) (PTree.set _u (XLv 0) (PTree.empty sx)))))).
Definition div62_finish_start := mkst div62_finish_temps div62_finish_regs [] 5.
Definition div62_finish_run := xstmt (genv_cenv secp_ge) [] [] 80 [] div62_finish_start div62_finish.
Definition div62_finish_state := match div62_finish_run with Some(RDone st _)=>st | _=>div62_finish_start end.
Lemma div62_finish_run_eq : div62_finish_run=Some(RDone div62_finish_state (OReturn (Some(XLv 4,tlong)))).
Proof. reflexivity. Qed.
Lemma div62_finish_out : sregs div62_finish_state=[mkreg (u64_cells 0 [XLv 0;XLv 1;XLv 2;XLv 3]) true (Some 32)].
Proof. reflexivity. Qed.
Lemma div62_finish_log : slog div62_finish_state=[].
Proof. reflexivity. Qed.

Lemma div62_finish_initial rho m b : Mem.range_perm m b 0 32 Cur Freeable ->
  rep rho [(b,0)] div62_finish_regs m.
Proof.
  intro Free;apply (rep_add _ [] [] m b 0);[apply rep_nil|cbn;tauto|].
  unfold region_ok;cbn [rcells rw rfree bas blk lay nth fst snd div62_finish_regs hd app length].
  split;[lia|];split;[eapply Mem.perm_valid_block;apply (Free 0);lia|].
  split;[reflexivity|];split.
  - apply Forall_forall;intros c Member;cbn [In] in Member;
      destruct Member as [Eq|[Eq|[Eq|[Eq|Nil]]]];try contradiction;subst c;
      apply writable_undefined_cell;cbn [bas blk lay nth fst snd size_chunk align_chunk];
      try (change Ptrofs.max_unsigned with 18446744073709551615;lia);
      try (apply freeable_range_writable;intros pos HP;apply Free;lia).
    all: match goal with |- (8|?k)=>exists (k/8);reflexivity end.
  - split;[reflexivity|];split;[reflexivity|];split;[exact Free|];repeat constructor;cbn;lia.
Qed.

Local Opaque xstmt div62_finish_state.
Theorem exec_div62_finish rho le m b :
  le!_t=Some(Vptr b Ptrofs.zero) -> le!_u=Some(Vlong(rho 0%nat)) ->
  le!_v=Some(Vlong(rho 1%nat)) -> le!_q=Some(Vlong(rho 2%nat)) ->
  le!_r=Some(Vlong(rho 3%nat)) -> le!_eta=Some(Vlong(rho 4%nat)) ->
  Mem.range_perm m b 0 32 Cur Freeable -> exists lef mf,
  Clight2.exec_stmt secp_ge empty_env le m div62_finish E0 lef mf (Out_return (Some(Vlong(rho 4%nat),tlong))) /\
  (forall j,(j<4)%nat -> Mem.load Mint64 mf b (8*Z.of_nat j)=Some(Vlong(rho j))) /\
  Mem.range_perm mf b 0 32 Cur Freeable /\ lframe (fun bx _=>bx<>b) m mf.
Proof.
  intros T U V Q R Eta Free.
  assert (Temps : tmatch rho [(b,0)] div62_finish_temps le).
  { intros id x Lookup;unfold div62_finish_temps in Lookup.
    repeat rewrite PTree.gsspec in Lookup;
      repeat match type of Lookup with context[if ?D then _ else _]=>destruct D end;
      try (rewrite PTree.gempty in Lookup;discriminate);try discriminate;injection Lookup as <-;
      subst id;assumption. }
  assert (Env : ematch [(b,0)] [] empty_env).
  { intro id;split;[apply PTree.gempty|intros r ty Bad;discriminate]. }
  destruct (xstmt_sound secp_ge [] [] (fun _ _=>True) (fun _ _ _=>True) (fun _=>False)
    ltac:(auto) ltac:(intros;contradiction) ltac:(intros id ent Lookup;discriminate Lookup) 80
    [] div62_finish_start div62_finish (RDone div62_finish_state (OReturn (Some(XLv 4,tlong))))
    div62_finish_run_eq rho [(b,0)] empty_env le m (div62_finish_initial rho m b Free) Temps Env)
    as (lef & mf & out & Exec & Post).
  - split;intros;discriminate.
  - intros r _ Bad;exact Bad.
  - exact I.
  - change (Forall (fun _=>True) (slog div62_finish_state));rewrite div62_finish_log;constructor.
  - destruct Post as (Rep & Match & Outcome & Shape & Inv & Frame).
    cbn [rsel fst snd outmatch] in Rep,Outcome.
    destruct out as [| | |[[value ty]|]];try contradiction.
    destruct Outcome as [-> ->].
    rewrite div62_finish_out in Rep.
    pose proof (rep_region _ _ _ _ 0 _ Rep eq_refl) as Region.
    pose proof Region as (_ & _ & _ & _ & _ & _ & Owned & _).
    exists lef,mf;split;[exact Exec|];split.
    + intros j J.
      pose proof (region_load _ _ _ _ _ (8*Z.of_nat j) Mint64 (XLv j) Region
        ltac:(replace (8*Z.of_nat j) with (0+8*Z.of_nat j) by lia;apply u64_cells_nth;
          destruct j as [|[|[|[|j]]]];try lia;reflexivity)) as Load.
      exact Load.
    + split;[exact Owned|].
      eapply lframe_implies;[exact Frame|].
      intros bx pos Outside Valid;split;[exact Valid|];split;[|intros Bad;exact Bad].
      intros (r & sh & ofs & ch & Nth & Cell & Block & Range).
      destruct r;[apply Outside;exact Block|destruct r;discriminate Nth].
Qed.

Definition div62_exit_words u v q r eta i (n : nat) :=
  nth n [Int64.shl u (Int64.repr i);Int64.shl v (Int64.repr i);q;r;Int64.repr (eta-i)] Int64.zero.

Theorem exec_div62_count_exit le m b g u v q r eta i : 0<=i<=62 ->
  le!_t=Some(Vptr b Ptrofs.zero) -> le!_g=Some(Vlong g) ->
  le!_u=Some(Vlong u) -> le!_v=Some(Vlong v) -> le!_q=Some(Vlong q) -> le!_r=Some(Vlong r) ->
  le!_eta=Some(Vlong (Int64.repr eta)) -> le!_i=Some(Vint (Int.repr i)) ->
  le!_zeros=Some(Vint (Int.repr i)) -> Mem.range_perm m b 0 32 Cur Freeable -> exists lef mf,
  Clight2.exec_stmt secp_ge empty_env le m div62_after_count E0
    (div62_count_temps le g u v eta i i) m Out_break /\
  Clight2.exec_stmt secp_ge empty_env (div62_count_temps le g u v eta i i) m div62_finish E0 lef mf
    (Out_return (Some(Vlong (Int64.repr (eta-i)),tlong))) /\
  (forall j,(j<4)%nat -> Mem.load Mint64 mf b (8*Z.of_nat j)=Some(Vlong (div62_exit_words u v q r eta i j))) /\
  Mem.range_perm mf b 0 32 Cur Freeable /\ lframe (fun bx _=>bx<>b) m mf.
Proof.
  intros Range T G U V Q R Eta Index Zeros Free.
  pose proof (exec_div62_count_prefix empty_env le m g u v eta i i ltac:(lia)
    ltac:(lia) G U V Eta Index Zeros) as Count.
  unfold div62_count_outcome in Count;rewrite Z.eqb_refl in Count.
  assert (After : Clight2.exec_stmt secp_ge empty_env le m div62_after_count E0
    (div62_count_temps le g u v eta i i) m Out_break).
  { rewrite div62_count_source;eapply exec_statement_prefix_aborts;[discriminate|exact Count]. }
  destruct (exec_div62_finish (div62_exit_words u v q r eta i)
    (div62_count_temps le g u v eta i i) m b
    ltac:(unfold div62_count_temps;rewrite !PTree.gso by discriminate;exact T)
    ltac:(unfold div62_count_temps;rewrite !PTree.gso by discriminate;apply PTree.gss)
    ltac:(unfold div62_count_temps;rewrite !PTree.gso by discriminate;apply PTree.gss)
    ltac:(unfold div62_count_temps;rewrite !PTree.gso by discriminate;exact Q)
    ltac:(unfold div62_count_temps;rewrite !PTree.gso by discriminate;exact R)
    ltac:(unfold div62_count_temps;rewrite PTree.gso by discriminate;apply PTree.gss) Free)
    as (lef & mf & Finish & Words & Owned & Frame).
  exists lef,mf;repeat first [assumption|split].
Qed.
