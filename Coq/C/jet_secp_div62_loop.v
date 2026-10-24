(** Enclosing production divstep loop and function, factored at the existing
    CTZ helper boundary. [CountCall] below is an explicit INTERNAL execution
    obligation, not an external model, axiom, or accepted public jet proof.
    In particular this file does not establish that the builtin counts bits. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clightdefs Clight
  ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.extraMath C.divstep C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_statement_prefix C.jet_secp_div62_count C.jet_secp_div62_consume
  C.jet_secp_div62_transition C.jet_secp_div62_entry C.jet_secp_div62_invariant
  C.jet_secp_div62_finish C.jet_secp_div62_exit.
Require Import C.jet_secp_closed_helpers C.jet_clight_internal_preserve C.jet_clight_internal_frame.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition div62_count_call := Scall (Some _t'1)
  (Evar _secp256k1_ctz64_var (Tfunction (Tcons tulong Tnil) tint cc_default))
  [div62_sentinel_expr].
Definition div62_counted_temps le z := PTree.set _zeros (Vint(Int.repr z))
  (PTree.set _t'1 (Vint(Int.repr z)) le).
Lemma div62_loop_source : div62_loop=Sloop div62_loop_body Sskip.
Proof. reflexivity. Qed.
Lemma div62_body_count_source : div62_loop_body=Ssequence Sskip
  (Ssequence (Ssequence div62_count_call div62_copy_count) div62_after_count).
Proof. reflexivity. Qed.
Lemma div62_ctz_linked : exists b,
  Genv.find_symbol secp_ge _secp256k1_ctz64_var=Some b /\
  Genv.find_funct_ptr secp_ge b=Some(Internal f_secp256k1_ctz64_var).
Proof. exists (secp_symbol_block _secp256k1_ctz64_var);split;reflexivity. Qed.
Local Opaque secp_ge.

Lemma div62_counted_lookup le z id : id<>_zeros -> id<>_t'1 ->
  (div62_counted_temps le z)!id=le!id.
Proof. intros Z T;unfold div62_counted_temps;rewrite !PTree.gso by congruence;reflexivity. Qed.
Lemma div62_counted_invariant start precision n pending b le z :
  div62_loop_invariant start precision n pending b le ->
  div62_loop_invariant start precision n pending b (div62_counted_temps le z).
Proof.
  unfold div62_loop_invariant,div62_pending_matrix,div62_pending_fg.
  intros (N & P & (u & v & MU & MV & U & V & Q & R) & (a & g0 & A & B & F & G) & Eta & Index & T).
  split;[exact N|];split;[exact P|];split.
  - exists u,v;rewrite !div62_counted_lookup by discriminate;repeat split;assumption.
  - split.
    + exists a,g0;rewrite !div62_counted_lookup by discriminate;repeat split;assumption.
    + rewrite !div62_counted_lookup by discriminate;repeat split;assumption.
Qed.
Lemma div62_counted_expected le z i :
  div62_expected_count (div62_counted_temps le z) i=div62_expected_count le i.
Proof. unfold div62_expected_count;rewrite div62_counted_lookup by discriminate;reflexivity. Qed.

Theorem exec_div62_count_call le m g i : 0<=i<=62 ->
  le!_g=Some(Vlong g) -> le!_i=Some(Vint(Int.repr i)) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ctz64_var)
    [Vlong(div62_sentinel_word g i)] E0 m (Vint(Int.repr(div62_sentinel_count g i))) ->
  Clight2.exec_stmt secp_ge empty_env le m (Ssequence div62_count_call div62_copy_count) E0
    (div62_counted_temps le (div62_sentinel_count g i)) m Out_normal.
Proof.
  intros I G Index CountCall;destruct div62_ctz_linked as (bf & Symbol & Function).
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _t'1 (Vint(Int.repr(div62_sentinel_count g i))) le).
  - unfold div62_count_call;eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
      (vargs:=[Vlong(div62_sentinel_word g i)]) (f:=Internal f_secp256k1_ctz64_var)
      (vres:=Vint(Int.repr(div62_sentinel_count g i))).
    + reflexivity.
    + eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact Symbol]|apply deref_loc_reference;reflexivity].
    + eapply eval_Econs;[eapply eval_div62_sentinel;eassumption|reflexivity|constructor].
    + exact Function.
    + reflexivity.
    + exact CountCall.
  - apply exec_div62_copy_count;apply PTree.gss.
Qed.

(** This section factors out a missing helper execution; closing the section
    generalizes [CountCall] into the statements. It is not discharged here. *)
Section COUNT_CALL_BOUNDARY.
Variable m : mem.
Hypothesis CountCall : forall x,Int64.unsigned x<>0 ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 m (Vint(Int.repr(Z_ctz(Int64.unsigned x)))).

Theorem exec_div62_body_invariant le start precision n pending b :
  62<=precision<=64 -> -683<=eta start<683 ->
  div62_loop_invariant start precision n pending b le -> exists lef out,
    Clight2.exec_stmt secp_ge empty_env le m div62_loop_body E0 lef m out /\
    ((out=Out_break /\ div62_loop_invariant start precision 62 0 b lef) \/
     (out=Out_normal /\ exists n2 p2,(n<n2)%nat /\ div62_loop_invariant start precision n2 p2 b lef)).
Proof.
  intros Precision Initial Inv.
  pose proof Inv as (N & P & Matrix & (a & g0 & A & B & F & G) & Eta & Index & T).
  set (i:=62-Z.of_nat n+pending) in *.
  assert (I:0<=i<=62) by (unfold i;apply Nat2Z.inj_le in N;lia).
  set (w:=Int64.repr(g0*2^pending)) in *.
  pose proof (exec_div62_count_call le m w i I G Index
    (CountCall (div62_sentinel_word w i) (div62_sentinel_nonzero w i I))) as Call.
  set (z:=div62_sentinel_count w i) in *.
  assert (Zeros:(div62_counted_temps le z)!_zeros=
    Some(Vint(Int.repr(div62_expected_count (div62_counted_temps le z) i)))).
  { rewrite div62_counted_expected;unfold div62_expected_count;rewrite G.
    unfold div62_counted_temps;apply PTree.gss. }
  destruct (exec_div62_postcount_invariant empty_env (div62_counted_temps le z) m
    start precision n pending b Precision Initial (div62_counted_invariant _ _ _ _ _ _ z Inv) Zeros)
    as (lef & out & Post & Result).
  exists lef,out;split;[|exact Result].
  rewrite div62_body_count_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0)
    (m1:=m) (le1:=le);[constructor|].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Call|exact Post].
Qed.

Theorem exec_div62_loop_fuel fuel : forall le start precision n pending b,
  (62-n<fuel)%nat -> 62<=precision<=64 -> -683<=eta start<683 ->
  div62_loop_invariant start precision n pending b le -> exists lef,
    Clight2.exec_stmt secp_ge empty_env le m div62_loop E0 lef m Out_normal /\
    div62_loop_invariant start precision 62 0 b lef.
Proof.
  induction fuel as [|fuel IH];intros le start precision n pending b Fuel Precision Initial Inv;
    [lia|].
  destruct (exec_div62_body_invariant le start precision n pending b Precision Initial Inv)
    as (le1 & out & Body & [(-> & Final)|(-> & n2 & p2 & Progress & Next)]).
  - exists le1;split;[|exact Final].
    rewrite div62_loop_source;eapply exec_Sloop_stop1;[exact Body|constructor].
  - pose proof (proj1 Inv) as N;pose proof (proj1 Next) as N2.
    destruct (IH le1 start precision n2 p2 b ltac:(lia) Precision Initial Next)
      as (lef & Repeat & Final).
    exists lef;split;[|exact Final].
    rewrite div62_loop_source in Repeat |- *.
    eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0)
      (m1:=m) (m2:=m) (le1:=le1) (le2:=le1) (out1:=Out_normal).
    + exact Body.
    + constructor.
    + constructor.
    + exact Repeat.
Qed.

Theorem exec_div62_loop_invariant le start precision n pending b :
  62<=precision<=64 -> -683<=eta start<683 ->
  div62_loop_invariant start precision n pending b le -> exists lef,
    Clight2.exec_stmt secp_ge empty_env le m div62_loop E0 lef m Out_normal /\
    div62_loop_invariant start precision 62 0 b lef.
Proof. intros; eapply (exec_div62_loop_fuel 63);[lia|eassumption|eassumption|eassumption]. Qed.

Theorem eval_div62_from_count_calls st precision f0 g0 b :
  62<=precision<=64 -> -683<=eta st<683 ->
  eqm (2^precision) (Int64.unsigned f0) (f st) ->
  eqm (2^precision) (Int64.unsigned g0) (g st) ->
  Mem.range_perm m b 0 32 Cur Freeable -> exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_modinv64_divsteps_62_var)
      [Vlong(Int64.repr(eta st));Vlong f0;Vlong g0;Vptr b Ptrofs.zero]
      E0 mf (Vlong(Int64.repr(eta(fst(stepN 62 st))))) /\
    (forall j,(j<4)%nat -> exists w,Mem.load Mint64 mf b (8*Z.of_nat j)=Some(Vlong w) /\
      Int64.signed w=div62_matrix_field (Trans.transN 62 st) j) /\
    (forall j,(j<4)%nat -> Mem.load Mint64 mf b (8*Z.of_nat j)=Some(Vlong(div62_exit_words st j))) /\
    Int64.signed(Int64.repr(eta(fst(stepN 62 st))))=eta(fst(stepN 62 st)) /\
    Mem.range_perm mf b 0 32 Cur Freeable /\ lframe(fun bx _=>bx<>b) m mf /\ readonly_preserved m mf.
Proof.
  intros Precision Initial F G Free.
  destruct (div62_entry_invariant m st precision f0 g0 b Precision F G)
    as (le0 & le1 & Entry & Init & Inv).
  destruct (exec_div62_loop_invariant le1 st precision 0 0 b Precision Initial Inv)
    as (le2 & Loop & Terminal).
  destruct (exec_div62_exit le2 m st precision b Initial Terminal Free)
    as (lef & mf & Finish & Loads & Eta & Owned & Frame).
  assert (ExactLoads:forall j,(j<4)%nat ->
    Mem.load Mint64 mf b (8*Z.of_nat j)=Some(Vlong(div62_exit_words st j))).
  { intros j J;destruct (Loads j J) as (w & Load & Signed).
    rewrite div62_exit_words_field by exact J;rewrite <- Signed,Int64.repr_signed;exact Load. }
  assert(Readonly:readonly_preserved m mf).
  { eapply secp_closed_stmt_preserved;[exact Finish|apply plain_empty|reflexivity]. }
  exists mf;split;[|split;[exact Loads|];split;[exact ExactLoads|];
    split;[exact Eta|];split;[exact Owned|];split;[exact Frame|exact Readonly]].
  eapply eval_funcall_internal with (e:=empty_env) (le1:=le0) (le2:=lef) (m1:=m) (m2:=mf)
    (out:=Out_return(Some(Vlong(Int64.repr(eta(fst(stepN 62 st)))),tlong))).
  - exact Entry.
  - rewrite div62_finish_source;eapply exec_statement_prefix_then_last;[exact Init|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Loop|exact Finish].
  - split;[discriminate|reflexivity].
  - reflexivity.
Qed.
End COUNT_CALL_BOUNDARY.
