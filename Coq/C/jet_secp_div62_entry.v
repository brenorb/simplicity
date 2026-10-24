(** Actual function entry and initial loop representations for divsteps_62_var. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.divstep C.jet_secp_statement_prefix
  C.jet_secp_div62_count C.jet_secp_div62_transition.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition div62_initializers := statement_sequence (firstn 7 (fst div62_parts)) Sskip.
Definition div62_initial_temps le f0 g0 :=
  PTree.set _i (Vint(Int.repr 62)) (PTree.set _g (Vlong g0) (PTree.set _f (Vlong f0)
    (PTree.set _r (Vlong Int64.one) (PTree.set _q (Vlong Int64.zero)
      (PTree.set _v (Vlong Int64.zero) (PTree.set _u (Vlong Int64.one) le)))))).
Definition div62_entry_temps eta f0 g0 b :=
  PTree.set _t (Vptr b Ptrofs.zero) (PTree.set _g0 (Vlong g0) (PTree.set _f0 (Vlong f0)
    (PTree.set _eta (Vlong eta) (create_undef_temps (fn_temps f_secp256k1_modinv64_divsteps_62_var))))).

Lemma div62_initializers_source : div62_initializers=
  Ssequence (Sset _u (Ecast (Econst_int Int.one tint) tulong))
  (Ssequence (Sset _v (Ecast (Econst_int Int.zero tint) tulong))
  (Ssequence (Sset _q (Ecast (Econst_int Int.zero tint) tulong))
  (Ssequence (Sset _r (Ecast (Econst_int Int.one tint) tulong))
  (Ssequence (Sset _f (Etempvar _f0 tulong))
  (Ssequence (Sset _g (Etempvar _g0 tulong))
  (Ssequence (Sset _i (Econst_int (Int.repr 62) tint)) Sskip)))))).
Proof. reflexivity. Qed.

Local Ltac entry_lookup := first [eassumption|apply PTree.gss|rewrite PTree.gso by discriminate;entry_lookup].
Local Ltac entry_expr := first [apply eval_Etempvar;entry_lookup|apply eval_Econst_int|apply eval_Econst_long|
  eapply eval_Ecast;[entry_expr|reflexivity]].

Theorem exec_div62_initializers e le m f0 g0 : le!_f0=Some(Vlong f0) -> le!_g0=Some(Vlong g0) ->
  Clight2.exec_stmt secp_ge e le m div62_initializers E0 (div62_initial_temps le f0 g0) m Out_normal.
Proof.
  intros F G;rewrite div62_initializers_source;unfold div62_initial_temps.
  repeat (eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m);[apply exec_Sset;entry_expr|]).
  constructor.
Qed.

Lemma div62_initial_temps_outside le f0 g0 id : ~In id [_u;_v;_q;_r;_f;_g;_i] ->
  (div62_initial_temps le f0 g0)!id=le!id.
Proof.
  intro Outside;unfold div62_initial_temps;rewrite !PTree.gso;[reflexivity| | | | | | | ];
    intro Eq;subst id;apply Outside;cbn [In];tauto.
Qed.

Lemma div62_function_entry m eta f0 g0 b :
  function_entry2 secp_ge f_secp256k1_modinv64_divsteps_62_var
    [Vlong eta;Vlong f0;Vlong g0;Vptr b Ptrofs.zero] m empty_env (div62_entry_temps eta f0 g0 b) m.
Proof.
  assert (OK : fn_okb f_secp256k1_modinv64_divsteps_62_var=true) by reflexivity.
  destruct (fn_okb_true _ OK) as (N1 & N2 & Disjoint).
  constructor;[exact N1|exact N2|exact Disjoint|constructor|reflexivity].
Qed.

Theorem div62_entry_to_loop m st precision f0 g0 b :
  62<=precision<=64 ->
  eqm (2^precision) (Int64.unsigned f0) (f st) ->
  eqm (2^precision) (Int64.unsigned g0) (g st) ->
  exists le0 le1,
    function_entry2 secp_ge f_secp256k1_modinv64_divsteps_62_var
      [Vlong(Int64.repr(eta st));Vlong f0;Vlong g0;Vptr b Ptrofs.zero] m empty_env le0 m /\
    Clight2.exec_stmt secp_ge empty_env le0 m div62_initializers E0 le1 m Out_normal /\
    div62_pending_matrix le1 Trans.I 0 /\ div62_pending_fg le1 st precision 0 /\
    le1!_eta=Some(Vlong(Int64.repr(eta st))) /\ le1!_i=Some(Vint(Int.repr 62)) /\
    le1!_t=Some(Vptr b Ptrofs.zero).
Proof.
  intros Precision F G.
  set (le0:=div62_entry_temps (Int64.repr(eta st)) f0 g0 b).
  set (le1:=div62_initial_temps le0 f0 g0).
  exists le0,le1;split;[apply div62_function_entry|];split.
  - unfold le1;apply exec_div62_initializers;unfold le0,div62_entry_temps;entry_lookup.
  - split.
    + unfold div62_pending_matrix;exists 1,0;repeat apply conj;try reflexivity.
      all: unfold le1,div62_initial_temps;entry_lookup.
    + split.
      * unfold div62_pending_fg;exists (Int64.unsigned f0),(Int64.unsigned g0).
        split;[exact F|];split;[exact G|];split.
        -- rewrite Int64.repr_unsigned;unfold le1,div62_initial_temps;entry_lookup.
        -- rewrite Z.pow_0_r,Z.mul_1_r,Int64.repr_unsigned;unfold le1,div62_initial_temps;entry_lookup.
      * split.
        -- unfold le1;rewrite div62_initial_temps_outside by (cbn [In];intuition discriminate).
           unfold le0,div62_entry_temps;entry_lookup.
        -- split.
           ++ unfold le1,div62_initial_temps;apply PTree.gss.
           ++ unfold le1;rewrite div62_initial_temps_outside by (cbn [In];intuition discriminate).
              unfold le0,div62_entry_temps;apply PTree.gss.
Qed.
