(** The local replacement theorem applies to every context and input.

    [jet_context] replaces a jet's Bit Machine translation by the generated C
    function, from any memory representing the pre-state.  With
    [bm_rep_constructible], such a memory exists for every context and input
    whose state fits the address space, and can be built in two fresh blocks
    on top of any memory.  So for each jet proved against [jet_local_spec]
    with a parametric specification: for all contexts and inputs, the C
    function runs on a representation of the Bit Machine pre-state and ends
    in a representation of exactly the state the Bit Machine reaches. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.BitMachine Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_context_separated.
Require Import C.jet_frame_constructible_bm.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Theorem jet_context_executable {A B : Ty} (f : function)
    (t : forall {alg : Alg.Core.Algebra}, Alg.Core.domain alg A B) :
  Alg.Core.Parametric (@t) ->
  jet_local_spec f A B (fun a => @t Alg.CoreFunSem a) ->
  (1 <= bitSize B)%nat ->
  forall (env : val) (ctx : Context) (a : A) (m0 : mem),
  let s0 := fillContext ctx
    {| readLocalState := encode a; writeLocalState := newWriteFrame (bitSize B) |} in
  let s1 := fillContext ctx
    {| readLocalState := encode a;
       writeLocalState := fullWriteFrame (encode (@t Alg.CoreFunSem a)) |} in
  bm_state_fits s0 ->
  exists m L mf,
    bm_rep m L s0 /\
    (forall b, Mem.valid_block m0 b ->
      forall chunk ofs, Mem.load chunk m b ofs = Mem.load chunk m0 b ofs) /\
    Clight2.eval_funcall ge0 m (Internal f) (jet_args env L) E0 mf (Vint Int.one) /\
    bm_rep mf L s1 /\
    (s0 >>- @t Naive.translate ->> s1).
Proof.
  intros Ht HSpec HB env ctx a m0 s0 s1 HFits.
  destruct (bm_rep_constructible s0 m0 HFits)
    as (m & L & HRep & HSep & HWritable & _ & _ & HOld).
  destruct (jet_context f (@t) Ht HSpec HB env m L ctx a HRep HSep HWritable)
    as (mf & HCall & HFinal & HRun).
  exists m, L, mf.
  split; [exact HRep|]. split; [intros b Hb; exact (proj2 (HOld b Hb))|].
  split; [exact HCall|]. split; [exact HFinal|exact HRun].
Qed.

(** The same for jets proved against the separated (copy) contract. *)
Theorem jet_context_separated_executable {A B : Ty} (f : function)
    (t : forall {alg : Alg.Core.Algebra}, Alg.Core.domain alg A B) :
  Alg.Core.Parametric (@t) ->
  jet_separated_local_spec f A B (fun a => @t Alg.CoreFunSem a) ->
  (1 <= bitSize B)%nat ->
  forall (env : val) (ctx : Context) (a : A) (m0 : mem),
  let s0 := fillContext ctx
    {| readLocalState := encode a; writeLocalState := newWriteFrame (bitSize B) |} in
  let s1 := fillContext ctx
    {| readLocalState := encode a;
       writeLocalState := fullWriteFrame (encode (@t Alg.CoreFunSem a)) |} in
  bm_state_fits s0 ->
  exists m L mf,
    bm_rep m L s0 /\
    (forall b, Mem.valid_block m0 b ->
      forall chunk ofs, Mem.load chunk m b ofs = Mem.load chunk m0 b ofs) /\
    Clight2.eval_funcall ge0 m (Internal f) (jet_args env L) E0 mf (Vint Int.one) /\
    bm_rep mf L s1 /\
    (s0 >>- @t Naive.translate ->> s1).
Proof.
  intros Ht HSpec HB env ctx a m0 s0 s1 HFits.
  destruct (bm_rep_constructible s0 m0 HFits)
    as (m & L & HRep & HSep & HWritable & _ & _ & HOld).
  destruct (jet_context_separated f (@t) Ht HSpec HB env m L ctx a HRep HSep HWritable)
    as (mf & HCall & HFinal & HRun).
  exists m, L, mf.
  split; [exact HRep|]. split; [intros b Hb; exact (proj2 (HOld b Hb))|].
  split; [exact HCall|]. split; [exact HFinal|exact HRun].
Qed.
