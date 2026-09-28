(** Execution guarantees for the generated jets at the call boundary.

    A public jet theorem produces a terminating, silent big-step call.
    [jet_local_spec_guarantees] and [jet_context_guarantees] combine it with
    [eval_funcall_silent_guarantees]: for every call continuation that is a
    call continuation, every small-step execution from the call state follows
    the same silent path until the call returns, is never stuck or forked
    before the return, and any infinite execution from the call state is that
    silent path followed by an infinite execution of the caller.  Uniqueness
    is among terminating executions; only the top-level statement
    ([Kstop]) also excludes divergence.  Nothing here concerns the caller's
    execution after the return, and no determinism axiom is used. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Import Simplicity.Ty Simplicity.BitMachine Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_clight_determinism.
Require Import C.jet_canonical.
Import ListNotations.
Local Open Scope Z_scope.

Theorem jet_local_spec_guarantees (f : function) (A B : Ty) (spec : A -> B) :
  jet_local_spec f A B spec ->
  forall m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A),
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    exists mf,
      silent_call_guarantees (Clight.globalenv prog) (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); Vundef]
        m (Vint Int.one) mf /\
      frame_output_cells_at mf bw outedge cursor (encode (spec a)).
Proof.
  intros Hspec m bd dbase bs sbase bi bw edge outedge cursor rc a HB HA HF H0 Hmax Hin Hout.
  destruct (Hspec m bd dbase bs sbase bi bw edge outedge cursor rc a
    HB HA HF H0 Hmax Hin Hout) as (mf & Hcall & Hobs & _).
  exists mf. split; [|exact Hobs].
  exact (eval_funcall_silent_guarantees prog m (Internal f) _ mf _ Hcall).
Qed.

Theorem jet_context_guarantees {A B : Ty} (f : function)
    (t : forall {alg : Alg.Core.Algebra}, Alg.Core.domain alg A B) :
  Alg.Core.Parametric (@t) ->
  jet_local_spec f A B (fun a => @t Alg.CoreFunSem a) ->
  (1 <= bitSize B)%nat ->
  forall m L (ctx : Context) (a : A),
  let s0 := fillContext ctx
    {| readLocalState := encode a; writeLocalState := newWriteFrame (bitSize B) |} in
  let s1 := fillContext ctx
    {| readLocalState := encode a;
       writeLocalState := fullWriteFrame (encode (@t Alg.CoreFunSem a)) |} in
  bm_rep m L s0 -> bm_separated L s0 -> active_write_writable m L s0 ->
  exists mf,
    silent_call_guarantees (Clight.globalenv prog) (Internal f) (jet_args L)
      m (Vint Int.one) mf /\
    bm_rep mf L s1 /\ (s0 >>- @t Naive.translate ->> s1).
Proof.
  intros Ht Hspec HB m L ctx a s0 s1 Hrep Hsep Hwr.
  destruct (jet_context f t Ht Hspec HB m L ctx a Hrep Hsep Hwr)
    as (mf & Hcall & Hrep' & Htr).
  exists mf. split; [|exact (conj Hrep' Htr)].
  exact (eval_funcall_silent_guarantees prog m (Internal f) _ mf _ Hcall).
Qed.

(** * The twelve jets *)

Definition one8_guarantees := jet_local_spec_guarantees _ _ _ _ one8_local_spec.
Definition one16_guarantees := jet_local_spec_guarantees _ _ _ _ one16_local_spec.
Definition one32_guarantees := jet_local_spec_guarantees _ _ _ _ one32_local_spec.
Definition one64_guarantees := jet_local_spec_guarantees _ _ _ _ one64_local_spec.
Definition increment8_guarantees := jet_local_spec_guarantees _ _ _ _ increment8_local_spec.
Definition increment16_guarantees := jet_local_spec_guarantees _ _ _ _ increment16_local_spec.
Definition increment32_guarantees := jet_local_spec_guarantees _ _ _ _ increment32_local_spec.
Definition increment64_guarantees := jet_local_spec_guarantees _ _ _ _ increment64_local_spec.
Definition add8_guarantees := jet_local_spec_guarantees _ _ _ _ add8_local_spec.
Definition add16_guarantees := jet_local_spec_guarantees _ _ _ _ add16_local_spec.
Definition add32_guarantees := jet_local_spec_guarantees _ _ _ _ add32_local_spec.
Definition add64_guarantees := jet_local_spec_guarantees _ _ _ _ add64_local_spec.
