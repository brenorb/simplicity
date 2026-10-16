(** Interpret the original parametric Bitcoin programs over raw inputs.
    A single primitive/Assertion-algebra relation transports whole programs;
    no cached hash is substituted for the canonical program's meaning. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Primitive Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import Simplicity.Primitive.Bitcoin.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_bitcoin_raw_env.
Require Import C.jet_bitcoin_raw_jets C.jet_application_sep.
Set Default Timeout 10.

Definition raw_full_sem {A B} (p : BitcoinFull.t A B) (a : Ty.tySem A)
    (environment : raw_bitcoin_environment) : option (Ty.tySem B) :=
  (match p in BitcoinFull.prim A B return Ty.tySem A -> option (Ty.tySem B) with
   | BitcoinFull.Base q => fun a => Bitcoin.sem q a (raw_base environment)
   | BitcoinFull.Ext q => fun a => raw_ext_sem q a environment
   end) a.

Definition raw_fullalg : PF.Algebra :=
  @PF._Pack (fun A B => Ty.tySem A -> raw_bitcoin_environment -> option (Ty.tySem B))
    (@PF.Class _
      (Alg.Assertion.class_of (Alg.AssertionSem (ReaderT_CIMonadZero raw_bitcoin_environment option_Monad_Zero)))
      (@PF.Mixin _ (@raw_full_sem))).

Lemma raw_full_projection {A B} (p : BitcoinFull.t A B) a environment Hpath :
  BitcoinFull.sem p a (project_raw_environment environment Hpath) = raw_full_sem p a environment.
Proof.
  destruct p; [reflexivity|apply bitcoin_ext_raw_projection].
Qed.

Definition raw_program_relation {A B} (f : PF.domain fullalg A B)
    (g : PF.domain raw_fullalg A B) : Prop :=
  forall a environment Hpath,
    f a (project_raw_environment environment Hpath) = g a environment.

Lemma raw_core_relation_class :
  @Alg.Core.Parametric.class fullcore (PF.CanonicalStructures.toCore raw_fullalg)
    (@raw_program_relation).
Proof.
  constructor.
  - intros A a environment Hpath. reflexivity.
  - intros A B C s1 s2 t1 t2 Hs Ht a environment Hpath.
    (* The option Reader dictionaries contain a map/join pair, not the
       definitionally reduced bind. Leave the raw projection opaque. *)
    cbv -[project_raw_environment].
    rewrite Hs. destruct (s2 a environment); [apply Ht|reflexivity].
  - intros A a environment Hpath. reflexivity.
  - intros A B C t1 t2 Ht a environment Hpath.
    cbv -[project_raw_environment].
    rewrite Ht. reflexivity.
  - intros A B C t1 t2 Ht a environment Hpath.
    cbv -[project_raw_environment].
    rewrite Ht. reflexivity.
  - intros A B C D s1 s2 t1 t2 Hs Ht [[a|b] c] environment Hpath;
      [apply Hs|apply Ht].
  - intros A B C s1 s2 t1 t2 Hs Ht a environment Hpath.
    cbv -[project_raw_environment].
    rewrite Hs. destruct (s2 a environment); [|reflexivity].
    cbv beta iota. rewrite Ht. reflexivity.
  - intros A B C t1 t2 Ht [a b] environment Hpath. apply Ht.
  - intros A B C t1 t2 Ht [a b] environment Hpath. apply Ht.
Qed.

Lemma raw_assertion_relation_class :
  @Alg.Assertion.Parametric.class fullassert (PF.CanonicalStructures.toAssertion raw_fullalg)
    (@raw_program_relation).
Proof.
  constructor; [exact raw_core_relation_class|]. constructor.
  - intros A B C D s1 s2 th Hs [[a|b] c] environment Hpath; [apply Hs|reflexivity].
  - intros A B C D sh t1 t2 Ht [[a|b] c] environment Hpath; [reflexivity|apply Ht].
  - intros A B hh a environment Hpath. reflexivity.
Qed.

Lemma raw_program_relation_class :
  @PF.Parametric.class fullalg raw_fullalg (@raw_program_relation).
Proof.
  constructor; [exact raw_assertion_relation_class|]. constructor.
  intros A B p a environment Hpath.
  rewrite fx_prim.
  change (BitcoinFull.sem p a (project_raw_environment environment Hpath) = raw_full_sem p a environment).
  apply raw_full_projection.
Qed.

Definition raw_program_parametric_relation : PF.Parametric.Rel fullalg raw_fullalg :=
  @PF.Parametric.Pack fullalg raw_fullalg (@raw_program_relation) raw_program_relation_class.

Theorem bitcoin_program_raw_projection {A B : Ty}
    (program : forall alg : PF.Algebra, PF.domain alg A B)
    (Hprogram : PF.Parametric program) a environment Hpath :
  program fullalg a (project_raw_environment environment Hpath) = program raw_fullalg a environment.
Proof.
  exact (Hprogram fullalg raw_fullalg raw_program_parametric_relation a environment Hpath).
Qed.

Theorem application_raw_program_local_spec_sep f ge A B rep
    (program : forall alg : PF.Algebra, PF.domain alg A B)
    (Hprogram : PF.Parametric program) :
  application_jet_local_spec_sep f ge ext_environment A B rep (program fullalg) ->
  application_jet_local_spec_sep f ge raw_bitcoin_environment A B
    (raw_env_rep rep) (program raw_fullalg).
Proof.
  apply application_raw_local_spec_sep.
  intros a environment Hpath. apply bitcoin_program_raw_projection. exact Hprogram.
Qed.
