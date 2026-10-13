(** The initial memory of the SHA translation unit exists.

    [sha_startup_state_initialized] and the lifecycle theorem start from
    [Genv.init_mem jets_sha.prog = Some m].  CompCert's initial memory is a
    partial function: it is defined when every global variable's
    initialization data is aligned and every symbol whose address is taken
    in an initializer is defined.  Both conditions are checked here for the
    actual program by a Boolean procedure proved sound, so the startup
    results are not vacuous: there is an initial memory, it satisfies the
    invariant, and lifecycles exist. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Memory Globalenvs.
Require Import C.jets_sha.
Require Import C.jet_sha_startup_state C.jet_sha_startup_lifecycle.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

Fixpoint init_aligned_b (p : Z) (il : list init_data) : bool :=
  match il with
  | [] => true
  | i :: rest =>
      Z.eqb (p mod Genv.init_data_alignment i) 0 &&
      init_aligned_b (p + init_data_size i) rest
  end.

Lemma init_data_alignment_pos i : 0 < Genv.init_data_alignment i.
Proof. destruct i; cbn; try lia. destruct Archi.ptr64; lia. Qed.

Lemma init_aligned_b_sound : forall il p,
  init_aligned_b p il = true -> Genv.init_data_list_aligned p il.
Proof.
  induction il as [|i rest IH]; intros p H; cbn [Genv.init_data_list_aligned]; [exact I|].
  cbn [init_aligned_b] in H. apply andb_true_iff in H. destruct H as [H1 H2].
  split; [|exact (IH _ H2)].
  apply Z.eqb_eq in H1. apply Z.mod_divide; [|exact H1].
  pose proof (init_data_alignment_pos i). lia.
Qed.

Section Symbols.
Context {F V : Type} (ge : Genv.t F V).

Definition addrof_defined_b (d : init_data) : bool :=
  match d with
  | Init_addrof i _ => match Genv.find_symbol ge i with Some _ => true | None => false end
  | _ => true
  end.

Lemma addrof_defined_b_sound il :
  forallb addrof_defined_b il = true ->
  forall i o, In (Init_addrof i o) il -> exists b, Genv.find_symbol ge i = Some b.
Proof.
  intros H i o HIn. rewrite forallb_forall in H. specialize (H _ HIn).
  cbn [addrof_defined_b] in H. destruct (Genv.find_symbol ge i) as [b|]; [|discriminate].
  exists b. reflexivity.
Qed.
End Symbols.

Definition globvar_init_ok {F V : Type} (ge : Genv.t F V) (g : globdef F V) : bool :=
  match g with
  | Gvar v => init_aligned_b 0 (gvar_init v) && forallb (addrof_defined_b ge) (gvar_init v)
  | Gfun _ => true
  end.

Theorem init_mem_exists_checked {F V : Type} (p : AST.program F V) :
  forallb (fun idg => globvar_init_ok (Genv.globalenv p) (snd idg)) (AST.prog_defs p) = true ->
  exists m, Genv.init_mem p = Some m.
Proof.
  intros H. apply Genv.init_mem_exists. intros id v HIn.
  rewrite forallb_forall in H. specialize (H _ HIn). cbn [snd globvar_init_ok] in H.
  apply andb_true_iff in H. destruct H as [H1 H2]. split.
  - exact (init_aligned_b_sound _ _ H1).
  - exact (addrof_defined_b_sound _ _ H2).
Qed.

Lemma sha_program_initializers_ok :
  forallb (fun idg => globvar_init_ok (Genv.globalenv (program_of_program jets_sha.prog)) (snd idg))
    (AST.prog_defs (program_of_program jets_sha.prog)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem sha_init_mem_exists : exists m, Genv.init_mem jets_sha.prog = Some m.
Proof. exact (init_mem_exists_checked _ sha_program_initializers_ok). Qed.

(** The invariant is inhabited by the program's own initial memory. *)
Theorem sha_startup_state_exists : exists m, sha_startup_state m.
Proof.
  destruct sha_init_mem_exists as [m HInit].
  exists m. exact (sha_startup_state_initialized m HInit).
Qed.

Theorem sha_lifecycle_exists : exists m, sha_lifecycle m [].
Proof.
  destruct sha_init_mem_exists as [m HInit].
  exists m. exact (life_initial m HInit).
Qed.
