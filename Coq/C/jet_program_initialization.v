(** Generic checked initialization conditions, without constructing a memory image. *)
From Coq Require Import ZArith List Bool Lia.
From compcert Require Import AST Ctypes Globalenvs Memory.
Local Open Scope Z_scope.
Set Default Timeout 10.
Fixpoint initializer_alignedb (ofs : Z) (il : list init_data) : bool :=
  match il with
  | nil => true
  | i :: rest => Z.eqb (ofs mod Genv.init_data_alignment i) 0 &&
      initializer_alignedb (ofs + init_data_size i) rest
  end.
Definition initializer_referenceb {F V : Type} (ge : Genv.t F V) (i : init_data) : bool :=
  match i with
  | Init_addrof id _ =>
      match Genv.find_symbol ge id with Some _ => true | None => false end
  | _ => true
  end.
Definition program_initialization_okb {F V : Type} (p : AST.program F V) : bool :=
  forallb (fun idg => match snd idg with
    | Gfun _ => true
    | Gvar v => initializer_alignedb 0 (gvar_init v) &&
        forallb (initializer_referenceb (Genv.globalenv p)) (gvar_init v)
    end) (AST.prog_defs p).
Lemma initializer_alignment_positive i : 0 < Genv.init_data_alignment i.
Proof. destruct i; cbn [Genv.init_data_alignment]; try lia; destruct Archi.ptr64; lia. Qed.
Lemma initializer_alignedb_sound il ofs : initializer_alignedb ofs il = true -> Genv.init_data_list_aligned ofs il.
Proof.
  revert ofs; induction il as [|i rest IH]; intros ofs H; [exact I|].
  cbn [initializer_alignedb] in H; apply andb_true_iff in H; destruct H as (HA & HR).
  split; [|apply IH; exact HR]. apply Z.mod_divide; [pose proof (initializer_alignment_positive i); lia|].
  apply Z.eqb_eq; exact HA.
Qed.
Lemma program_initialization_checked {F V : Type} (p : AST.program F V) :
  program_initialization_okb p = true -> exists m, Genv.init_mem p = Some m.
Proof.
  intro H.
  apply Genv.init_mem_exists; intros id v Hin.
  unfold program_initialization_okb in H; rewrite forallb_forall in H.
  specialize (H (id,Gvar v) Hin); cbn [snd] in H; apply andb_true_iff in H.
  destruct H as (HA & HR); split; [apply initializer_alignedb_sound; exact HA|].
  intros i ofs HRef; rewrite forallb_forall in HR; specialize (HR (Init_addrof i ofs) HRef).
  unfold initializer_referenceb in HR.
  destruct (Genv.find_symbol (Genv.globalenv p) i) as [b|] eqn:HB;
    [exists b; reflexivity|discriminate HR].
Qed.
