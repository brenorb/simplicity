(** Complete actual secp256k1_umul128 helper call, including its store, return
    and framing. Its output slot is writable initially; no store is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_umul128_value.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition umul128_result_hi a b :=
  umul128_hi (umul128_hh a b) (umul128_lh a b) (umul128_hl a b)
    (umul128_mid (umul128_ll a b) (umul128_lh a b) (umul128_hl a b)).
Definition umul128_result_lo a b :=
  umul128_lo (umul128_ll a b) (umul128_mid (umul128_ll a b) (umul128_lh a b) (umul128_hl a b)).
Definition umul128_temps a b bh ofs :=
  PTree.set _hi (Vptr bh ofs) (PTree.set _b (Vlong b) (PTree.set _a (Vlong a)
    (create_undef_temps f_secp256k1_umul128.(fn_temps)))).

Ltac umul128_lookup :=
  repeat first [rewrite PTree.gss | rewrite PTree.gso by discriminate]; reflexivity.
(** Structural recursion over the seven small generated scalar trees only. *)
Ltac umul128_scalar :=
  lazymatch goal with
  | |- eval_expr _ _ _ _ (Etempvar _ _) _ => apply eval_Etempvar; umul128_lookup
  | |- eval_expr _ _ _ _ (Econst_int _ _) _ => apply eval_Econst_int
  | |- eval_expr _ _ _ _ (Ecast _ _) _ => eapply eval_Ecast; [umul128_scalar|reflexivity]
  | |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ =>
      eapply eval_Ebinop; [umul128_scalar|umul128_scalar|reflexivity]
  end.

Theorem eval_umul128_layout m bh ofs a b :
  Mem.valid_access m Mint64 bh (Ptrofs.unsigned ofs) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_secp256k1_umul128)
      [Vlong a; Vlong b; Vptr bh ofs] E0 mf (Vlong (umul128_result_lo a b)) /\
    Mem.load Mint64 mf bh (Ptrofs.unsigned ofs) = Some (Vlong (umul128_result_hi a b)) /\
    Int64.unsigned (umul128_result_hi a b) = (Int64.unsigned a * Int64.unsigned b) / Int64.modulus /\
    Int64.unsigned (umul128_result_lo a b) = (Int64.unsigned a * Int64.unsigned b) mod Int64.modulus /\
    (forall chunk bb addr, bb <> bh \/ addr + size_chunk chunk <= Ptrofs.unsigned ofs \/
        Ptrofs.unsigned ofs + 8 <= addr -> Mem.load chunk mf bb addr = Mem.load chunk m bb addr) /\
    (forall bb addr kind p, Mem.perm m bb addr kind p -> Mem.perm mf bb addr kind p) /\
    Mem.nextblock mf = Mem.nextblock m.
Proof.
  intros HP.
  destruct (Mem.valid_access_store m Mint64 bh (Ptrofs.unsigned ofs) (Vlong (umul128_result_hi a b)) HP)
    as [mf HS].
  set (le0 := umul128_temps a b bh ofs).
  set (le1 := PTree.set _ll (Vlong (umul128_ll a b)) le0).
  set (le2 := PTree.set _lh (Vlong (umul128_lh a b)) le1).
  set (le3 := PTree.set _hl (Vlong (umul128_hl a b)) le2).
  set (le4 := PTree.set _hh (Vlong (umul128_hh a b)) le3).
  set (le5 := PTree.set _mid34 (Vlong (umul128_mid (umul128_ll a b) (umul128_lh a b) (umul128_hl a b))) le4).
  exists mf. split.
  - eapply eval_funcall_internal with (e := PTree.empty _) (le1 := le0) (le2 := le5)
      (m1 := m) (m2 := mf) (out := Out_return (Some (Vlong (umul128_result_lo a b),tulong))).
    + constructor.
      * constructor.
      * change (list_norepet [_a; _b; _hi]). vm_compute.
        repeat (apply list_norepet_cons; [simpl; intuition discriminate|]). constructor.
      * change (list_disjoint [_a; _b; _hi] [_ll; _lh; _hl; _hh; _mid34]).
        vm_compute. intuition congruence.
      * constructor.
      * reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
      * apply exec_set. unfold le0, umul128_temps, umul128_ll, umul128_low. umul128_scalar.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m).
        -- apply exec_set. unfold le1, le0, umul128_temps, umul128_lh, umul128_low, C.jet_divmod96_value.divmod96_high.
           umul128_scalar.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m).
           ++ apply exec_set. unfold le2, le1, le0, umul128_temps, umul128_hl, umul128_low, C.jet_divmod96_value.divmod96_high.
              umul128_scalar.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m).
              ** apply exec_set. unfold le3, le2, le1, le0, umul128_temps, umul128_hh, C.jet_divmod96_value.divmod96_high.
                 umul128_scalar.
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := m).
                 --- apply exec_set. unfold le4, le3, le2, le1, le0, umul128_temps,
                       umul128_mid, umul128_low, C.jet_divmod96_value.divmod96_high. umul128_scalar.
                 --- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := mf).
                     +++ eapply exec_Sassign with (loc := bh) (ofs := ofs) (bf := Full)
                           (v2 := Vlong (umul128_result_hi a b)) (v := Vlong (umul128_result_hi a b)).
                         *** apply eval_Ederef. apply eval_Etempvar.
                             unfold le5, le4, le3, le2, le1, le0, umul128_temps. umul128_lookup.
                         *** unfold le5, le4, le3, le2, le1, le0, umul128_temps,
                               umul128_result_hi, umul128_hi, C.jet_divmod96_value.divmod96_high. umul128_scalar.
                         *** reflexivity.
                         *** apply assign_loc_value with (chunk := Mint64); [reflexivity|exact HS].
                     +++ apply exec_Sreturn_some. unfold le5, le4, le3, le2, le1, le0, umul128_temps,
                           umul128_result_lo, umul128_lo, umul128_low. umul128_scalar.
    + cbn; split; solve [discriminate|reflexivity].
    + reflexivity.
  - split.
    + exact (Mem.load_store_same Mint64 m bh (Ptrofs.unsigned ofs) (Vlong (umul128_result_hi a b)) mf HS).
    + destruct (umul128_machine_observation a b) as [HH HL]. split; [exact HH|]. split; [exact HL|]. split.
      * intros chunk bb addr Hout. eapply Mem.load_store_other; [exact HS|exact Hout].
      * split.
        -- intros bb addr kind p Hperm. eapply Mem.perm_store_1; eauto.
        -- eapply Mem.nextblock_store; exact HS.
Qed.
