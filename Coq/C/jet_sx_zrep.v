(** Integer values of the cells of a region of 64-bit words. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Maps Values Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_zval C.jet_sx_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

Fixpoint zreg_okb (bnd : nat -> Z * Z) (ofs : Z) (cs : list cell) : bool :=
  match cs with
  | [] => true
  | c :: t =>
      Z.eqb (cofs c) ofs && chunk_eqb (cchunk c) Mint64 &&
      match cval c with
      | Some x => isk KL x && match zb bnd x with Some _ => true | None => false end
      | None => false
      end && zreg_okb bnd (ofs + 8) t
  end.

Definition zcells (zρ : nat -> Z) (cs : list cell) : list Z :=
  map (fun c => match cval c with Some x => zval zρ x | None => 0 end) cs.

Section ZREP.
Variables (ρ : nat -> int64) (bnd : nat -> Z * Z) (β : layout).
Hypothesis Hb : forall n, fst (bnd n) <= Int64.unsigned (ρ n) <= snd (bnd n).

Lemma zreg_load m r w cs : forall ofs,
  zreg_okb bnd ofs cs = true -> Forall (cell_ok ρ β m r w) cs ->
  (forall i z, nth_error (zcells (zrho ρ) cs) i = Some z ->
     Mem.load Mint64 m (blk β r) (bas β r + (ofs + 8 * Z.of_nat i)) = Some (Vlong (Int64.repr z))) /\
  Mem.range_perm m (blk β r) (bas β r + ofs) (bas β r + ofs + 8 * Z.of_nat (length cs)) Cur
    (if w then Writable else Readable).
Proof.
  induction cs as [|c t IH]; intros ofs Hok Hc.
  - split; [intros i z H; destruct i; discriminate|]. intros o Ho. simpl in Ho. lia.
  - simpl in Hok. apply andb_true_iff in Hok. destruct Hok as [Hok Ht].
    apply andb_true_iff in Hok. destruct Hok as [Hok Hv].
    apply andb_true_iff in Hok. destruct Hok as [Ho Hch].
    apply Z.eqb_eq in Ho. apply chunk_eqb_eq in Hch.
    destruct (cval c) as [x|] eqn:Ev; [|discriminate].
    apply andb_true_iff in Hv. destruct Hv as [Hk Hz].
    destruct (zb bnd x) as [[lo hi]|] eqn:Ez; [|discriminate].
    inversion Hc as [|? ? Hc1 Hct]; subst.
    destruct (IH (cofs c + 8) Ht Hct) as [IHl IHp].
    destruct Hc1 as (_ & _ & Hperm & Hval). rewrite Hch in *.
    split.
    + intros i z Hn. destruct i; simpl in Hn.
      * rewrite Ev in Hn. inversion Hn; subst z.
        destruct (Hval x Ev) as [Hl _]. rewrite Z.mul_0_r, Z.add_0_r, Hl.
        rewrite (proj1 (den_zval_long ρ bnd (lay β) Hb x lo hi Ez Hk)). reflexivity.
      * replace (cofs c + 8 * Z.of_nat (S i)) with (cofs c + 8 + 8 * Z.of_nat i) by lia.
        apply IHl. exact Hn.
    + intros o Ho. simpl length in Ho. change (size_chunk Mint64) with 8 in Hperm.
      destruct (Z_lt_dec o (bas β r + cofs c + 8)); [apply Hperm; lia|apply IHp; lia].
Qed.
End ZREP.
