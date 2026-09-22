From Coq Require Import ZArith List PArith.BinPos.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word.
Require Import Simplicity.Bit.
Require Import Simplicity.Util.Monad.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import C.jet_one8.
Require Import C.jet_exec.
Require Import jets.

Import Clightdefs Clightdefs.ClightNotations.
Import Values Mem Ctypes.
Import Events.

Import ListNotations.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Local Open Scope semantic_scope.
Local Open Scope Z_scope.

(* The arithmetic specification is the primitive Simplicity program
   [one word8] = [true >>> left_pad_low word1 word8].  The library's [Word]
   file contains the vector combinators used by this program, but not the
   Haskell-level [left_pad_low] wrapper, so spell out its three padding
   layers here.  The base case is [iden]: the input word is the low word. *)
Fixpoint left_pad_low_1_n {term : Alg.Core.Algebra} (n : nat) :
    @Alg.Core.domain term Bit (Word n) :=
  match n with
  | Datatypes.O => @Alg.Core.Combinators.iden Bit term
  | S n =>
      @Alg.Core.Combinators.pair Bit (Word n) (Word n) term
        (fill (n := n)
          (@Alg.Core.Combinators.comp Bit Ty.Unit Bit term
            (@Alg.Core.Combinators.unit Bit term) (@Bit.false Ty.Unit term)))
        (left_pad_low_1_n n)
  end.

Definition left_pad_low_1_8 {term : Alg.Core.Algebra} :
    @Alg.Core.domain term Bit Word8 :=
  left_pad_low_1_n 3.

Definition one8_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term Ty.Unit Word8 :=
  @Alg.Core.Combinators.comp Ty.Unit Bit Word8 term
    (@Bit.true Ty.Unit term) (@left_pad_low_1_8 term).

Definition one8_spec_value : Ty.tySem Word8 :=
  @one8_spec Alg.CoreFunSem tt.

Lemma one8_spec_correct :
    @one8_spec Alg.CoreFunSem tt = @fromZ (WordToZ 3) 1%Z.
Proof.
  unfold one8_spec, left_pad_low_1_8, left_pad_low_1_n.
  vm_compute; reflexivity.
Qed.

Lemma left_pad_low_1_n_parametric : forall n,
    Alg.Core.Parametric (fun term => @left_pad_low_1_n term n).
Proof.
  intros n alg1 alg2 R.
  induction n as [| n IH].
  - apply Alg.iden_Parametric.
  - cbn [left_pad_low_1_n].
    apply Alg.pair_Parametric.
    + apply fill_Parametric.
      apply Alg.comp_Parametric.
      * apply Alg.unit_Parametric.
      * apply Bit.false_Parametric.
    + apply IH.
Qed.

Lemma one8_spec_parametric : Alg.Core.Parametric (@one8_spec).
Proof.
  intros alg1 alg2 R.
  unfold one8_spec, left_pad_low_1_8.
  apply Alg.comp_Parametric.
  - apply Bit.true_Parametric.
  - apply left_pad_low_1_n_parametric.
Qed.

Lemma one8_spec_initial (M : CIMonad.type) : forall (u : Ty.tySem Ty.Unit),
    @one8_spec (Alg.CoreSem M) u =
      eta (@one8_spec Alg.CoreFunSem u).
Proof.
  apply Alg.CoreSem_initial.
  exact one8_spec_parametric.
Qed.

Definition decode_word8 (w : int64) : Ty.tySem Word8 :=
  @fromZ (WordToZ 3) (Int64.unsigned w).

Definition one8_output_spec (m : mem) (bw : block) : Prop :=
  exists w,
    Mem.load Mint64 m bw 0 = Some (Vlong w) /\
    decode_word8 w = one8_spec_value.

Lemma decode_word8_one :
    decode_word8 (Int64.repr 1) = one8_spec_value.
Proof.
  unfold decode_word8, one8_spec_value.
  rewrite one8_spec_correct.
  vm_compute; reflexivity.
Qed.

Lemma eval_one8_matches_spec : forall (m m1 m2 mw m3 m4 : mem)
    (bl bd bw bs : block) (ofs : ptrofs) (bytes : list memval),
    Mem.alloc m 0 16 = (m1, bl) ->
    (access_mode (Tstruct _frameItem noattr) = By_copy) ->
    (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr) > 0 ->
      (alignof_blockcopy prog.(prog_comp_env) (Tstruct _frameItem noattr) |
        Ptrofs.unsigned ofs)) ->
    (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr) > 0 ->
      (alignof_blockcopy prog.(prog_comp_env) (Tstruct _frameItem noattr) |
        Ptrofs.unsigned Ptrofs.zero)) ->
    bl <> bs \/
      Ptrofs.unsigned ofs = Ptrofs.unsigned Ptrofs.zero \/
      Ptrofs.unsigned ofs + sizeof prog.(prog_comp_env)
        (Tstruct _frameItem noattr) <= Ptrofs.unsigned Ptrofs.zero \/
      Ptrofs.unsigned Ptrofs.zero + sizeof prog.(prog_comp_env)
        (Tstruct _frameItem noattr) <= Ptrofs.unsigned ofs ->
    Mem.loadbytes m1 bs (Ptrofs.unsigned ofs)
      (sizeof prog.(prog_comp_env) (Tstruct _frameItem noattr)) = Some bytes ->
    Mem.storebytes m1 bl 0 bytes = Some m2 ->
    Mem.load Mptr m2 bd 0 = Some (Vptr bw Ptrofs.zero) ->
    Mem.load Mint64 m2 bd 8 = Some (Vlong (Int64.repr 8)) ->
    Mem.load Mint64 m2 bw 0 = Some (Vlong Int64.zero) ->
    Mem.store Mint64 m2 bw 0 (Vlong (Int64.repr 1)) = Some mw ->
    Mem.store Mint64 mw bd 8 (Vlong (Int64.repr 0)) = Some m3 ->
    bd <> bw ->
    bl <> bd ->
    bl <> bw ->
    Mem.free_list m3 (blocks_of_env ge0 (e_one8 bl)) = Some m4 ->
    one8_output_spec m4 bw /\
    ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_one_8)
      (Vptr bd Ptrofs.zero :: Vptr bs ofs :: Vundef :: nil)
      E0 m4 (Vint (Int.repr 1)).
Proof.
  intros m m1 m2 mw m3 m4 bl bd bw bs ofs bytes Halloc Hmode Hsrc_align
    Hdst_align Hdisjoint Hload Hstore Hedge Hoffset Hword Hstore_word
    Hstore_offset Hbdw Hblbd Hblbw Hfree.
  pose proof (eval_one8_zero m m1 m2 mw m3 m4 bl bd bw bs ofs bytes
    Halloc Hmode Hsrc_align Hdst_align Hdisjoint Hload Hstore Hedge Hoffset
    Hword Hstore_word Hstore_offset Hbdw Hblbd Hblbw Hfree) as H.
  destruct H as [Hword_final [Hoffset_final Hcall]].
  split.
  - exists (Int64.repr 1).
    split; [exact Hword_final | apply decode_word8_one].
  - exact Hcall.
Qed.
