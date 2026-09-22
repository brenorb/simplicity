(** One_8 on an arbitrary initialized output word; the other 56 bits survive. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jet_exec C.jet_one8 C.jet_frame_copy C.jet_spec C.jets.
Require Import C.jet_one8_position.
Require Import C.jet_frame_spec C.jet_word_bits C.jet_word_decode C.jet_write8_general.
Import Values Mem ListNotations.
Local Open Scope Z_scope.

Theorem eval_one8_frame_matches_spec m bd bs bw bytes :
  Mem.loadbytes m bs 0 16 = Some bytes ->
  single_word_output m bd bw 8 ->
  exists mf output,
    ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_one_8)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vundef]
      E0 mf (Vint Int.one) /\
    Mem.load Mint64 mf bw 0 = Some (Vlong output) /\
    decode_word8 output = @one8_spec Alg.CoreFunSem tt /\
    (forall old, Mem.load Mint64 m bw 0 = Some (Vlong old) ->
      word_outside_eq 0 8 output old) /\
    Mem.load Mint64 mf bd 8 = Some (Vlong Int64.zero) /\
    loads_outside_blocks m mf bd bw.
Proof.
  intros HB HF.
  pose proof (eval_one8_position_matches_spec m bd bs bw bytes 8
    ltac:(lia) HB HF) as H.
  change (Int64.repr (8 - 8)) with Int64.zero in H.
  setoid_rewrite Int64.shru_zero in H.
  exact H.
Qed.
