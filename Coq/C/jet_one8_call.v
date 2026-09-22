(** Total [one_8] execution from initial-memory facts, including the by-value
    source-frame copy even though the Simplicity input is Unit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jet_exec C.jet_one8 C.jet_frame_copy C.jet_spec C.jets.
Require Import C.jet_frame_spec C.jet_one8_general.
Import Values Mem ListNotations.
Local Open Scope Z_scope.

Theorem eval_one8_initial_matches_spec m bd bs bw bytes :
  Mem.loadbytes m bs 0 16 = Some bytes ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr 8)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong Int64.zero) ->
  Mem.valid_access m Mint64 bd 8 Writable ->
  Mem.valid_access m Mint64 bw 0 Writable ->
  bd <> bw ->
  exists mf output,
    ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_one_8)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vundef]
      E0 mf (Vint Int.one) /\
    Mem.load Mint64 mf bw 0 = Some (Vlong output) /\
    decode_word8 output = @one8_spec Alg.CoreFunSem tt /\
    Mem.load Mint64 mf bd 8 = Some (Vlong Int64.zero) /\
    (forall chunk b ofs, Mem.valid_block m b -> b <> bd -> b <> bw ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HB HE HO HW PD PW HDw.
  assert (HF : single_word_output m bd bw 8).
  { split; [split; assumption |]. split; [lia |].
    split; [exact HDw |]. split; [exact PD |].
    split; [exact PW |]. exists Int64.zero; exact HW. }
  destruct (eval_one8_frame_matches_spec m bd bs bw bytes HB HF)
    as [mf [output [HC [Hout [Hspec [Hbits [Hoff Hmem]]]]]]].
  exists mf, output. split; [exact HC |]. split; [exact Hout |].
  split; [exact Hspec |]. split; assumption.
Qed.
