(** The generated C implementation versus the canonical Simplicity increment
    term, for every Word8 input on the concrete frame layout stated below. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Util.Monad.
Require Import C.jet_exec C.jet_read8 C.jet_increment8_exec.
Require Import C.jet_increment8_call C.jet_spec C.jets.
Import Values Mem ListNotations.
Local Open Scope Z_scope.

Definition encode_word8 (x : Ty.tySem Word8) : int64 :=
  Int64.repr (@toZ (WordToZ 3) x).

Definition decode_increment8 (w : int64) : Ty.tySem (Ty.Prod Bit Word8) :=
  ((if Int64.testbit w 8 then inr tt else inl tt), decode_word8 w).

Lemma increment8_output_denotes_spec (x : Ty.tySem Word8) :
  decode_increment8 (increment8_written_word (read8_result (encode_word8 x))) =
    increment8_spec_value x.
Proof.
  (* Exhaustion is over the eight input sums of Unit, not over executions.
     The preceding execution theorem handles arbitrary CompCert memories. *)
  destruct x as [[[a b] [c d]] [[e f] [g h]]].
  destruct a as [[]|[]]; destruct b as [[]|[]];
  destruct c as [[]|[]]; destruct d as [[]|[]];
  destruct e as [[]|[]]; destruct f as [[]|[]];
  destruct g as [[]|[]]; destruct h as [[]|[]];
    timeout 10 vm_compute; reflexivity.
Qed.

Lemma increment8_spec_initial (M : CIMonad.type) (x : Ty.tySem Word8) :
  @increment8_spec (Alg.CoreSem M) x = eta (increment8_spec_value x).
Proof. apply Alg.CoreSem_initial. exact increment8_spec_parametric. Qed.

Theorem eval_increment8_matches_spec m bd bs bi bw (x : Ty.tySem Word8) :
  Mem.load Mptr m bs 0 = Some (Vptr bi (Ptrofs.repr 8)) ->
  Mem.load Mint64 m bs 8 = Some (Vlong (Int64.repr 56)) ->
  Mem.load Mint64 m bi 0 = Some (Vlong (encode_word8 x)) ->
  Mem.load Mptr m bd 0 = Some (Vptr bw Ptrofs.zero) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr 9)) ->
  Mem.load Mint64 m bw 0 = Some (Vlong Int64.zero) ->
  Mem.valid_access m Mint64 bd 8 Writable ->
  Mem.valid_access m Mint64 bw 0 Writable ->
  bd <> bw ->
  exists mf output,
    ClightBigstep.Clight2.eval_funcall ge0 m
      (Internal f_simplicity_increment_8)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vundef]
      E0 mf (Vint Int.one) /\
    Mem.load Mint64 mf bw 0 = Some (Vlong output) /\
    decode_increment8 output = @increment8_spec Alg.CoreFunSem x /\
    Mem.load Mint64 mf bd 8 = Some (Vlong Int64.zero) /\
    (forall chunk b ofs, Mem.valid_block m b -> b <> bd -> b <> bw ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs).
Proof.
  intros HSE HSO HI HDE HDO HW PD PW Hneq.
  destruct (eval_increment8_concrete m bd bs bi bw (encode_word8 x)
    HSE HSO HI HDE HDO HW PD PW Hneq) as [mf [HC [HO [HF HP]]]].
  exists mf, (increment8_written_word (read8_result (encode_word8 x))).
  split; [exact HC |]. split; [exact HO |].
  split; [apply increment8_output_denotes_spec |]. split; assumption.
Qed.
