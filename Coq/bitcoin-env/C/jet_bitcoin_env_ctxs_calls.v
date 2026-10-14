(** The context operations of sha256.h on one of several live contexts:
    the call executes, the operated context advances, the others stay live.
    Conditional on [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep C.jet_sha_uchars_exec.
Require Import C.jet_sha_finalize_exec C.jet_sha_ctx_abs.
Require Import C.jet_bitcoin_env_ctxo C.jet_bitcoin_env_ctxo_more C.jet_bitcoin_env_ctxs C.jet_bitcoin_env_ctxs_ops.
Import ListNotations.
Local Open Scope Z_scope.
Local Opaque sha_ge.
Set Default Timeout 120.

Section Calls.
Variable Hmodel : memcpy_model.
Variables (bA : block) (cs : list ctx_entry) (live : nat -> Prop) (k : nat).
Variables (bx : block) (ob : Z) (l regs : list int) (c : int64) (ovf : bool).
Hypothesis HSep : ctxs_sep bA cs.
Hypothesis Hk : nth_error cs k = Some (bx, ob, l, regs, c, ovf).
Hypothesis Hlive : live k.

Lemma call_facts :
  bA <> bx /\ GC <> bx /\ GC <> bA /\ GM <> bx /\ GM <> bA /\ (0 <= ob /\ ob + 32 <= Ptrofs.max_unsigned).
Proof.
  destruct HSep as (NG & NM & H1 & _). destruct (H1 k _ Hk) as (D1 & D2 & D3 & D4 & D5).
  cbn [ctx_block ctx_out] in *. repeat split; auto.
Qed.

Theorem live_hash m bt ot (regsH : list int) :
  ctxs_live m bA cs live ->
  length regsH = 8%nat -> Ptrofs.unsigned ot + 32 <= Ptrofs.max_unsigned ->
  (forall j, (j < 8)%nat ->
     Mem.load Mint32 m bt (Ptrofs.unsigned ot + 4 * Z.of_nat j) = Some (Vint (nth j regsH Int.zero))) ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_hash) [Vptr bx (Ptrofs.repr 0); Vptr bt ot] E0 m' Vundef /\
    ctxs_live m' bA
      (upd cs k (bx, ob, fst (absorb_i l regs (be_bytes regsH)), snd (absorb_i l regs (be_bytes regsH)),
                 Int64.add c (Int64.repr 32), uc_overflow ovf c (Int64.repr 32))) live /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx ->
       (b <> bA \/ ofs + size_chunk ch <= ob \/ ob + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs kk p, Mem.valid_block m b -> Mem.perm m b ofs kk p -> Mem.perm m' b ofs kk p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HC HrH HotM HH. destruct call_facts as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof (HC k _ Hk Hlive) as HA. cbn [ctx_holds] in HA.
  destruct (ctxo_hash bx bA ob F1 F2 F3 F4 F5 F6 Hmodel m bt ot l regs regsH c ovf HA HrH HotM HH)
    as (m' & HCall & HA' & HL & HP & HV).
  exists m'. split; [exact HCall|]. split; [|split; [exact HL|split; [exact HP|exact HV]]].
  eapply live_step; [exact HC|exact HSep|exact Hk|exact HA'|exact HL|exact HP].
Qed.

Theorem live_u32be m (x : int64) :
  ctxs_live m bA cs live ->
  exists m' vr,
    Clight2.eval_funcall sha_ge m (Internal f_sha256_u32be) [Vptr bx (Ptrofs.repr 0); Vlong x] E0 m' vr /\
    ctxs_live m' bA
      (upd cs k (bx, ob, fst (absorb_i l regs (c_be32_bytes x)), snd (absorb_i l regs (c_be32_bytes x)),
                 Int64.add c (Int64.repr 4), uc_overflow ovf c (Int64.repr 4))) live /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx ->
       (b <> bA \/ ofs + size_chunk ch <= ob \/ ob + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs kk p, Mem.valid_block m b -> Mem.perm m b ofs kk p -> Mem.perm m' b ofs kk p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HC. destruct call_facts as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof (HC k _ Hk Hlive) as HA. cbn [ctx_holds] in HA.
  destruct (ctxo_u32be Hmodel bx bA ob F1 F2 F3 F4 F5 F6 m l regs x c ovf HA)
    as (m' & HCall & HA' & HL & HP & HV).
  exists m'. eexists. split; [exact HCall|]. split; [|split; [exact HL|split; [exact HP|exact HV]]].
  eapply live_step; [exact HC|exact HSep|exact Hk|exact HA'|exact HL|exact HP].
Qed.

Theorem live_u64be m (x : int64) :
  ctxs_live m bA cs live ->
  exists m' vr,
    Clight2.eval_funcall sha_ge m (Internal f_sha256_u64be) [Vptr bx (Ptrofs.repr 0); Vlong x] E0 m' vr /\
    ctxs_live m' bA
      (upd cs k (bx, ob, fst (absorb_i l regs (c_be64_bytes x)), snd (absorb_i l regs (c_be64_bytes x)),
                 Int64.add c (Int64.repr 8), uc_overflow ovf c (Int64.repr 8))) live /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx ->
       (b <> bA \/ ofs + size_chunk ch <= ob \/ ob + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs kk p, Mem.valid_block m b -> Mem.perm m b ofs kk p -> Mem.perm m' b ofs kk p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HC. destruct call_facts as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof (HC k _ Hk Hlive) as HA. cbn [ctx_holds] in HA.
  destruct (ctxo_u64be Hmodel bx bA ob F1 F2 F3 F4 F5 F6 m l regs x c ovf HA)
    as (m' & HCall & HA' & HL & HP & HV).
  exists m'. eexists. split; [exact HCall|]. split; [|split; [exact HL|split; [exact HP|exact HV]]].
  eapply live_step; [exact HC|exact HSep|exact Hk|exact HA'|exact HL|exact HP].
Qed.

Theorem live_uchar m (x : int) :
  ctxs_live m bA cs live -> Int.zero_ext 8 x = x ->
  exists m' vr,
    Clight2.eval_funcall sha_ge m (Internal f_sha256_uchar) [Vptr bx (Ptrofs.repr 0); Vint x] E0 m' vr /\
    ctxs_live m' bA
      (upd cs k (bx, ob, fst (absorb_i l regs [x]), snd (absorb_i l regs [x]),
                 Int64.add c (Int64.repr 1), uc_overflow ovf c (Int64.repr 1))) live /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx ->
       (b <> bA \/ ofs + size_chunk ch <= ob \/ ob + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs kk p, Mem.valid_block m b -> Mem.perm m b ofs kk p -> Mem.perm m' b ofs kk p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HC Hx. destruct call_facts as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof (HC k _ Hk Hlive) as HA. cbn [ctx_holds] in HA.
  destruct (ctxo_uchar Hmodel bx bA ob F1 F2 F3 F4 F5 F6 m l regs x c ovf HA Hx)
    as (m' & HCall & HA' & HL & HP & HV).
  exists m'. eexists. split; [exact HCall|]. split; [|split; [exact HL|split; [exact HP|exact HV]]].
  eapply live_step; [exact HC|exact HSep|exact Hk|exact HA'|exact HL|exact HP].
Qed.

(** [sha256_finalize]: the output field receives the padded state; the
    context is spent and the others stay live. *)
Theorem live_finalize m :
  ctxs_live m bA cs live ->
  exists m' vr,
    Clight2.eval_funcall sha_ge m (Internal f_sha256_finalize) [Vptr bx (Ptrofs.repr 0)] E0 m' vr /\
    (forall i, (i < 8)%nat ->
       Mem.load Mint32 m' bA (ob + 4 * Z.of_nat i) =
         Some (Vint (nth i (snd (absorb_i l regs (sha_pad c))) Int.zero))) /\
    ctxs_live m' bA cs (fun j => live j /\ j <> k) /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx ->
       (b <> bA \/ ofs + size_chunk ch <= ob \/ ob + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs kk p, Mem.valid_block m b -> Mem.perm m b ofs kk p -> Mem.perm m' b ofs kk p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HC. destruct call_facts as (F1 & F2 & F3 & F4 & F5 & F6).
  pose proof (HC k _ Hk Hlive) as HA. cbn [ctx_holds] in HA.
  destruct (ctxo_finalize bx bA ob F1 F2 F3 F4 F5 F6 Hmodel m l regs c ovf HA)
    as (m' & HCall & HReg & HL & HP & HV).
  exists m'. eexists. split; [exact HCall|]. split; [exact HReg|].
  split; [|split; [exact HL|split; [exact HP|exact HV]]].
  eapply live_kill; [exact HC|exact HSep|exact Hk|exact HL|exact HP].
Qed.
End Calls.
