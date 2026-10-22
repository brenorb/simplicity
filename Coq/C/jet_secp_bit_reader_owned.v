(** The original readBit on an owned local source-frame copy. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_frame_layout C.jet_input_layout C.jet_readBit_layout
 C.jet_secp_linkage C.jet_exec.
Require C.jets.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge ge0.

Theorem eval_secp_readBit_owned m bl bi edge rc (bit : bool) :
 0<=rc -> rc+1<=Int64.max_unsigned ->
 frame_fields_at m bl 0 bi edge rc -> frame_input_bit_at m bi edge rc bit ->
 Mem.range_perm m bl 0 16 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal C.jets.f_readBit)
   [Vptr bl Ptrofs.zero] E0 mf (Vint (bit_int bit)) /\
 frame_fields_at mf bl 0 bi edge (rc+1) /\
 Mem.range_perm mf bl 0 16 Cur Freeable /\ lframe (fun b _=>b<>bl) m mf.
Proof.
 intros RC Max Source Input Free.
 assert (WritePerm : Mem.valid_access m Mint64 bl (0+8) Writable).
 { split.
   - intros pos Pos;eapply Mem.perm_implies;[apply Free;cbn in Pos;lia|constructor].
   - change (8|8);exists 1;reflexivity. }
 destruct (eval_readBit_layout m bl 0 bi edge rc bit
   ltac:(change (0<=0 /\ 16<=18446744073709551615+1);lia)
   ltac:(lia) Source Input WritePerm) as (mf & Call & Fields & Loads & Perms & Valid).
 exists mf;split.
 - eapply secp_transport_call;[|exact Call].
   unfold secp_core_helpers;cbn;tauto.
 - split;[exact Fields|];split.
   + intros pos Pos;apply Perms;apply Free;exact Pos.
   + split.
     * intros ch b ofs VB Outside;apply Loads;left.
       exact (Outside ofs ltac:(pose proof (size_chunk_pos ch);lia)).
     * split;[intros;apply Perms;assumption|exact Valid].
Qed.
