(** Retain validity, outside-point framing and coordinate loads through prefix. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_gej_negate_fields C.jet_secp_gej_negate_three_copies C.jet_secp_gej_negate_flag.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem exec_gej_negate_prefix_framed le m b flag :
  le!_r = Some (Vptr b Ptrofs.zero) ->
  le!_a = Some (Vptr b Ptrofs.zero) ->
  Mem.range_perm m b 0 128 Cur Freeable ->
  Mem.load Mint32 m b 120 = Some (Vint flag) ->
  exists mi mx my mz,
    Clight2.exec_stmt secp_ge empty_env le m gej_negate_flag_prefix E0
      (PTree.set _t'1 (Vint flag) le) mi Out_normal /\
    Clight2.exec_stmt secp_ge empty_env (PTree.set _t'1 (Vint flag) le) mi
      (gej_negate_field_copy_stmt _x) E0 (PTree.set _t'1 (Vint flag) le) mx Out_normal /\
    Clight2.exec_stmt secp_ge empty_env (PTree.set _t'1 (Vint flag) le) mx
      (gej_negate_field_copy_stmt _y) E0 (PTree.set _t'1 (Vint flag) le) my Out_normal /\
    Clight2.exec_stmt secp_ge empty_env (PTree.set _t'1 (Vint flag) le) my
      (gej_negate_field_copy_stmt _z) E0 (PTree.set _t'1 (Vint flag) le) mz Out_normal /\
    Mem.load Mint32 mz b 120 = Some (Vint flag) /\
    Mem.range_perm mz b 0 128 Cur Freeable /\
    (forall chunk bx ofs, Mem.valid_block m bx ->
      bx <> b \/ ofs+size_chunk chunk <= 120 \/ 124 <= ofs ->
      Mem.load chunk mz bx ofs = Mem.load chunk m bx ofs) /\
    lframe (fun bx _ => bx <> b) m mz.
Proof.
  intros HR HA HP HL.
  destruct (exec_gej_negate_flag_owned le m b 0 flag ltac:(lia)
    ltac:(exists 0;lia) ltac:(change (128<=18446744073709551615);lia)
    HR HA HP HL) as (mi & HStmt & HFlag & HFree & HLoads & HPerms & HValid).
  assert (HR' : (PTree.set _t'1 (Vint flag) le)!_r = Some (Vptr b Ptrofs.zero)).
  { rewrite PTree.gso by discriminate; exact HR. }
  assert (HA' : (PTree.set _t'1 (Vint flag) le)!_a = Some (Vptr b Ptrofs.zero)).
  { rewrite PTree.gso by discriminate; exact HA. }
  destruct (exec_gej_negate_three_self_copies (PTree.set _t'1 (Vint flag) le)
    mi b 0 ltac:(lia) ltac:(exists 0;lia)
    ltac:(change (128<=18446744073709551615);lia) HR' HA' HFree)
    as (mx & my & mz & HX & HY & HZ & HCopyFrame & HFreeZ).
  assert (HOutside : lframe (fun bx _ => bx <> b) m mi).
  { split.
    - intros chunk bx ofs HB HOther.
      apply HLoads; left.
      apply (HOther ofs); pose proof (size_chunk_pos chunk); lia.
    - split.
      + intros bx ofs kind perm _ _ HPerm; apply (proj2 (HPerms bx ofs kind perm)); exact HPerm.
      + exact HValid. }
  exists mi,mx,my,mz; split; [exact HStmt|]. split; [exact HX|].
  split; [exact HY|]. split; [exact HZ|]. split.
  - eapply Mem.load_unchanged_on; [exact HCopyFrame|intros;exact I|exact HFlag].
  - split; [exact HFreeZ|]. split.
    + intros chunk bx ofs HB HOther.
      transitivity (Mem.load chunk mi bx ofs).
      * eapply Mem.load_unchanged_on_1; [exact HCopyFrame|apply HValid;exact HB|intros;exact I].
      * apply HLoads; exact HOther.
    + eapply lframe_trans; [exact HOutside|].
      eapply lframe_implies; [apply lframe_unchanged;exact HCopyFrame|intros;exact I].
Qed.
Timeout 60 Print Assumptions exec_gej_negate_prefix_framed.
