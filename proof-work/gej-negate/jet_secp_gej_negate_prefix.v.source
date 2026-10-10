(** Exact helper body and owned prefix, up to its original Y arithmetic. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_gej_negate_fields C.jet_secp_gej_negate_three_copies C.jet_secp_gej_negate_flag.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition gej_negate_y_address : expr :=
  Eaddrof (Efield (Ederef (Etempvar _r (tptr (Tstruct __6123 noattr)))
    (Tstruct __6123 noattr)) _y (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr)).
Definition gej_negate_y_tail : statement :=
  Ssequence
    (Scall None (Evar _secp256k1_fe_normalize_weak (Tfunction
      (Tcons (tptr (Tstruct __5467 noattr)) Tnil) tvoid cc_default))
      [gej_negate_y_address])
    (Scall None (Evar _secp256k1_fe_negate (Tfunction
      (Tcons (tptr (Tstruct __5467 noattr))
        (Tcons (tptr (Tstruct __5467 noattr)) (Tcons tint Tnil))) tvoid cc_default))
      [gej_negate_y_address;gej_negate_y_address;Econst_int (Int.repr 1) tint]).
Lemma gej_negate_helper_body : fn_body f_secp256k1_gej_neg =
  Ssequence gej_negate_flag_prefix
    (Ssequence (gej_negate_field_copy_stmt _x)
      (Ssequence (gej_negate_field_copy_stmt _y)
        (Ssequence (gej_negate_field_copy_stmt _z) gej_negate_y_tail))).
Proof. reflexivity. Qed.
Local Opaque secp_ge.

Theorem exec_gej_negate_owned_prefix le m b base flag :
  0 <= base -> (8 | base) -> base+128 <= Ptrofs.max_unsigned ->
  le!_r = Some (Vptr b (Ptrofs.repr base)) ->
  le!_a = Some (Vptr b (Ptrofs.repr base)) ->
  Mem.range_perm m b base (base+128) Cur Freeable ->
  Mem.load Mint32 m b (base+120) = Some (Vint flag) ->
  exists mi mx my mz,
    Clight2.exec_stmt secp_ge empty_env le m gej_negate_flag_prefix E0
      (PTree.set _t'1 (Vint flag) le) mi Out_normal /\
    Clight2.exec_stmt secp_ge empty_env (PTree.set _t'1 (Vint flag) le) mi
      (gej_negate_field_copy_stmt _x) E0 (PTree.set _t'1 (Vint flag) le) mx Out_normal /\
    Clight2.exec_stmt secp_ge empty_env (PTree.set _t'1 (Vint flag) le) mx
      (gej_negate_field_copy_stmt _y) E0 (PTree.set _t'1 (Vint flag) le) my Out_normal /\
    Clight2.exec_stmt secp_ge empty_env (PTree.set _t'1 (Vint flag) le) my
      (gej_negate_field_copy_stmt _z) E0 (PTree.set _t'1 (Vint flag) le) mz Out_normal /\
    Mem.load Mint32 mz b (base+120) = Some (Vint flag) /\
    Mem.range_perm mz b base (base+128) Cur Freeable /\
    (forall chunk b' ofs,
      Mem.valid_block m b' ->
      b' <> b \/ ofs+size_chunk chunk <= base+120 \/ base+124 <= ofs ->
      Mem.load chunk mz b' ofs = Mem.load chunk m b' ofs).
Proof.
  intros HB HA HM HR HS HP HL.
  destruct (exec_gej_negate_flag_owned le m b base flag HB HA HM HR HS HP HL)
    as (mi & HFlagStmt & HFlag & HPoint & HLoads & HPerms & HValid).
  assert (HR' : (PTree.set _t'1 (Vint flag) le)!_r =
    Some (Vptr b (Ptrofs.repr base))).
  { rewrite PTree.gso by discriminate; exact HR. }
  assert (HS' : (PTree.set _t'1 (Vint flag) le)!_a =
    Some (Vptr b (Ptrofs.repr base))).
  { rewrite PTree.gso by discriminate; exact HS. }
  destruct (exec_gej_negate_three_self_copies (PTree.set _t'1 (Vint flag) le)
    mi b base HB HA HM HR' HS' HPoint) as (mx & my & mz & HX & HY & HZ & HFrame & HFree).
  exists mi,mx,my,mz. split; [exact HFlagStmt|]. split; [exact HX|].
  split; [exact HY|]. split; [exact HZ|]. split.
  - eapply Mem.load_unchanged_on; [exact HFrame|intros;exact I|exact HFlag].
  - split; [exact HFree|].
    intros chunk b' ofs HValidOld HOther.
    transitivity (Mem.load chunk mi b' ofs).
    + eapply Mem.load_unchanged_on_1;
        [exact HFrame|apply HValid;exact HValidOld|intros;exact I].
    + apply HLoads; exact HOther.
Qed.
Timeout 60 Print Assumptions exec_gej_negate_owned_prefix.
