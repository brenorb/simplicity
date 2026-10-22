(** Actual single-limb scalar bit extraction, used by wNAF. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs
  ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_exec C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_signed62_numeric C.jet_secp_u128_word_shift.
Require Import C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric.
Require Import C.jet_secp_fe_math.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_bits_temps b base off count :=
  PTree.set _count (Vint count) (PTree.set _offset (Vint off)
    (PTree.set _a (Vptr b (Ptrofs.repr base))
      (create_undef_temps (fn_temps f_secp256k1_scalar_get_bits)))).
Definition scalar_bits_load_expr :=
  match fn_body f_secp256k1_scalar_get_bits with
  | Ssequence _ (Ssequence (Sset _ e) _) => e | _ => Econst_int Int.zero tint end.
Definition scalar_bits_result_expr :=
  match fn_body f_secp256k1_scalar_get_bits with
  | Ssequence _ (Ssequence _ (Sreturn (Some e))) => e | _ => Econst_int Int.zero tint end.
Definition scalar_bits_index off := Int.unsigned (Int.shru off (Int.repr 6)).
Definition scalar_bits_shift off := Int.unsigned (Int.and off (Int.repr 63)).
Definition scalar_bits_result limb off count :=
  Int64.loword (Int64.and
    (Int64.shru limb (Int64.repr (scalar_bits_shift off)))
    (Int64.sub (Int64.shl Int64.one (Int64.repr (Int.unsigned count))) Int64.one)).

Lemma scalar_bits_source : fn_body f_secp256k1_scalar_get_bits =
  Ssequence (Sloop Sskip Sbreak)
    (Ssequence (Sset _t'1 scalar_bits_load_expr) (Sreturn (Some scalar_bits_result_expr))).
Proof. reflexivity. Qed.
Local Opaque secp_ge.

Lemma scalar_bits_d_layout : exists co,
  (genv_cenv secp_ge)!__5826=Some co /\
  field_offset secp_ge _d (co_members co)=Errors.OK (0,Full).
Proof.
  assert (HM : option_map co_members ((genv_cenv secp_ge)!__5826)=
    Some [Member_plain _d (tarray tulong 4)]) by (vm_compute;reflexivity).
  destruct ((genv_cenv secp_ge)!__5826) as [co|] eqn:HC;[|discriminate].
  exists co;split;[reflexivity|].
  inversion HM as [Members];rewrite Members;reflexivity.
Qed.

Lemma scalar_bits_shift_bound off : 0<=scalar_bits_shift off<64.
Proof.
  unfold scalar_bits_shift.
  pose proof (Int.unsigned_range (Int.and off (Int.repr 63))) as Nonnegative.
  pose proof (Int.and_le (Int.repr 63) off) as Upper.
  rewrite Int.and_commut in Upper;change (Int.unsigned (Int.repr 63)) with 63 in Upper;lia.
Qed.

Lemma scalar_bits_mask count : Int.unsigned count<64 ->
  Int64.sub (Int64.shl Int64.one (Int64.repr (Int.unsigned count))) Int64.one=
    Int64.repr (2^(Int.unsigned count)-1).
Proof.
  intro Bound;pose proof (Int.unsigned_range count) as Nonnegative.
  rewrite Int64.shl_mul_two_p,Int64.mul_commut,Int64.mul_one.
  rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615;lia).
  rewrite two_p_equiv.
  assert (Power : 0<2^(Int.unsigned count)<2^64).
  { split;[apply Z.pow_pos_nonneg;lia|apply Z.pow_lt_mono_r;lia]. }
  unfold Int64.sub;rewrite Int64.unsigned_repr by
    (change Int64.max_unsigned with 18446744073709551615;lia).
  reflexivity.
Qed.

Theorem scalar_bits_result_numeric limb off count : Int.unsigned count<64 ->
  scalar_bits_result limb off count=
    Int.repr ((Int64.unsigned limb / 2^(scalar_bits_shift off)) mod 2^(Int.unsigned count)).
Proof.
  intro Bound;unfold scalar_bits_result,Int64.loword.
  rewrite scalar_bits_mask by exact Bound.
  rewrite repack_mask_unsigned by (pose proof (Int.unsigned_range count);lia).
  rewrite uns_shru by apply scalar_bits_shift_bound.
  reflexivity.
Qed.

Lemma scalar_bits_entry m b base off count :
  function_entry2 secp_ge f_secp256k1_scalar_get_bits
    [Vptr b (Ptrofs.repr base);Vint off;Vint count] m empty_env
    (scalar_bits_temps b base off count) m.
Proof.
  assert (OK : fn_okb f_secp256k1_scalar_get_bits=true) by reflexivity.
  destruct (fn_okb_true _ OK) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD|constructor|reflexivity].
Qed.

Lemma eval_scalar_bits_load e le m b base off limb :
  le!_a=Some (Vptr b (Ptrofs.repr base)) -> le!_offset=Some (Vint off) ->
  0<=base -> base+8*scalar_bits_index off<=Ptrofs.max_unsigned ->
  Mem.load Mint64 m b (base+8*scalar_bits_index off)=Some (Vlong limb) ->
  eval_expr secp_ge e le m scalar_bits_load_expr (Vlong limb).
Proof.
  intros HA HO HB HM HL;unfold scalar_bits_load_expr.
  destruct scalar_bits_d_layout as (co & HC & HF).
  eapply eval_Elvalue with (loc:=b) (ofs:=Ptrofs.repr (base+8*scalar_bits_index off)).
  - eapply eval_Ederef.
    eapply eval_Ebinop with
      (v1:=Vptr b (Ptrofs.repr base)) (v2:=Vint (Int.shru off (Int.repr 6))).
    + rewrite <- (Ptrofs.add_zero (Ptrofs.repr base)).
      eapply eval_Elvalue.
      * eapply eval_Efield_struct with (ofs:=Ptrofs.repr base) (delta:=0) (co:=co).
        -- eapply eval_Elvalue;[eapply eval_Ederef;apply eval_Etempvar;exact HA|].
           apply deref_loc_copy;reflexivity.
        -- reflexivity.
        -- exact HC.
        -- exact HF.
      * apply deref_loc_reference;reflexivity.
    + eapply eval_Ebinop;[apply eval_Etempvar;exact HO|constructor|reflexivity].
    + change (Some (Vptr b (Ptrofs.add (Ptrofs.repr base)
        (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_intu (Int.shru off (Int.repr 6))))))=
        Some (Vptr b (Ptrofs.repr (base+8*scalar_bits_index off)))).
      pose proof (Int.unsigned_range (Int.shru off (Int.repr 6))) as Index.
      change Int.modulus with 4294967296 in Index.
      unfold Ptrofs.of_intu,Ptrofs.of_int,Ptrofs.add,Ptrofs.mul,scalar_bits_index in *.
      rewrite (Ptrofs.unsigned_repr 8) by (change Ptrofs.max_unsigned with 18446744073709551615;lia).
      rewrite (Ptrofs.unsigned_repr (Int.unsigned (Int.shru off (Int.repr 6)))) by
        (change Ptrofs.max_unsigned with 18446744073709551615;lia).
      rewrite (Ptrofs.unsigned_repr (8*Int.unsigned (Int.shru off (Int.repr 6)))) by
        (change Ptrofs.max_unsigned with 18446744073709551615;lia).
      rewrite (Ptrofs.unsigned_repr base) by
        (change Ptrofs.max_unsigned with 18446744073709551615 in *;lia).
      reflexivity.
  - apply deref_loc_value with (chunk:=Mint64);[reflexivity|].
    cbn [Mem.loadv].
    rewrite Ptrofs.unsigned_repr;[exact HL|].
    pose proof (Int.unsigned_range (Int.shru off (Int.repr 6))).
    unfold scalar_bits_index in *;lia.
Qed.

Lemma eval_scalar_bits_result e le m limb off count :
  le!_t'1=Some (Vlong limb) -> le!_offset=Some (Vint off) -> le!_count=Some (Vint count) ->
  Int.unsigned count<64 ->
  eval_expr secp_ge e le m scalar_bits_result_expr
    (Vlong (Int64.and (Int64.shru limb (Int64.repr (scalar_bits_shift off)))
      (Int64.sub (Int64.shl Int64.one (Int64.repr (Int.unsigned count))) Int64.one))).
Proof.
  intros HL HO HC Bound.
  assert (Count : Int.ltu count Int64.iwordsize'=true).
  { unfold Int.ltu;change (Int.unsigned Int64.iwordsize') with 64.
    apply zlt_true;exact Bound. }
  assert (Shift : Int.ltu (Int.and off (Int.repr 63)) Int64.iwordsize'=true).
  { unfold Int.ltu;change (Int.unsigned Int64.iwordsize') with 64.
    apply zlt_true;exact (proj2 (scalar_bits_shift_bound off)). }
  unfold scalar_bits_result_expr.
  eapply eval_Ebinop with
    (v1:=Vlong (Int64.shru limb (Int64.repr (scalar_bits_shift off))))
    (v2:=Vlong (Int64.sub (Int64.shl Int64.one (Int64.repr (Int.unsigned count))) Int64.one)).
  - eapply eval_Ebinop.
    + apply eval_Etempvar;exact HL.
    + eapply eval_Ebinop;[apply eval_Etempvar;exact HO|constructor|reflexivity].
    + change ((if Int.ltu (Int.and off (Int.repr 63)) Int64.iwordsize' then
        Some (Vlong (Int64.shru limb (Int64.repr (scalar_bits_shift off)))) else None)=
        Some (Vlong (Int64.shru limb (Int64.repr (scalar_bits_shift off))))).
      rewrite Shift;reflexivity.
  - eapply eval_Ebinop with
      (v1:=Vlong (Int64.shl Int64.one (Int64.repr (Int.unsigned count)))) (v2:=Vint Int.one).
    + eapply eval_Ebinop.
      * eapply eval_Ecast;[constructor|reflexivity].
      * apply eval_Etempvar;exact HC.
      * change ((if Int.ltu count Int64.iwordsize' then
          Some (Vlong (Int64.shl Int64.one (Int64.repr (Int.unsigned count)))) else None)=
          Some (Vlong (Int64.shl Int64.one (Int64.repr (Int.unsigned count))))).
        rewrite Count;reflexivity.
    + constructor.
    + reflexivity.
  - reflexivity.
Qed.

Lemma scalar_bits_index_numeric off : scalar_bits_index off=Int.unsigned off/64.
Proof.
  unfold scalar_bits_index;rewrite Int.shru_div_two_p.
  change (two_p (Int.unsigned (Int.repr 6))) with 64.
  apply Int.unsigned_repr.
  pose proof (Int.unsigned_range off) as Bound.
  split;[apply Z.div_pos;lia|].
  apply Z.div_le_upper_bound;[lia|];change Int.max_unsigned with 4294967295.
  change Int.modulus with 4294967296 in Bound;lia.
Qed.

Lemma scalar_bits_shift_numeric off : scalar_bits_shift off=Int.unsigned off mod 64.
Proof.
  unfold scalar_bits_shift.
  change (Int.repr 63) with (Int.repr (two_p 6-1)).
  rewrite <-Int.zero_ext_and by lia.
  exact (Int.zero_ext_mod 6 off ltac:(change (0<=6<32);lia)).
Qed.

Lemma scalar_bits_limb_value value i : 0<=value<2^256 -> 0<=i<4 ->
  nth (Z.to_nat i) (scalar_limbs_of value) 0=(value/2^(64*i)) mod 2^64.
Proof.
  intros Value Index.
  assert (Cases : i=0 \/ i=1 \/ i=2 \/ i=3) by lia.
  destruct Cases as [E|[E|[E|E]]];subst i.
  - change (value mod 2^64=(value/1) mod 2^64);rewrite Z.div_1_r;reflexivity.
  - reflexivity.
  - reflexivity.
  - change (value/2^192=(value/2^192) mod 2^64).
    symmetry;apply Z.mod_small;split;[apply Z.div_pos;lia|].
    apply Z.div_lt_upper_bound;[lia|].
    change (value<2^256);exact (proj2 Value).
Qed.

Theorem eval_scalar_get_bits m b base off count limb :
  0<=base -> base+8*scalar_bits_index off<=Ptrofs.max_unsigned -> Int.unsigned count<64 ->
  Mem.load Mint64 m b (base+8*scalar_bits_index off)=Some (Vlong limb) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_get_bits)
    [Vptr b (Ptrofs.repr base);Vint off;Vint count] E0 m
    (Vint (scalar_bits_result limb off count)).
Proof.
  intros HB HM Count Load.
  eapply eval_funcall_internal with (e:=empty_env)
    (le1:=scalar_bits_temps b base off count)
    (le2:=PTree.set _t'1 (Vlong limb) (scalar_bits_temps b base off count))
    (m1:=m) (m2:=m)
    (out:=Out_return (Some (Vlong (Int64.and
      (Int64.shru limb (Int64.repr (scalar_bits_shift off)))
      (Int64.sub (Int64.shl Int64.one (Int64.repr (Int.unsigned count))) Int64.one)),tulong))).
  - apply scalar_bits_entry.
  - rewrite scalar_bits_source.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=scalar_bits_temps b base off count).
    + eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m)
        (le1:=scalar_bits_temps b base off count) (out1:=Out_normal) (out2:=Out_break);constructor.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
        (le1:=PTree.set _t'1 (Vlong limb) (scalar_bits_temps b base off count)).
      * apply exec_Sset;eapply eval_scalar_bits_load with (b:=b) (base:=base) (off:=off);
          try reflexivity;assumption.
      * apply exec_Sreturn_some;apply eval_scalar_bits_result;try reflexivity;exact Count.
  - split;[discriminate|reflexivity].
  - reflexivity.
Qed.

Theorem eval_scalar_get_bits_slice m b base value off count :
  0<=value<2^256 -> 0<=off<256 -> 0<=count<=32 -> off mod 64+count<=64 ->
  scalar_at m b base (map Int64.repr (scalar_limbs_of value)) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_get_bits)
    [Vptr b (Ptrofs.repr base);Vint (Int.repr off);Vint (Int.repr count)] E0 m
    (Vint (Int.repr ((value/2^off) mod 2^count))).
Proof.
  intros Value Offset Count Within (Len & Base & Align & Max & Perm & Loads).
  assert (Off : Int.unsigned (Int.repr off)=off) by
    (apply Int.unsigned_repr;change Int.max_unsigned with 4294967295;lia).
  assert (Cnt : Int.unsigned (Int.repr count)=count) by
    (apply Int.unsigned_repr;change Int.max_unsigned with 4294967295;lia).
  assert (Index : 0<=off/64<4).
  { split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]. }
  assert (Nth : (Z.to_nat (off/64)<length (scalar_limbs_of value))%nat).
  { change (Z.to_nat (off/64)<4)%nat;apply Nat2Z.inj_lt;rewrite Z2Nat.id by lia;cbn;lia. }
  pose (limb := Int64.repr (nth (Z.to_nat (off/64)) (scalar_limbs_of value) 0)).
  assert (Loaded : Mem.load Mint64 m b (base+8*scalar_bits_index (Int.repr off))=Some (Vlong limb)).
  { rewrite scalar_bits_index_numeric,Off.
    rewrite <-(Z2Nat.id (off/64)) at 1 by lia.
    apply Loads;rewrite nth_error_map,(nth_error_nth' _ 0 Nth);reflexivity. }
  assert (Result : scalar_bits_result limb (Int.repr off) (Int.repr count)=
      Int.repr ((value/2^off) mod 2^count)).
  { rewrite scalar_bits_result_numeric by (rewrite Cnt;lia).
    rewrite scalar_bits_shift_numeric,Off,Cnt.
    unfold limb;rewrite Int64.unsigned_repr by (apply nth_u64_bound;apply scalar_limbs_bounds;exact Value).
    rewrite scalar_bits_limb_value by assumption.
    rewrite mod_div_mod by (pose proof (Z.mod_pos_bound off 64 ltac:(lia));lia).
    rewrite div_div_pow by (pose proof (Z.mod_pos_bound off 64 ltac:(lia));lia).
    pose proof (Z.div_mod off 64 ltac:(lia)) as Decompose.
    replace (64*(off/64)+off mod 64) with off by lia;reflexivity. }
  rewrite <-Result;apply eval_scalar_get_bits;try assumption.
  - rewrite scalar_bits_index_numeric,Off;lia.
  - rewrite Cnt;lia.
Qed.
