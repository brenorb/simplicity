(** The production cross-word scalar reader used by wNAF. This is a complete
    internal-helper result, not a public jet equivalence theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs
  ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_fns
  C.jet_secp_curve_statements C.jet_secp_scalar_get_bits
  C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
  C.jet_secp_signed62_numeric C.jet_secp_u128_word_shift C.jet_secp_fe_math.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_var_index_expr := Ebinop Oshr (Etempvar _offset tuint)
  (Econst_int (Int.repr 6) tint) tuint.
Definition scalar_var_array_expr ix := Ederef
  (Ebinop Oadd (Efield (Ederef (Etempvar _a (tptr (Tstruct __5826 noattr)))
    (Tstruct __5826 noattr)) _d (tarray tulong 4)) ix (tptr tulong)) tulong.
Definition scalar_var_high_expr := scalar_var_array_expr
  (Ebinop Oadd scalar_var_index_expr (Econst_int Int.one tint) tuint).
Definition scalar_var_guard := match fn_body f_secp256k1_scalar_get_bits_var with
  | Ssequence _ (Ssequence _ (Sifthenelse guard _ _))=>guard
  | _=>Econst_int Int.zero tint end.
Definition scalar_var_then := match fn_body f_secp256k1_scalar_get_bits_var with
  | Ssequence _ (Ssequence _ (Sifthenelse _ yes _))=>yes
  | _=>Sskip end.
Definition scalar_var_else := match fn_body f_secp256k1_scalar_get_bits_var with
  | Ssequence _ (Ssequence _ (Sifthenelse _ _ no))=>no
  | _=>Sskip end.
Definition scalar_var_result_expr := match scalar_var_else with
  | Ssequence _ (Ssequence _ (Ssequence _ (Sreturn (Some result))))=>result
  | _=>Econst_int Int.zero tint end.
Definition scalar_var_test off count := Int.eq
  (Int.shru (Int.sub (Int.add off count) Int.one) (Int.repr 6))
  (Int.shru off (Int.repr 6)).
Definition scalar_var_mask count := Int64.sub
  (Int64.shl Int64.one (Int64.repr (Int.unsigned count))) Int64.one.
Definition scalar_var_join lo hi off := Int64.or
  (Int64.shru lo (Int64.repr (scalar_bits_shift off)))
  (Int64.shl hi (Int64.repr (64-scalar_bits_shift off))).
Definition scalar_var_temps b base off count :=
  PTree.set _count (Vint count) (PTree.set _offset (Vint off)
    (PTree.set _a (Vptr b (Ptrofs.repr base))
      (create_undef_temps (fn_temps f_secp256k1_scalar_get_bits_var)))).

Lemma scalar_var_source : fn_body f_secp256k1_scalar_get_bits_var=
  Ssequence (Sloop Sskip Sbreak) (Ssequence (Sloop Sskip Sbreak)
    (Sifthenelse scalar_var_guard scalar_var_then scalar_var_else)).
Proof. reflexivity. Qed.
Lemma scalar_var_else_source : scalar_var_else=
  Ssequence (Sloop Sskip Sbreak) (Ssequence (Sset _t'2 scalar_bits_load_expr)
    (Ssequence (Sset _t'3 scalar_var_high_expr) (Sreturn (Some scalar_var_result_expr)))).
Proof. reflexivity. Qed.
Lemma scalar_var_then_source : scalar_var_then=
  Ssequence (curve_call _secp256k1_scalar_get_bits f_secp256k1_scalar_get_bits (Some _t'1)
    [Etempvar _a (tptr (Tstruct __5826 noattr));Etempvar _offset tuint;Etempvar _count tuint])
    (Sreturn (Some (Etempvar _t'1 tuint))).
Proof. reflexivity. Qed.
Local Opaque secp_ge.

Lemma scalar_var_join_value lo hi shift count : 0<shift<64 -> 0<=count<64 ->
  Int64.unsigned (Int64.and
    (Int64.or (Int64.shru lo (Int64.repr shift)) (Int64.shl hi (Int64.repr (64-shift))))
    (Int64.repr (2^count-1)))=
  ((Int64.unsigned lo+Int64.unsigned hi*2^64)/2^shift) mod 2^count.
Proof.
  intros Shift Count.
  rewrite repack_shifted_join_unsigned by
    (try lia;replace (shift+(64-shift)) with 64 by lia;apply Int64.unsigned_range).
  assert (Power : 2^64=2^(64-shift)*2^shift) by
    (rewrite <-Z.pow_add_r by lia;f_equal;lia).
  rewrite Power.
  replace (Int64.unsigned lo+Int64.unsigned hi*(2^(64-shift)*2^shift)) with
    (Int64.unsigned lo+(Int64.unsigned hi*2^(64-shift))*2^shift) by ring.
  rewrite Z.div_add by (apply Z.pow_nonzero;lia);reflexivity.
Qed.

Lemma scalar_var_two_limbs value i : 0<=value<2^256 -> 0<=i<3 ->
  nth (Z.to_nat i) (scalar_limbs_of value) 0+
    nth (Z.to_nat (i+1)) (scalar_limbs_of value) 0*2^64=
  (value/2^(64*i)) mod 2^128.
Proof.
  intros Value Index.
  rewrite !scalar_bits_limb_value by lia.
  replace (64*(i+1)) with (64*i+64) by ring.
  rewrite <-div_div_pow by lia.
  pose (t:=value/2^(64*i)).
  change (t mod 2^64+(t/2^64) mod 2^64*2^64=t mod 2^128).
  pose proof (Z.div_mod t (2^64) ltac:(lia)) as Decompose.
  replace t with (t mod 2^64+(t/2^64)*2^64) at 3 by lia.
  rewrite repack_join_mod by (pose proof (Z.mod_pos_bound t (2^64) ltac:(lia));lia).
  reflexivity.
Qed.

Lemma scalar_var_array_load e le m b base ix idx limb :
  le!_a=Some (Vptr b (Ptrofs.repr base)) -> typeof ix=tuint ->
  eval_expr secp_ge e le m ix (Vint idx) ->
  0<=base -> base+8*Int.unsigned idx<=Ptrofs.max_unsigned ->
  Mem.load Mint64 m b (base+8*Int.unsigned idx)=Some (Vlong limb) ->
  eval_expr secp_ge e le m (scalar_var_array_expr ix) (Vlong limb).
Proof.
  intros HA Ty Index Base Max Load.
  destruct scalar_bits_d_layout as (co & HC & HF).
  unfold scalar_var_array_expr.
  eapply eval_Elvalue with (loc:=b) (ofs:=Ptrofs.repr (base+8*Int.unsigned idx)).
  - apply eval_Ederef.
    eapply eval_Ebinop with (v1:=Vptr b (Ptrofs.repr base)) (v2:=Vint idx).
    + rewrite <-(Ptrofs.add_zero (Ptrofs.repr base)).
      eapply eval_Elvalue.
      * eapply eval_Efield_struct with (ofs:=Ptrofs.repr base) (delta:=0) (co:=co).
        -- eapply eval_Elvalue;[eapply eval_Ederef;apply eval_Etempvar;exact HA|].
           apply deref_loc_copy;reflexivity.
        -- reflexivity.
        -- exact HC.
        -- exact HF.
      * apply deref_loc_reference;reflexivity.
    + exact Index.
    + rewrite Ty.
      change (Some (Vptr b (Ptrofs.add (Ptrofs.repr base)
        (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_intu idx))))=
        Some (Vptr b (Ptrofs.repr (base+8*Int.unsigned idx)))).
      pose proof (Int.unsigned_range idx) as Bound;change Int.modulus with 4294967296 in Bound.
      unfold Ptrofs.of_intu,Ptrofs.of_int,Ptrofs.add,Ptrofs.mul.
      rewrite (Ptrofs.unsigned_repr 8) by (change Ptrofs.max_unsigned with 18446744073709551615;lia).
      rewrite (Ptrofs.unsigned_repr (Int.unsigned idx)) by
        (change Ptrofs.max_unsigned with 18446744073709551615;lia).
      rewrite (Ptrofs.unsigned_repr (8*Int.unsigned idx)) by
        (change Ptrofs.max_unsigned with 18446744073709551615;lia).
      rewrite (Ptrofs.unsigned_repr base) by
        (change Ptrofs.max_unsigned with 18446744073709551615 in *;lia);reflexivity.
  - apply deref_loc_value with (chunk:=Mint64);[reflexivity|].
    cbn [Mem.loadv];rewrite Ptrofs.unsigned_repr;[exact Load|].
    pose proof (Int.unsigned_range idx);lia.
Qed.

Lemma scalar_var_entry m b base off count :
  function_entry2 secp_ge f_secp256k1_scalar_get_bits_var
    [Vptr b (Ptrofs.repr base);Vint off;Vint count] m empty_env
    (scalar_var_temps b base off count) m.
Proof.
  assert (OK : fn_okb f_secp256k1_scalar_get_bits_var=true) by reflexivity.
  destruct (fn_okb_true _ OK) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD|constructor|reflexivity].
Qed.

Lemma eval_scalar_var_guard e le m off count :
  le!_offset=Some (Vint off) -> le!_count=Some (Vint count) ->
  eval_expr secp_ge e le m scalar_var_guard (Val.of_bool (scalar_var_test off count)).
Proof.
  intros HO HC;unfold scalar_var_guard,scalar_var_test.
  eapply eval_Ebinop.
  - eapply eval_Ebinop.
    + eapply eval_Ebinop.
      * eapply eval_Ebinop;[apply eval_Etempvar;exact HO|apply eval_Etempvar;exact HC|reflexivity].
      * constructor.
      * reflexivity.
    + constructor.
    + reflexivity.
  - eapply eval_Ebinop;[apply eval_Etempvar;exact HO|constructor|reflexivity].
  - reflexivity.
Qed.

Lemma scalar_var_test_numeric off count : 0<=off<256 -> 1<=count<32 ->
  scalar_var_test (Int.repr off) (Int.repr count)=
    (if zeq ((off+count-1)/64) (off/64) then true else false).
Proof.
  intros Offset Count.
  assert (HO : Int.unsigned (Int.repr off)=off) by
    (apply Int.unsigned_repr;change Int.max_unsigned with 4294967295;lia).
  assert (HC : Int.unsigned (Int.repr count)=count) by
    (apply Int.unsigned_repr;change Int.max_unsigned with 4294967295;lia).
  assert (Sum : Int.add (Int.repr off) (Int.repr count)=Int.repr (off+count)).
  { unfold Int.add;rewrite HO,HC;reflexivity. }
  assert (Sub : Int.sub (Int.add (Int.repr off) (Int.repr count)) Int.one=
    Int.repr (off+count-1)).
  { rewrite Sum;unfold Int.sub;rewrite Int.unsigned_repr by
      (change Int.max_unsigned with 4294967295;lia);reflexivity. }
  unfold scalar_var_test;rewrite Sub;unfold Int.eq;fold scalar_bits_index.
  change ((if zeq (scalar_bits_index (Int.repr (off+count-1)))
    (scalar_bits_index (Int.repr off)) then true else false)=
    (if zeq ((off+count-1)/64) (off/64) then true else false)).
  rewrite !scalar_bits_index_numeric,HO,Int.unsigned_repr by
    (change Int.max_unsigned with 4294967295;lia);reflexivity.
Qed.

Lemma scalar_var_branch_bounds off count : 0<=off<256 -> 1<=count<32 -> off+count<=256 ->
  (off+count-1)/64=off/64 -> off mod 64+count<=64.
Proof.
  intros Offset Count End Same.
  pose proof (Z.div_mod off 64 ltac:(lia)).
  pose proof (Z.mod_pos_bound off 64 ltac:(lia)).
  pose proof (Z.div_mod (off+count-1) 64 ltac:(lia)).
  pose proof (Z.mod_pos_bound (off+count-1) 64 ltac:(lia));nia.
Qed.

Lemma scalar_var_cross_bounds off count : 0<=off<256 -> 1<=count<32 -> off+count<=256 ->
  (off+count-1)/64<>off/64 -> 0<off mod 64<64 /\ 0<=off/64<3.
Proof.
  intros Offset Count End Cross.
  pose proof (Z.div_mod off 64 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound off 64 ltac:(lia)) as R.
  assert (I : 0<=off/64<4) by
    (split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]).
  assert (Boundary : 64<off mod 64+count).
  { apply Z.nle_gt;intro Fits;apply Cross.
    replace (off+count-1) with ((off mod 64+count-1)+(off/64)*64) by nia.
    rewrite Z.div_add by lia;rewrite Z.div_small by lia;lia. }
  split;split;nia.
Qed.

Lemma eval_scalar_var_high e le m b base off hi :
  le!_a=Some (Vptr b (Ptrofs.repr base)) -> le!_offset=Some (Vint (Int.repr off)) ->
  0<=off<256 -> 0<=base -> base+8*(off/64+1)<=Ptrofs.max_unsigned ->
  Mem.load Mint64 m b (base+8*(off/64+1))=Some (Vlong hi) ->
  eval_expr secp_ge e le m scalar_var_high_expr (Vlong hi).
Proof.
  intros HA HO Offset Base Max Load.
  assert (Off : Int.unsigned (Int.repr off)=off) by
    (apply Int.unsigned_repr;change Int.max_unsigned with 4294967295;lia).
  assert (Index : 0<=off/64<4) by
    (split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]).
  assert (Next : Int.unsigned (Int.repr (off/64+1))=off/64+1) by
    (apply Int.unsigned_repr;change Int.max_unsigned with 4294967295;lia).
  unfold scalar_var_high_expr.
  apply scalar_var_array_load with (b:=b) (base:=base) (idx:=Int.repr (off/64+1));
    try assumption;try reflexivity;try (rewrite Next;assumption).
  unfold scalar_var_index_expr;eapply eval_Ebinop.
  - eapply eval_Ebinop;[apply eval_Etempvar;exact HO|constructor|reflexivity].
  - constructor.
  - change (Some (Vint (Int.add (Int.shru (Int.repr off) (Int.repr 6)) Int.one))=
      Some (Vint (Int.repr (off/64+1)))).
    change (Some (Vint (Int.repr (scalar_bits_index (Int.repr off)+1)))=
      Some (Vint (Int.repr (off/64+1)))).
    rewrite scalar_bits_index_numeric,Off;reflexivity.
Qed.

Lemma eval_scalar_var_result e le m lo hi off count :
  le!_t'2=Some (Vlong lo) -> le!_t'3=Some (Vlong hi) ->
  le!_offset=Some (Vint off) -> le!_count=Some (Vint count) ->
  0<scalar_bits_shift off<64 -> Int.unsigned count<64 ->
  eval_expr secp_ge e le m scalar_var_result_expr
    (Vlong (Int64.and (scalar_var_join lo hi off) (scalar_var_mask count))).
Proof.
  intros Lo Hi Off Cnt Shift Count.
  assert (Complement : Int.unsigned (Int.sub (Int.repr 64) (Int.and off (Int.repr 63)))=
    64-scalar_bits_shift off).
  { change (Int.unsigned (Int.repr (64-scalar_bits_shift off))=64-scalar_bits_shift off).
    apply Int.unsigned_repr;change Int.max_unsigned with 4294967295;lia. }
  assert (LShift : Int.ltu (Int.and off (Int.repr 63)) Int64.iwordsize'=true).
  { unfold Int.ltu;change (Int.unsigned Int64.iwordsize') with 64;apply zlt_true;exact (proj2 Shift). }
  assert (RShift : Int.ltu (Int.sub (Int.repr 64) (Int.and off (Int.repr 63))) Int64.iwordsize'=true).
  { unfold Int.ltu;change (Int.unsigned Int64.iwordsize') with 64;rewrite Complement;apply zlt_true;lia. }
  assert (CShift : Int.ltu count Int64.iwordsize'=true).
  { unfold Int.ltu;change (Int.unsigned Int64.iwordsize') with 64;apply zlt_true;exact Count. }
  unfold scalar_var_result_expr.
  eapply eval_Ebinop with (v1:=Vlong (scalar_var_join lo hi off)) (v2:=Vlong (scalar_var_mask count)).
  - unfold scalar_var_join;eapply eval_Ebinop with
      (v1:=Vlong (Int64.shru lo (Int64.repr (scalar_bits_shift off))))
      (v2:=Vlong (Int64.shl hi (Int64.repr (64-scalar_bits_shift off)))).
    + eapply eval_Ebinop.
      * apply eval_Etempvar;exact Lo.
      * eapply eval_Ebinop;[apply eval_Etempvar;exact Off|constructor|reflexivity].
      * change ((if Int.ltu (Int.and off (Int.repr 63)) Int64.iwordsize' then
          Some (Vlong (Int64.shru lo (Int64.repr (scalar_bits_shift off)))) else None)=
          Some (Vlong (Int64.shru lo (Int64.repr (scalar_bits_shift off))))).
        rewrite LShift;reflexivity.
    + eapply eval_Ebinop.
      * apply eval_Etempvar;exact Hi.
      * eapply eval_Ebinop.
        -- constructor.
        -- eapply eval_Ebinop;[apply eval_Etempvar;exact Off|constructor|reflexivity].
        -- reflexivity.
      * change ((if Int.ltu (Int.sub (Int.repr 64) (Int.and off (Int.repr 63))) Int64.iwordsize'
          then Some (Vlong (Int64.shl hi
            (Int64.repr (Int.unsigned (Int.sub (Int.repr 64) (Int.and off (Int.repr 63))))))) else None)=
          Some (Vlong (Int64.shl hi (Int64.repr (64-scalar_bits_shift off))))).
        rewrite RShift,Complement;reflexivity.
    + reflexivity.
  - unfold scalar_var_mask;eapply eval_Ebinop with
      (v1:=Vlong (Int64.shl Int64.one (Int64.repr (Int.unsigned count)))) (v2:=Vint Int.one).
    + eapply eval_Ebinop.
      * eapply eval_Ecast;[constructor|reflexivity].
      * apply eval_Etempvar;exact Cnt.
      * change ((if Int.ltu count Int64.iwordsize' then
          Some (Vlong (Int64.shl Int64.one (Int64.repr (Int.unsigned count)))) else None)=
          Some (Vlong (Int64.shl Int64.one (Int64.repr (Int.unsigned count))))).
        rewrite CShift;reflexivity.
    + constructor.
    + reflexivity.
  - reflexivity.
Qed.

Lemma scalar_var_result_numeric value off count lo hi :
  0<=value<2^256 -> 0<=off<256 -> 1<=count<32 -> off+count<=256 ->
  (off+count-1)/64<>off/64 ->
  Int64.unsigned lo=nth (Z.to_nat (off/64)) (scalar_limbs_of value) 0 ->
  Int64.unsigned hi=nth (Z.to_nat (off/64+1)) (scalar_limbs_of value) 0 ->
  Int64.loword (Int64.and (scalar_var_join lo hi (Int.repr off)) (scalar_var_mask (Int.repr count)))=
    Int.repr ((value/2^off) mod 2^count).
Proof.
  intros Value Offset Count End Cross Lo Hi.
  destruct (scalar_var_cross_bounds off count Offset Count End Cross) as (Shift & Index).
  assert (Off : Int.unsigned (Int.repr off)=off) by
    (apply Int.unsigned_repr;change Int.max_unsigned with 4294967295;lia).
  assert (Cnt : Int.unsigned (Int.repr count)=count) by
    (apply Int.unsigned_repr;change Int.max_unsigned with 4294967295;lia).
  unfold scalar_var_join,scalar_var_mask,Int64.loword.
  rewrite scalar_bits_mask by (rewrite Cnt;lia).
  rewrite scalar_bits_shift_numeric,Off,Cnt.
  rewrite scalar_var_join_value by lia.
  rewrite Lo,Hi,scalar_var_two_limbs by assumption.
  rewrite mod_div_mod by lia.
  rewrite div_div_pow by lia.
  pose proof (Z.div_mod off 64 ltac:(lia)).
  replace (64*(off/64)+off mod 64) with off by lia;reflexivity.
Qed.

Lemma eval_scalar_var_then le m b base off count result :
  le!_a=Some (Vptr b (Ptrofs.repr base)) -> le!_offset=Some (Vint off) ->
  le!_count=Some (Vint count) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_get_bits)
    [Vptr b (Ptrofs.repr base);Vint off;Vint count] E0 m (Vint result) ->
  Clight2.exec_stmt secp_ge empty_env le m scalar_var_then E0
    (PTree.set _t'1 (Vint result) le) m (Out_return (Some (Vint result,tuint))).
Proof.
  intros HA HO HC Call;rewrite scalar_var_then_source.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'1 (Vint result) le).
  - eapply exec_curve_call with (vargs:=[Vptr b (Ptrofs.repr base);Vint off;Vint count]) (v:=Vint result).
    + unfold secp_pure;repeat (first [left;reflexivity|right]).
    + reflexivity.
    + eapply eval_Econs;[apply eval_Etempvar;exact HA|reflexivity|].
      eapply eval_Econs;[apply eval_Etempvar;exact HO|reflexivity|].
      eapply eval_Econs;[apply eval_Etempvar;exact HC|reflexivity|constructor].
    + exact Call.
  - apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
Qed.

Lemma eval_scalar_var_from_branch m b base off count le out result :
  Clight2.exec_stmt secp_ge empty_env (scalar_var_temps b base off count) m
    (if scalar_var_test off count then scalar_var_then else scalar_var_else) E0 le m out ->
  outcome_result_value out tuint (Vint result) m ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_get_bits_var)
    [Vptr b (Ptrofs.repr base);Vint off;Vint count] E0 m (Vint result).
Proof.
  intros Branch Return.
  eapply eval_funcall_internal with (e:=empty_env) (le1:=scalar_var_temps b base off count)
    (le2:=le) (m1:=m) (m2:=m) (out:=out).
  - apply scalar_var_entry.
  - rewrite scalar_var_source.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=scalar_var_temps b base off count).
    + eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m)
        (le1:=scalar_var_temps b base off count) (out1:=Out_normal) (out2:=Out_break);constructor.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=scalar_var_temps b base off count).
      * eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m)
          (le1:=scalar_var_temps b base off count) (out1:=Out_normal) (out2:=Out_break);constructor.
      * eapply exec_Sifthenelse with (v1:=Val.of_bool (scalar_var_test off count))
          (b:=scalar_var_test off count).
        -- apply eval_scalar_var_guard;reflexivity.
        -- destruct (scalar_var_test off count);reflexivity.
        -- exact Branch.
  - exact Return.
  - reflexivity.
Qed.

Lemma exec_scalar_var_else m le b base off count lo hi :
  le!_a=Some (Vptr b (Ptrofs.repr base)) -> le!_offset=Some (Vint (Int.repr off)) ->
  le!_count=Some (Vint count) ->
  0<=off<256 -> 0<off mod 64<64 -> Int.unsigned count<64 ->
  0<=base -> base+8*(off/64+1)<=Ptrofs.max_unsigned ->
  Mem.load Mint64 m b (base+8*(off/64))=Some (Vlong lo) ->
  Mem.load Mint64 m b (base+8*(off/64+1))=Some (Vlong hi) ->
  Clight2.exec_stmt secp_ge empty_env le m scalar_var_else E0
    (PTree.set _t'3 (Vlong hi) (PTree.set _t'2 (Vlong lo) le)) m
    (Out_return (Some (Vlong (Int64.and (scalar_var_join lo hi (Int.repr off))
      (scalar_var_mask count)),tulong))).
Proof.
  intros HA HO HC Offset Shift Count Base Max Lo Hi.
  assert (Off : Int.unsigned (Int.repr off)=off) by
    (apply Int.unsigned_repr;change Int.max_unsigned with 4294967295;lia).
  rewrite scalar_var_else_source.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le).
  - eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le)
      (out1:=Out_normal) (out2:=Out_break);constructor.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'2 (Vlong lo) le).
    + apply exec_Sset;eapply eval_scalar_bits_load with (b:=b) (base:=base) (off:=Int.repr off);
        try assumption;rewrite scalar_bits_index_numeric,Off;try assumption;lia.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
        (le1:=PTree.set _t'3 (Vlong hi) (PTree.set _t'2 (Vlong lo) le)).
      * apply exec_Sset;eapply eval_scalar_var_high with (b:=b) (base:=base) (off:=off);
          try assumption;rewrite PTree.gso by discriminate;assumption.
      * apply exec_Sreturn_some;apply eval_scalar_var_result.
        -- rewrite PTree.gso by discriminate;apply PTree.gss.
        -- apply PTree.gss.
        -- rewrite !PTree.gso by discriminate;exact HO.
        -- rewrite !PTree.gso by discriminate;exact HC.
        -- rewrite scalar_bits_shift_numeric,Off;exact Shift.
        -- exact Count.
Qed.

Lemma scalar_var_storage_limb m b base value i :
  scalar_at m b base (map Int64.repr (scalar_limbs_of value)) -> 0<=i<4 ->
  Mem.load Mint64 m b (base+8*i)=
    Some (Vlong (Int64.repr (nth (Z.to_nat i) (scalar_limbs_of value) 0))).
Proof.
  intros (Len & Base & Align & Max & Perm & Loads) Index.
  rewrite <-(Z2Nat.id i) at 1 by lia.
  apply Loads;rewrite nth_error_map,(nth_error_nth' _ 0);[reflexivity|].
  change (Z.to_nat i<4)%nat;apply Nat2Z.inj_lt;rewrite Z2Nat.id by lia;cbn;lia.
Qed.

Theorem eval_scalar_get_bits_var_slice m b base value off count :
  0<=value<2^256 -> 0<=off<256 -> 1<=count<32 -> off+count<=256 ->
  scalar_at m b base (map Int64.repr (scalar_limbs_of value)) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_get_bits_var)
    [Vptr b (Ptrofs.repr base);Vint (Int.repr off);Vint (Int.repr count)] E0 m
    (Vint (Int.repr ((value/2^off) mod 2^count))).
Proof.
  intros Value Offset Count End Storage.
  destruct (zeq ((off+count-1)/64) (off/64)) as [Same|Cross].
  - assert (Test : scalar_var_test (Int.repr off) (Int.repr count)=true).
    { rewrite scalar_var_test_numeric by assumption;destruct zeq;congruence. }
    eapply eval_scalar_var_from_branch with
      (out:=Out_return (Some (Vint (Int.repr ((value/2^off) mod 2^count)),tuint))).
    + rewrite Test;apply eval_scalar_var_then with (b:=b) (base:=base)
        (off:=Int.repr off) (count:=Int.repr count);try reflexivity.
      apply eval_scalar_get_bits_slice;try assumption;try lia.
      eapply scalar_var_branch_bounds;assumption.
    + split;[discriminate|reflexivity].
  - destruct (scalar_var_cross_bounds off count Offset Count End Cross) as (Shift & Index).
    assert (Test : scalar_var_test (Int.repr off) (Int.repr count)=false).
    { rewrite scalar_var_test_numeric by assumption;destruct zeq;congruence. }
    pose (lo:=Int64.repr (nth (Z.to_nat (off/64)) (scalar_limbs_of value) 0)).
    pose (hi:=Int64.repr (nth (Z.to_nat (off/64+1)) (scalar_limbs_of value) 0)).
    assert (Lo : Mem.load Mint64 m b (base+8*(off/64))=Some (Vlong lo)) by
      (apply scalar_var_storage_limb;[exact Storage|lia]).
    assert (Hi : Mem.load Mint64 m b (base+8*(off/64+1))=Some (Vlong hi)) by
      (apply scalar_var_storage_limb;[exact Storage|lia]).
    assert (Result : Int64.loword (Int64.and (scalar_var_join lo hi (Int.repr off))
      (scalar_var_mask (Int.repr count)))=Int.repr ((value/2^off) mod 2^count)).
    { apply scalar_var_result_numeric with (value:=value);try assumption;
        unfold lo,hi;apply Int64.unsigned_repr;apply nth_u64_bound;apply scalar_limbs_bounds;exact Value. }
    destruct Storage as (Len & Base & Align & Max & Perm & Loads).
    eapply eval_scalar_var_from_branch with (out:=Out_return (Some
      (Vlong (Int64.and (scalar_var_join lo hi (Int.repr off)) (scalar_var_mask (Int.repr count))),tulong))).
    + rewrite Test;apply exec_scalar_var_else with (b:=b) (base:=base) (off:=off);
        try reflexivity;try assumption;try lia.
      rewrite Int.unsigned_repr;[lia|change Int.max_unsigned with 4294967295;lia].
    + split;[discriminate|].
      change (Some (Vint (Int64.loword (Int64.and (scalar_var_join lo hi (Int.repr off))
        (scalar_var_mask (Int.repr count)))))=Some (Vint (Int.repr ((value/2^off) mod 2^count)))).
      rewrite Result;reflexivity.
Qed.
