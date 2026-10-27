(** Original bit-383 load and conditional-add call. The bit is taken from
    the retained full product, never assumed as a desired rounding result. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_secp_scalar_shift384_control C.jet_secp_scalar_shift384_stores C.jet_secp_statement_prefix
 C.jet_secp_u128_word_shift C.jet_secp_signed62_numeric.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition shift384_round_word word := Int64.and (Int64.shru word (Int64.repr 63)) Int64.one.
Definition shift384_round_flag word := Z.eqb (Int64.unsigned word/2^63) 1.
Lemma shift384_round_bounds word : 0<=Int64.unsigned word/2^63<2.
Proof.
 pose proof (Int64.unsigned_range word) as Range;change Int64.modulus with (2^64) in Range.
 split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia].
Qed.
Lemma shift384_round_value word :
 shift384_round_word word=(if shift384_round_flag word then Int64.one else Int64.zero) /\
 (if shift384_round_flag word then 1 else 0)=Int64.unsigned word/2^63.
Proof.
 pose proof (shift384_round_bounds word) as Bound.
 pose proof (uns_shru word 63 ltac:(lia)) as Shift.
 pose proof (Int64.repr_unsigned (Int64.shru word (Int64.repr 63))) as Word.
 rewrite Shift in Word;unfold shift384_round_word,shift384_round_flag.
 assert (Cases:Int64.unsigned word/2^63=0 \/ Int64.unsigned word/2^63=1) by lia.
 destruct Cases as [Zero|One];rewrite ?Zero,?One in *;rewrite <-Word;split;reflexivity.
Qed.

Local Ltac round_lookup := first [eassumption|apply PTree.gss|rewrite PTree.gso by discriminate;round_lookup].
Local Ltac round_expr := first [apply eval_Etempvar;round_lookup|apply eval_Econst_int|
 eapply eval_Ebinop;[round_expr|round_expr|reflexivity]].

Theorem exec_shift384_round_load e le m bl word : e!_l=Some (bl,tarray tulong 8) ->
 le!_shift=Some (Vint (Int.repr 384)) -> Mem.load Mint64 m bl 40=Some (Vlong word) ->
 Clight2.exec_stmt secp_ge e le m shift384_round_load E0 (PTree.set _t'11 (Vlong word) le) m Out_normal.
Proof.
 intros Local Shift Load;apply exec_Sset.
 eapply eval_Elvalue with (loc:=bl) (ofs:=Ptrofs.repr 40).
 - apply eval_Ederef;eapply eval_Ebinop with (v1:=Vptr bl Ptrofs.zero) (v2:=Vint (Int.repr 5)).
   + eapply eval_Elvalue;[apply eval_Evar_local;exact Local|apply deref_loc_reference;reflexivity].
   + round_expr.
   + reflexivity.
 - apply deref_loc_value with (chunk:=Mint64);[reflexivity|exact Load].
Qed.

Theorem exec_shift384_round_call e le m mf br word : e!_secp256k1_scalar_cadd_bit=None ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_shift=Some (Vint (Int.repr 384)) -> le!_t'11=Some (Vlong word) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_cadd_bit)
  [Vptr br Ptrofs.zero;Vint Int.zero;Vint (if shift384_round_flag word then Int.one else Int.zero)] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m shift384_round_call E0 le mf Out_normal.
Proof.
 intros Global R Shift Word Call.
 change (Clight2.exec_stmt secp_ge e le m
  (curve_call _secp256k1_scalar_cadd_bit f_secp256k1_scalar_cadd_bit None
  [Etempvar _r (tptr (Tstruct __5826 noattr));Econst_int Int.zero tint;
   Ebinop Oand (Ebinop Oshr (Etempvar _t'11 tulong)
    (Ebinop Oand (Ebinop Osub (Etempvar _shift tuint) (Econst_int Int.one tint) tuint)
     (Econst_int (Int.repr 63) tint) tuint) tulong) (Econst_int Int.one tint) tulong]) E0 le mf Out_normal).
 eapply (exec_curve_call _secp256k1_scalar_cadd_bit f_secp256k1_scalar_cadd_bit None _
  [Vptr br Ptrofs.zero;Vint Int.zero;Vint (if shift384_round_flag word then Int.one else Int.zero)] Vundef).
 - unfold secp_pure;repeat (first [left;reflexivity|right]).
 - exact Global.
 - eapply eval_Econs;[apply eval_Etempvar;exact R|reflexivity|].
   eapply eval_Econs;[constructor|reflexivity|].
   eapply eval_Econs with (v1:=Vlong (shift384_round_word word));[| |constructor].
   + eapply eval_Ebinop with (v1:=Vlong (Int64.shru word (Int64.repr 63))) (v2:=Vint Int.one).
     * eapply eval_Ebinop with (v1:=Vlong word) (v2:=Vint (Int.repr 63));
       [apply eval_Etempvar;exact Word|round_expr|reflexivity].
     * constructor.
     * reflexivity.
   + rewrite (proj1 (shift384_round_value word));destruct (shift384_round_flag word);reflexivity.
 - exact Call.
Qed.
