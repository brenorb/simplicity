(** Complete original window-5 loop and return against all 129 literal digits.
    Actual function entry, initial scalar/sign preparation and freeing remain
    outside this boundary; no body execution or final digits are assumed. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
From compcert Require Import Integers AST Maps Memory Values Events Clight ClightBigstep.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_signed C.jet_secp_wnaf_literal_array
 C.jet_sx_mem C.jet_secp_wnaf_slice_frame
 C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_signed_array
 C.jet_secp_wnaf_digit C.jet_secp_wnaf_control C.jet_secp_wnaf_loop
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric C.jet_secp_linkage C.jets_secp.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma exec_wnaf5_signed_loop_done le m bs carry sign b base last :
 wnaf_loop_fields le 129 129 5 carry sign b base last ->
 Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop E0 le m Out_normal.
Proof.
 intro Fields;rewrite wnaf_loop_body_source.
 eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
 eapply exec_Sseq_2;[|discriminate].
 eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=Datatypes.false);[|reflexivity|constructor].
 exact (eval_wnaf_loop_guard (wnaf_env bs) le m 129 129 ltac:(lia) ltac:(lia)
  (proj1 Fields) (proj1 (proj2 Fields))).
Qed.
Lemma exec_wnaf5_signed_loop_join le m bit carry sign b base last bs lei mi out lef mf :
 0<=bit<129 -> wnaf_loop_fields le bit 129 5 carry sign b base last ->
 Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop_body E0 lei mi out ->
 (out=Out_normal \/ out=Out_continue) ->
 Clight2.exec_stmt secp_ge (wnaf_env bs) lei mi wnaf_loop E0 lef mf Out_normal ->
 Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop E0 lef mf Out_normal.
Proof.
 intros HBit Fields Body Normal Rest;rewrite wnaf_loop_body_source in Rest|-*.
 eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0)
  (le1:=lei) (m1:=mi) (out1:=out) (le2:=lei) (m2:=mi).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m).
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=Datatypes.true);[|reflexivity|constructor].
     pose proof (eval_wnaf_loop_guard (wnaf_env bs) le m bit 129 ltac:(lia) ltac:(lia)
      (proj1 Fields) (proj1 (proj2 Fields))) as Guard.
     rewrite (proj2 (Z.ltb_lt bit 129) ltac:(lia)) in Guard;exact Guard.
   + exact Body.
 - destruct Normal as [E|E];subst out;constructor.
 - constructor.
 - exact Rest.
Qed.

Theorem exec_wnaf5_signed_loop_bounded fuel : forall le m n bit carry sign b base bs last digits sb word,
 129-bit<=Z.of_nat fuel -> 0<=n<2^129 -> 0<=bit<=129 ->
 (carry=0 \/ carry=1) -> (sign=1 \/ sign= -1) ->
 literal_wnaf_signed_value sb word=sign*(n/2^bit+carry) ->
 wnaf_loop_fields le bit 129 5 carry sign b base last ->
 scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) -> b<>bs ->
 0<=base -> base+4*129<=Ptrofs.max_unsigned ->
 wnaf_array_state m b base 129 5 sign bit last digits ->
 exists lef mf carryf lastf digitsf,
 Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop E0 lef mf Out_normal /\
 wnaf_loop_fields lef 129 129 5 carryf sign b base lastf /\ (carryf=0 \/ carryf=1) /\
 scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of n)) /\
 wnaf_array_state mf b base 129 5 sign 129 lastf digitsf /\ wnaf_memory_effect b m mf /\
 (forall i,0<=i<bit -> digitsf i=digits i) /\
 map wnaf5_literal_value (snd (literal_wnaf5_run (Z.to_nat (129-bit)) (sb,word)))=
  rev (map (fun d=>sign*d) (wnaf_slice (Z.to_nat (129-bit)) digitsf bit)) /\
 lframe (wnaf_slice_outside b base 129) m mf.
Proof.
 induction fuel as [|fuel IH];intros le m n bit carry sign b base bs last digits sb word
  Fuel N HBit Carry Sign Value Fields Storage Separate Base Max Array;
  destruct (Coqlib.zeq bit 129) as [Done|More].
 - subst bit;exists le,m,carry,last,digits;split;[eapply exec_wnaf5_signed_loop_done;exact Fields|];
   split;[exact Fields|];split;[exact Carry|];split;[exact Storage|];split;[exact Array|];
   split;[apply wnaf_memory_refl|];split;[intros;reflexivity|];
   split;[change (([]:list Z)=[]);reflexivity|apply lframe_refl].
 - change (129-bit<=0) in Fuel;lia.
 - subst bit;exists le,m,carry,last,digits;split;[eapply exec_wnaf5_signed_loop_done;exact Fields|];
   split;[exact Fields|];split;[exact Carry|];split;[exact Storage|];split;[exact Array|];
   split;[apply wnaf_memory_refl|];split;[intros;reflexivity|];
   split;[change (([]:list Z)=[]);reflexivity|apply lframe_refl].
 - destruct (exec_wnaf5_signed_array_step le m n bit carry sign b base bs last digits sb word
    N ltac:(lia) Carry Sign Value Fields Storage Separate Base Max Array)
    as (lei & mi & biti & carryi & lasti & digitsi & out & sbi & next & segment & Body & FieldsI
      & Advance & CarryI & StorageI & ArrayI & EffectI & Normal & Run & ValueI & Segment & PrefixI & SliceI).
   assert (FuelI:129-biti<=Z.of_nat fuel) by (rewrite Nat2Z.inj_succ in Fuel;lia).
   destruct (IH lei mi n biti carryi sign b base bs lasti digitsi sbi next FuelI N ltac:(lia)
    CarryI Sign ValueI FieldsI StorageI Separate Base Max ArrayI)
    as (lef & mf & carryf & lastf & digitsf & Rest & FieldsF & CarryF & StorageF & ArrayF
      & EffectF & PrefixF & DecodeF & SliceF).
   exists lef,mf,carryf,lastf,digitsf;split.
   + eapply exec_wnaf5_signed_loop_join with (bit:=bit) (carry:=carry) (sign:=sign)
      (b:=b) (base:=base) (last:=last);[lia|exact Fields|exact Body|exact Normal|exact Rest].
   + split;[exact FieldsF|];split;[exact CarryF|];split;[exact StorageF|];split;[exact ArrayF|];
      split;[eapply wnaf_memory_trans;eassumption|];split.
     * intros i Range;rewrite PrefixF by lia;apply PrefixI;exact Range.
     * split;[|eapply lframe_trans;[exact SliceI|exact SliceF]].
       assert (Count:Z.to_nat (129-bit)=(Z.to_nat (biti-bit)+Z.to_nat (129-biti))%nat).
       { rewrite <-Z2Nat.inj_add by lia;f_equal;lia. }
       assert (Start:bit+Z.of_nat (Z.to_nat (biti-bit))=biti) by (rewrite Z2Nat.id by lia;lia).
       assert (Slice:wnaf_slice (Z.to_nat (biti-bit)) digitsf bit=
        wnaf_slice (Z.to_nat (biti-bit)) digitsi bit).
       { apply wnaf_slice_ext;intros i Range;rewrite Z2Nat.id in Range by lia;apply PrefixF;lia. }
       rewrite Count,(wnaf5_literal_run_join _ _ _ _ _ Run).
       refine (eq_trans (f_equal2 (@app Z) DecodeF Segment) _).
       rewrite wnaf_slice_app,Start,map_app,rev_app_distr,Slice;reflexivity.
Qed.

Theorem exec_wnaf5_loop_zero_signed le m n sign b base bs sb word :
 0<=n<2^129 -> (sign=1 \/ sign= -1) -> literal_wnaf_signed_value sb word=sign*n ->
 wnaf_loop_fields le 0 129 5 0 sign b base (-1) ->
 scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) -> b<>bs ->
 0<=base -> base+4*129<=Ptrofs.max_unsigned ->
 (forall i,0<=i<129 -> Mem.valid_access m Mint32 b (base+4*i) Writable) ->
 (forall i,0<=i<129 -> Mem.load Mint32 m b (base+4*i)=Some (Vint Int.zero)) ->
 exists lef mf carry last digits,
 Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop_return E0 lef mf
  (Out_return (Some (Vint (Int.repr (last+1)),Ctypesdefs.tint))) /\
 wnaf_loop_fields lef 129 129 5 carry sign b base last /\ (carry=0 \/ carry=1) /\
 scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of n)) /\
 wnaf_array_state mf b base 129 5 sign 129 last digits /\
 0<=last+1<=129 /\ wnaf_memory_effect b m mf /\
 map wnaf5_literal_value (literal_wnaf5_digits (sb,word))=
  rev (map (fun i=>sign*digits (Z.of_nat i)) (seq 0 129)) /\
 lframe (wnaf_slice_outside b base 129) m mf.
Proof.
 intros N Sign Value Fields Storage Separate Base Max Access Load.
 assert (Array:wnaf_array_state m b base 129 5 sign 0 (-1) (fun _=>0)).
 { apply wnaf_array_zero;try assumption;lia. }
 assert (Initial:literal_wnaf_signed_value sb word=sign*(n/2^0+0)).
 { change (literal_wnaf_signed_value sb word=sign*(n/1+0));rewrite Z.div_1_r,Z.add_0_r;exact Value. }
 destruct (exec_wnaf5_signed_loop_bounded 129 le m n 0 0 sign b base bs (-1) (fun _=>0) sb word
  ltac:(lia) N ltac:(lia) ltac:(left;reflexivity) Sign Initial Fields Storage Separate Base Max Array)
  as (lef & mf & carry & last & digits & Loop & Final & Carry & StorageF & ArrayF
    & Effect & Prefix & Decode & SliceFrame).
 destruct (wnaf_array_last _ _ _ _ _ _ _ _ _ ArrayF) as (Range & Highest & Present).
 assert (Return:Clight2.exec_stmt secp_ge (wnaf_env bs) lef mf
  (snd (C.jet_secp_statement_prefix.split_statement_last (fn_body f_secp256k1_ecmult_wnaf))) E0
  lef mf (Out_return (Some (Vint (Int.repr (last+1)),Ctypesdefs.tint)))).
 { apply exec_wnaf_return;[lia|].
   destruct Final as (_ & _ & _ & _ & _ & _ & HT);exact HT. }
 exists lef,mf,carry,last,digits;split.
 - unfold wnaf_loop_return;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Loop|exact Return].
 - split;[exact Final|];split;[exact Carry|];split;[exact StorageF|];split;[exact ArrayF|];
    split;[lia|];split;[exact Effect|].
   split;[|exact SliceFrame].
   rewrite <-literal_wnaf5_digits_order.
   pose proof (wnaf_slice_seq 129 digits 0) as Slice.
   change (wnaf_slice 129 digits 0=map (fun i=>digits (Z.of_nat i)) (seq 0 129)) in Slice.
   change (map wnaf5_literal_value (snd (literal_wnaf5_run 129 (sb,word)))=
    rev (map (fun d:Z=>sign*d) (wnaf_slice 129 digits 0))) in Decode.
   rewrite Slice,map_map in Decode;exact Decode.
Qed.
