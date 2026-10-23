(** Original wNAF entry and preparation at the generator's actual 129/15 call.
    Stops before the original external memset; no zeroing law is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Cop Clight Clightdefs ClightBigstep Integers Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix.
Require Import C.jet_secp_wnaf_digit C.jet_secp_wnaf_control C.jet_secp_wnaf_prepare.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition wnaf_entry15_temps b base a :=
 PTree.set _w (Vint (Int.repr 15)) (PTree.set _a a (PTree.set _len (Vint (Int.repr 129))
 (PTree.set _wnaf (Vptr b (Ptrofs.repr base)) (create_undef_temps (fn_temps f_secp256k1_ecmult_wnaf))))).
Definition wnaf_before_temps le :=
 PTree.set _carry (Vint Int.zero) (PTree.set _sign (Vint Int.one)
 (PTree.set _bit (Vint Int.zero) (PTree.set _last_set_bit (Vint (Int.repr (-1))) le))).
Definition wnaf_before_memset := statement_sequence (firstn 8 wnaf_statements) Sskip.
Definition wnaf_memset_call := nth 8 wnaf_statements Sskip.
Definition wnaf_memset_args := match wnaf_memset_call with Scall _ _ args=>args | _=>[] end.
Definition wnaf_at_memset := Ssequence wnaf_memset_call wnaf_post_memset.

Lemma wnaf_entry15_ok : fn_okb f_secp256k1_ecmult_wnaf=true.
Proof. reflexivity. Qed.
Lemma wnaf_before_source tail : statement_sequence (firstn 8 wnaf_statements) tail=
 Ssequence (Sset _last_set_bit (Eunop Oneg (Econst_int Int.one tint) tint))
 (Ssequence (Sset _bit (Econst_int Int.zero tint))
 (Ssequence (Sset _sign (Econst_int Int.one tint))
 (Ssequence (Sset _carry (Econst_int Int.zero tint))
 (Ssequence (Sloop Sskip Sbreak)
 (Ssequence (Sloop (Sifthenelse (Ebinop Ole (Econst_int Int.zero tint) (Etempvar _len tint) tint) Sskip Sskip) Sbreak)
 (Ssequence (Sloop Sskip Sbreak)
 (Ssequence (Sloop (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 2) tint) (Etempvar _w tint) tint) Sskip Sskip) Sbreak)
 tail))))))).
Proof. reflexivity. Qed.
Lemma wnaf_body_to_memset_source : fn_body f_secp256k1_ecmult_wnaf=
 statement_sequence (firstn 8 wnaf_statements) wnaf_at_memset.
Proof. reflexivity. Qed.
Lemma wnaf_memset_call_source : wnaf_memset_call=Scall None
 (Evar _memset (Tfunction (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid) cc_default))
 [Etempvar _wnaf (tptr tint);Econst_int Int.zero tint;
  Ebinop Omul (Etempvar _len tint) (Esizeof tint tulong) tulong].
Proof. reflexivity. Qed.

Lemma wnaf_entry15 m mi bs b base a : Mem.alloc m 0 32=(mi,bs) ->
 function_entry2 secp_ge f_secp256k1_ecmult_wnaf
 [Vptr b (Ptrofs.repr base);Vint (Int.repr 129);a;Vint (Int.repr 15)] m
 (wnaf_env bs) (wnaf_entry15_temps b base a) mi.
Proof.
 intro Alloc;destruct (fn_okb_true _ wnaf_entry15_ok) as (Vars & Params & Disjoint).
 constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
 eapply alloc_variables_cons with (m1:=mi) (b1:=bs);[exact Alloc|constructor].
Qed.

Lemma wnaf_before_preserves le id : id<>_carry -> id<>_sign -> id<>_bit -> id<>_last_set_bit ->
 (wnaf_before_temps le)!id=le!id.
Proof.
 intros Carry Sign Bit Last;unfold wnaf_before_temps.
 rewrite PTree.gso by exact Carry;rewrite PTree.gso by exact Sign;
 rewrite PTree.gso by exact Bit;rewrite PTree.gso by exact Last;reflexivity.
Qed.

Theorem exec_wnaf_before_memset15 e le m :
 le!_len=Some (Vint (Int.repr 129)) -> le!_w=Some (Vint (Int.repr 15)) ->
 Clight2.exec_stmt secp_ge e le m wnaf_before_memset E0 (wnaf_before_temps le) m Out_normal.
Proof.
 intros Len W;unfold wnaf_before_memset;rewrite wnaf_before_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_Sset;eapply eval_Eunop;[constructor|reflexivity]|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_Sset;constructor|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_Sset;constructor|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_Sset;constructor|].
 change (Clight2.exec_stmt secp_ge e (wnaf_before_temps le) m
  (Ssequence (Sloop Sskip Sbreak)
   (Ssequence (Sloop (Sifthenelse (Ebinop Ole (Econst_int Int.zero tint) (Etempvar _len tint) tint) Sskip Sskip) Sbreak)
    (Ssequence (Sloop Sskip Sbreak)
     (Ssequence (Sloop (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 2) tint) (Etempvar _w tint) tint) Sskip Sskip) Sbreak) Sskip))))
  E0 (wnaf_before_temps le) m Out_normal).
 assert (LenReady:(wnaf_before_temps le)!_len=Some (Vint (Int.repr 129)))
  by (rewrite wnaf_before_preserves by discriminate;exact Len).
 assert (WReady:(wnaf_before_temps le)!_w=Some (Vint (Int.repr 15)))
  by (rewrite wnaf_before_preserves by discriminate;exact W).
 repeat eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=wnaf_before_temps le).
 - eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (out1:=Out_normal) (out2:=Out_break);constructor.
 - eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (out1:=Out_normal) (out2:=Out_break);[|constructor|constructor|constructor].
   eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|constructor].
   eapply eval_Ebinop with (v1:=Vint Int.zero) (v2:=Vint (Int.repr 129));
    [constructor|apply eval_Etempvar;exact LenReady|reflexivity].
 - eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (out1:=Out_normal) (out2:=Out_break);constructor.
 - eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (out1:=Out_normal) (out2:=Out_break);[|constructor|constructor|constructor].
   eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|constructor].
   eapply eval_Ebinop with (v1:=Vint (Int.repr 2)) (v2:=Vint (Int.repr 15));
    [constructor|apply eval_Etempvar;exact WReady|reflexivity].
 - constructor.
Qed.

Lemma wnaf_memset_arguments15 e le m b base :
 le!_wnaf=Some (Vptr b (Ptrofs.repr base)) -> le!_len=Some (Vint (Int.repr 129)) ->
 eval_exprlist secp_ge e le m wnaf_memset_args
 (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil)))
 [Vptr b (Ptrofs.repr base);Vint Int.zero;Vlong (Int64.repr 516)].
Proof.
 intros Pointer Len;unfold wnaf_memset_args;rewrite wnaf_memset_call_source.
 eapply eval_Econs with (v1:=Vptr b (Ptrofs.repr base));[apply eval_Etempvar;exact Pointer|reflexivity|].
 eapply eval_Econs with (v1:=Vint Int.zero);[constructor|reflexivity|].
 eapply eval_Econs with (v1:=Vlong (Int64.repr 516));[|reflexivity|constructor].
 eapply eval_Ebinop with (v1:=Vint (Int.repr 129)) (v2:=Vlong (Int64.repr 4));
  [apply eval_Etempvar;exact Len|constructor|reflexivity].
Qed.

Theorem wnaf_entry15_ready m b base a : exists mi bs,
 function_entry2 secp_ge f_secp256k1_ecmult_wnaf
 [Vptr b (Ptrofs.repr base);Vint (Int.repr 129);a;Vint (Int.repr 15)] m
 (wnaf_env bs) (wnaf_entry15_temps b base a) mi /\
 Clight2.exec_stmt secp_ge (wnaf_env bs) (wnaf_entry15_temps b base a) mi wnaf_before_memset
  E0 (wnaf_before_temps (wnaf_entry15_temps b base a)) mi Out_normal /\
 wnaf_loop_fields (wnaf_before_temps (wnaf_entry15_temps b base a)) 0 129 15 0 1 b base (-1) /\
 eval_exprlist secp_ge (wnaf_env bs) (wnaf_before_temps (wnaf_entry15_temps b base a)) mi wnaf_memset_args
  (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil)))
  [Vptr b (Ptrofs.repr base);Vint Int.zero;Vlong (Int64.repr 516)] /\
 Mem.range_perm mi bs 0 32 Cur Freeable /\
 (forall old,Mem.valid_block m old -> old<>bs) /\ Mem.unchanged_on (fun _ _=>True) m mi.
Proof.
 destruct (Mem.alloc m 0 32) as [mi bs] eqn:Alloc.
 exists mi,bs;split;[apply wnaf_entry15;exact Alloc|];split.
 - apply exec_wnaf_before_memset15;reflexivity.
 - split.
   + unfold wnaf_loop_fields,wnaf_before_temps,wnaf_entry15_temps;repeat split;reflexivity.
   + split.
     * apply wnaf_memset_arguments15;rewrite wnaf_before_preserves by discriminate;reflexivity.
     * split.
       -- intros pos Range;eapply Mem.perm_alloc_2;[exact Alloc|exact Range].
       -- split.
          ++ intros old Valid ->;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid).
          ++ eapply Mem.alloc_unchanged_on;exact Alloc.
Qed.

Theorem wnaf_entry15_owned_output m b a : Mem.range_perm m b 0 516 Cur Freeable ->
 exists mi bs,
 function_entry2 secp_ge f_secp256k1_ecmult_wnaf
 [Vptr b Ptrofs.zero;Vint (Int.repr 129);a;Vint (Int.repr 15)] m
 (wnaf_env bs) (wnaf_entry15_temps b 0 a) mi /\
 Clight2.exec_stmt secp_ge (wnaf_env bs) (wnaf_entry15_temps b 0 a) mi wnaf_before_memset
  E0 (wnaf_before_temps (wnaf_entry15_temps b 0 a)) mi Out_normal /\
 wnaf_loop_fields (wnaf_before_temps (wnaf_entry15_temps b 0 a)) 0 129 15 0 1 b 0 (-1) /\
 eval_exprlist secp_ge (wnaf_env bs) (wnaf_before_temps (wnaf_entry15_temps b 0 a)) mi wnaf_memset_args
  (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil)))
  [Vptr b Ptrofs.zero;Vint Int.zero;Vlong (Int64.repr 516)] /\
 Mem.range_perm mi b 0 516 Cur Freeable /\ Mem.range_perm mi bs 0 32 Cur Freeable /\
 b<>bs /\ Mem.unchanged_on (fun _ _=>True) m mi.
Proof.
 intro Owned;destruct (wnaf_entry15_ready m b 0 a)
  as (mi & bs & Entry & Prefix & Fields & Args & Private & Separate & Frame).
 assert (Valid:Mem.valid_block m b) by (eapply Mem.perm_valid_block;apply (Owned 0);lia).
 exists mi,bs;split;[exact Entry|];split;[exact Prefix|];split;[exact Fields|];split;[exact Args|];split.
 - intros pos Range;eapply Mem.perm_unchanged_on;[exact Frame|exact I|apply Owned;exact Range].
 - split;[exact Private|];split;[apply Separate;exact Valid|exact Frame].
Qed.
