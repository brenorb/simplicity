(** Original one-point Strauss length reads and maximum updates. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_strauss_wnaf_calls
 C.jet_secp_generator_bits_max C.jet_secp_statement_prefix C.jet_secp_strauss_split_wnaf
 C.jet_secp_generator_preprocess
 C.jet_sx_mem C.jet_memset_model C.jet_secp_split_literal C.jet_secp_canonical_scalar
 C.jet_secp_split_function C.jet_secp_split_constants C.jet_secp_wnaf_slice_frame
 C.jet_secp_wnaf_loop C.jet_secp_wnaf5_input C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_signed_array
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Require Import Simplicity.Ty Simplicity.Word.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Opaque secp_ge canonical_scalar_normalize literal_scalar_split_lambda.
Set Default Timeout 10.

Definition strauss_count_expr (high:bool) tmp :=
 Efield (strauss_point_from_temp tmp) (if high then _bits_na_lam else _bits_na_1) tint.
Definition strauss_raise_bits (high:bool) :=
 let ptr:=if high then _t'38 else _t'41 in
 let count:=if high then _t'39 else _t'42 in
 let again:=if high then _t'40 else _t'43 in
 Ssequence (Sset ptr strauss_ps_pointer)
  (Ssequence (Sset count (strauss_count_expr high ptr))
   (Sifthenelse (Ebinop Ogt (Etempvar count tint) (Etempvar _bits tint) tint)
    (Ssequence (Sset again strauss_ps_pointer) (Sset _bits (strauss_count_expr high again))) Sskip)).
Definition strauss_bits_max :=
 statement_sequence [Sloop Sskip Sbreak;Sloop Sskip Sbreak;
  strauss_raise_bits Datatypes.false;strauss_raise_bits Datatypes.true] Sskip.
Definition strauss_after_bits_max := match strauss_after_wnaf with
 | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ rest)))=>rest | _=>Sskip end.

Lemma strauss_bits_max_source : strauss_after_wnaf=
 statement_sequence [Sloop Sskip Sbreak;Sloop Sskip Sbreak;
  strauss_raise_bits Datatypes.false;strauss_raise_bits Datatypes.true] strauss_after_bits_max.
Proof. reflexivity. Qed.

Definition strauss_raise_loaded (high:bool) le bp candidate :=
 PTree.set (if high then _t'39 else _t'42) (Vint (Int.repr candidate))
  (PTree.set (if high then _t'38 else _t'41) (Vptr bp Ptrofs.zero) le).
Definition strauss_raise_temps (high:bool) le bp current candidate :=
 generator_raise_temps
  (if current <? candidate then
    PTree.set (if high then _t'40 else _t'43) (Vptr bp Ptrofs.zero)
     (strauss_raise_loaded high le bp candidate)
   else strauss_raise_loaded high le bp candidate) current candidate.
Definition strauss_bits_max_temps le bp low high :=
 strauss_raise_temps Datatypes.true
  (strauss_raise_temps Datatypes.false le bp 0 low) bp low high.

Lemma eval_strauss_count (high:bool) e le m bp tmp bits :
 le!tmp=Some (Vptr bp Ptrofs.zero) -> le!_no=Some (Vlong Int64.zero) ->
 Mem.load Mint32 m bp (strauss_wnaf_count_offset high)=Some (Vint (Int.repr bits)) ->
 eval_expr secp_ge e le m (strauss_count_expr high tmp) (Vint (Int.repr bits)).
Proof.
 intros Pointer No Count;unfold strauss_count_expr.
 eapply eval_Elvalue with (loc:=bp) (ofs:=Ptrofs.repr (strauss_wnaf_count_offset high)) (bf:=Full).
 - eapply eval_strauss_point_field;[destruct high;cbn [strauss_wnaf_count_offset In];tauto|exact Pointer|exact No].
 - eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
   destruct high;
    [change (Mem.load Mint32 m bp 1036=Some (Vint (Int.repr bits)))|
     change (Mem.load Mint32 m bp 1032=Some (Vint (Int.repr bits)))];exact Count.
Qed.

Lemma eval_strauss_raise_guard e le m id current candidate :
 0<=current<=129 -> 0<=candidate<=129 ->
 le!_bits=Some (Vint (Int.repr current)) -> le!id=Some (Vint (Int.repr candidate)) ->
 eval_expr secp_ge e le m (Ebinop Ogt (Etempvar id tint) (Etempvar _bits tint) tint)
  (Vint (if current <? candidate then Int.one else Int.zero)).
Proof.
 intros Current Candidate Bits Count;eapply eval_Ebinop;
  [apply eval_Etempvar;exact Count|apply eval_Etempvar;exact Bits|].
 change (Some (Val.of_bool (Int.lt (Int.repr current) (Int.repr candidate)))=
  Some (Vint (if current <? candidate then Int.one else Int.zero))).
 unfold Int.lt;rewrite !Int.signed_repr by
  (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
 destruct (Coqlib.zlt current candidate),(Z.ltb_spec current candidate);try lia;reflexivity.
Qed.

Lemma strauss_raise_bits_value high le bp current candidate :
 le!_bits=Some (Vint (Int.repr current)) ->
 (strauss_raise_temps high le bp current candidate)!_bits=
  Some (Vint (Int.repr (Z.max current candidate))).
Proof.
 intro Bits;unfold strauss_raise_temps;apply generator_raise_bits_value.
 unfold strauss_raise_loaded;destruct high,(current <? candidate);
  rewrite !PTree.gso by discriminate;exact Bits.
Qed.
Lemma strauss_raise_bits_other (high:bool) le bp current candidate id :
 id<>_bits -> id<>(if high then _t'38 else _t'41) ->
 id<>(if high then _t'39 else _t'42) -> id<>(if high then _t'40 else _t'43) ->
 (strauss_raise_temps high le bp current candidate)!id=le!id.
Proof.
 intros Bits Ptr Count Again;unfold strauss_raise_temps.
 rewrite generator_raise_bits_other by exact Bits.
 unfold strauss_raise_loaded;destruct (current <? candidate);
  rewrite !PTree.gso by assumption;reflexivity.
Qed.

Theorem exec_strauss_raise_bits (high:bool) e le m bs bp current candidate :
 0<=current<=129 -> 0<=candidate<=129 -> le!_bits=Some (Vint (Int.repr current)) ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_no=Some (Vlong Int64.zero) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mint32 m bp (strauss_wnaf_count_offset high)=Some (Vint (Int.repr candidate)) ->
 Clight2.exec_stmt secp_ge e le m (strauss_raise_bits high) E0
  (strauss_raise_temps high le bp current candidate) m Out_normal.
Proof.
 intros Current Candidate Bits State No Pointer Count.
 pose (lp:=PTree.set (if high then _t'38 else _t'41) (Vptr bp Ptrofs.zero) le).
 pose (lc:=strauss_raise_loaded high le bp candidate).
 assert (NoP:lp!_no=Some (Vlong Int64.zero)).
 { unfold lp;destruct high;rewrite PTree.gso by discriminate;exact No. }
 assert (Read:eval_expr secp_ge e lp m
  (strauss_count_expr high (if high then _t'38 else _t'41)) (Vint (Int.repr candidate))).
 { apply (eval_strauss_count high e lp m bp);[unfold lp;apply PTree.gss|exact NoP|exact Count]. }
 assert (StateC:lc!_state=Some (Vptr bs Ptrofs.zero)).
 { unfold lc,strauss_raise_loaded;destruct high;rewrite !PTree.gso by discriminate;exact State. }
 assert (NoC:lc!_no=Some (Vlong Int64.zero)).
 { unfold lc,strauss_raise_loaded;destruct high;rewrite !PTree.gso by discriminate;exact No. }
 assert (BitsC:lc!_bits=Some (Vint (Int.repr current))).
 { unfold lc,strauss_raise_loaded;destruct high;rewrite !PTree.gso by discriminate;exact Bits. }
 assert (CountC:lc!(if high then _t'39 else _t'42)=Some (Vint (Int.repr candidate))).
 { unfold lc,strauss_raise_loaded;apply PTree.gss. }
 pose proof (eval_strauss_raise_guard e lc m _ current candidate Current Candidate BitsC CountC) as Guard.
 unfold strauss_raise_bits;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lp) (m1:=m).
 - apply exec_Sset;exact (eval_strauss_ps_pointer e le m bs bp State Pointer).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lc) (m1:=m).
   + apply exec_Sset;exact Read.
   + unfold strauss_raise_temps,generator_raise_temps.
     destruct (current <? candidate) eqn:Choose.
     * eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=Datatypes.true);
        [exact Guard|reflexivity|].
       eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
       -- apply exec_Sset;exact (eval_strauss_ps_pointer e lc m bs bp StateC Pointer).
       -- apply exec_Sset;apply (eval_strauss_count high e _ m bp).
          ++ apply PTree.gss.
          ++ destruct high;rewrite PTree.gso by discriminate;exact NoC.
          ++ exact Count.
     * eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=Datatypes.false);
        [exact Guard|reflexivity|constructor].
Qed.

Lemma exec_strauss_noop e le m :
 Clight2.exec_stmt secp_ge e le m (Sloop Sskip Sbreak) E0 le m Out_normal.
Proof.
 eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (out1:=Out_normal) (out2:=Out_break);
  [constructor|constructor|constructor|constructor].
Qed.

Theorem exec_strauss_bits_max e le m bs bp low high :
 0<=low<=129 -> 0<=high<=129 -> le!_bits=Some (Vint Int.zero) ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_no=Some (Vlong Int64.zero) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mint32 m bp 1032=Some (Vint (Int.repr low)) ->
 Mem.load Mint32 m bp 1036=Some (Vint (Int.repr high)) ->
 Clight2.exec_stmt secp_ge e le m strauss_bits_max E0 (strauss_bits_max_temps le bp low high) m Out_normal /\
 (strauss_bits_max_temps le bp low high)!_bits=Some (Vint (Int.repr (Z.max low high))) /\
 forall id,~In id [_bits;_t'38;_t'39;_t'40;_t'41;_t'42;_t'43] ->
  (strauss_bits_max_temps le bp low high)!id=le!id.
Proof.
 intros Low High Bits State No Pointer CountLow CountHigh.
 pose (l1:=strauss_raise_temps Datatypes.false le bp 0 low).
 assert (Bits1:l1!_bits=Some (Vint (Int.repr low))).
 { unfold l1;pose proof (strauss_raise_bits_value Datatypes.false le bp 0 low Bits) as B.
   rewrite Z.max_r in B by lia;exact B. }
 assert (State1:l1!_state=Some (Vptr bs Ptrofs.zero)).
 { unfold l1;rewrite strauss_raise_bits_other by discriminate;exact State. }
 assert (No1:l1!_no=Some (Vlong Int64.zero)).
 { unfold l1;rewrite strauss_raise_bits_other by discriminate;exact No. }
 split.
 - unfold strauss_bits_max;cbn [statement_sequence].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_strauss_noop|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_strauss_noop|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=l1) (m1:=m).
   + apply (exec_strauss_raise_bits Datatypes.false e le m bs bp 0 low);
     [lia|exact Low|exact Bits|exact State|exact No|exact Pointer|exact CountLow].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[|constructor].
     exact (exec_strauss_raise_bits Datatypes.true e l1 m bs bp low high
      Low High Bits1 State1 No1 Pointer CountHigh).
 - split.
   + unfold strauss_bits_max_temps;apply strauss_raise_bits_value;exact Bits1.
   + intros id Outside;unfold strauss_bits_max_temps.
     rewrite !strauss_raise_bits_other;cbn [In] in Outside;intuition congruence.
Qed.

Lemma exec_strauss_bits_max_then_rest e le m l1 m1 lf mf out :
 Clight2.exec_stmt secp_ge e le m strauss_bits_max E0 l1 m1 Out_normal ->
 Clight2.exec_stmt secp_ge e l1 m1 strauss_after_bits_max E0 lf mf out ->
 Clight2.exec_stmt secp_ge e le m strauss_after_wnaf E0 lf mf out.
Proof.
 intros Prefix Rest;rewrite strauss_bits_max_source.
 eapply exec_statement_prefix_then_last;[exact Prefix|exact Rest].
Qed.

Definition strauss_scalar_prepare := Ssequence strauss_split_wnaf_prepare strauss_bits_max.
Definition strauss_scalar_prepare_temps le bp low high :=
 strauss_bits_max_temps (strauss_wnaf_prepare_temps le bp low high) bp low high.

Lemma strauss_wnaf_prepare_other le bp low high id :
 ~In id [_t'44;_t'5;_t'45;_t'46;_t'4;_t'47] ->
 (strauss_wnaf_prepare_temps le bp low high)!id=le!id.
Proof.
 intro Outside;unfold strauss_wnaf_prepare_temps,strauss_wnaf_half_temps.
 rewrite !PTree.gso;cbn [In] in Outside;intuition congruence.
Qed.

Lemma exec_strauss_scalar_prepare_then_rest e le m l1 m1 lf mf out :
 Clight2.exec_stmt secp_ge e le m strauss_scalar_prepare E0 l1 m1 Out_normal ->
 Clight2.exec_stmt secp_ge e l1 m1 strauss_after_bits_max E0 lf mf out ->
 Clight2.exec_stmt secp_ge e le m generator_preprocess_after_check E0 lf mf out.
Proof.
 intros Prefix Rest;unfold strauss_scalar_prepare in Prefix;inversion Prefix;subst.
 - match goal with H:?t1 ** ?t2=E0 |- _=>
    destruct (Eapp_E0_inv t1 t2 H) as [-> ->] end.
   eapply exec_strauss_split_wnaf_then_rest;[eassumption|].
   eapply exec_strauss_bits_max_then_rest;[eassumption|exact Rest].
 - contradiction.
Qed.

Theorem exec_strauss_scalar_prepare (Model:memset_model) e le m raw bk br1 br2 bs bp :
 e!_na_1=Some (br1,Tstruct __5826 noattr) -> e!_na_lam=Some (br2,Tstruct __5826 noattr) ->
 e!_secp256k1_scalar_split_lambda=None -> e!_secp256k1_ecmult_wnaf=None ->
 le!_na=Some (Vptr bk Ptrofs.zero) -> le!_np=Some (Vlong Int64.zero) ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_no=Some (Vlong Int64.zero) ->
 le!_bits=Some (Vint Int.zero) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) -> split_constants_ready m ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) ->
 Mem.range_perm m bk 0 32 Cur Freeable -> Mem.range_perm m br1 0 32 Cur Freeable ->
 Mem.range_perm m br2 0 32 Cur Freeable -> Mem.range_perm m bs 0 24 Cur Freeable ->
 Mem.range_perm m bp 0 1040 Cur Freeable -> NoDup [bk;br1;br2;bs;bp] ->
 let halves:=@literal_scalar_split_lambda Alg.CoreFunSem raw in
 exists mf last1 last2 digits1 digits2,
 Clight2.exec_stmt secp_ge e le m strauss_scalar_prepare E0
  (strauss_scalar_prepare_temps le bp (last1+1) (last2+1)) mf Out_normal /\
 (strauss_scalar_prepare_temps le bp (last1+1) (last2+1))!_bits=
  Some (Vint (Int.repr (Z.max (last1+1) (last2+1)))) /\
 0<=Z.max (last1+1) (last2+1)<=129 /\
 (forall id,~In id [_bits;_t'38;_t'39;_t'40;_t'41;_t'42;_t'43;_t'44;_t'5;_t'45;_t'46;_t'4;_t'47] ->
  (strauss_scalar_prepare_temps le bp (last1+1) (last2+1))!id=le!id) /\
 wnaf_array_state mf bp 0 129 5 (wnaf5_input_sign (fst (fst halves))) 129 last1 digits1 /\
 wnaf_array_state mf bp 516 129 5 (wnaf5_input_sign (fst (snd halves))) 129 last2 digits2 /\
 0<=last1+1<=129 /\ 0<=last2+1<=129 /\
 Mem.load Mint32 mf bp 1032=Some (Vint (Int.repr (last1+1))) /\
 Mem.load Mint32 mf bp 1036=Some (Vint (Int.repr (last2+1))) /\
 Mem.load Mptr mf bs 16=Some (Vptr bp Ptrofs.zero) /\
 scalar_at mf br1 0 (map Int64.repr (scalar_limbs_of
  (wnaf5_input_scalar (fst (fst halves)) (snd (fst halves))))) /\
 scalar_at mf br2 0 (map Int64.repr (scalar_limbs_of
  (wnaf5_input_scalar (fst (snd halves)) (snd (snd halves))))) /\
 scalar_at mf bk 0 (map Int64.repr (scalar_limbs_of
  (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw)))) /\
 Mem.range_perm mf bp 0 1040 Cur Freeable /\ split_constants_ready mf /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun old pos=>split_function_frame bk br1 br2 old pos /\
  wnaf_slice_outside bp 0 260 old pos) m mf /\
 map wnaf5_literal_value (literal_wnaf5_digits (fst halves))=
  rev (map (fun i=>wnaf5_input_sign (fst (fst halves))*digits1 (Z.of_nat i)) (seq 0 129)) /\
 map wnaf5_literal_value (literal_wnaf5_digits (snd halves))=
  rev (map (fun i=>wnaf5_input_sign (fst (snd halves))*digits2 (Z.of_nat i)) (seq 0 129)).
Proof.
 intros Low High SplitSymbol WnafSymbol NA NP State No Bits Pointer Ready Input FK F1 F2 FS FP Separate;
  cbv zeta.
 destruct (exec_strauss_split_wnaf_prepare Model e le m raw bk br1 br2 bs bp
  Low High SplitSymbol WnafSymbol NA NP State No Pointer Ready Input FK F1 F2 FS FP Separate)
  as (mf & last1 & last2 & digits1 & digits2 & Prefix & Array1 & Array2 & Bound1 & Bound2 &
   Count1 & Count2 & PointerF & Source1 & Source2 & SourceK & Owned & ReadyF & Keep & Readonly &
   Frame & Literal1 & Literal2).
 pose (lw:=strauss_wnaf_prepare_temps le bp (last1+1) (last2+1)).
 assert (BitsW:lw!_bits=Some (Vint Int.zero)).
 { unfold lw;rewrite strauss_wnaf_prepare_other by (cbn [In];intuition discriminate);exact Bits. }
 assert (StateW:lw!_state=Some (Vptr bs Ptrofs.zero)).
 { unfold lw;rewrite strauss_wnaf_prepare_other by (cbn [In];intuition discriminate);exact State. }
 assert (NoW:lw!_no=Some (Vlong Int64.zero)).
 { unfold lw;rewrite strauss_wnaf_prepare_other by (cbn [In];intuition discriminate);exact No. }
 destruct (exec_strauss_bits_max e lw mf bs bp (last1+1) (last2+1)
  Bound1 Bound2 BitsW StateW NoW PointerF Count1 Count2) as [Maximum [BitsF Other]].
 exists mf,last1,last2,digits1,digits2;split.
 - unfold strauss_scalar_prepare,strauss_scalar_prepare_temps;
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Prefix|exact Maximum].
 - split;[exact BitsF|];split;[lia|];split.
   + intros id Outside;unfold strauss_scalar_prepare_temps;rewrite Other.
     * unfold lw;apply strauss_wnaf_prepare_other;cbn [In] in Outside|-*;tauto.
     * cbn [In] in Outside|-*;tauto.
   + split;[exact Array1|];split;[exact Array2|];split;[exact Bound1|];split;[exact Bound2|];
     split;[exact Count1|];split;[exact Count2|];split;[exact PointerF|];
     split;[exact Source1|];split;[exact Source2|];split;[exact SourceK|];
     split;[exact Owned|];split;[exact ReadyF|];split;[exact Keep|];split;[exact Readonly|];
     split;[exact Frame|];split;[exact Literal1|exact Literal2].
Qed.
