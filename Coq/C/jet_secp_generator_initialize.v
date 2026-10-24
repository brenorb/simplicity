(** Actual initial counters and denominator-one call in Strauss. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_statement_prefix.
Require Import C.jet_secp_curve_statements C.jet_secp_fe_set_owned C.jet_secp_point_set_bit.
Require Import C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_generator_globalz_call C.jet_secp_scalar_add_reader_support.
Require Import C.jet_secp_field_read_preservation C.jet_secp_scalar_get_b32_storage.
Require Import C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Opaque secp_ge.
Set Default Timeout 10.

Definition generator_initial_counters := statement_sequence
 (firstn 4 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf)))) Sskip.
Definition generator_initialize := statement_sequence
 (firstn 5 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf)))) Sskip.
Definition generator_initial_temps le :=
 PTree.set _no (Vlong Int64.zero) (PTree.set _bits (Vint Int.zero)
  (PTree.set _bits_ng_128 (Vint Int.zero) (PTree.set _bits_ng_1 (Vint Int.zero) le))).
Definition generator_set_denominator := curve_call _secp256k1_fe_set_int f_secp256k1_fe_set_int None
 [Eaddrof (Evar _Z (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr));Econst_int Int.one tint].

Lemma generator_initial_counters_source : generator_initial_counters=
 Ssequence (Sset _bits_ng_1 (Econst_int Int.zero tint))
  (Ssequence (Sset _bits_ng_128 (Econst_int Int.zero tint))
   (Ssequence (Sset _bits (Econst_int Int.zero tint))
    (Ssequence (Sset _no (Ecast (Econst_int Int.zero tint) tulong)) Sskip))).
Proof. reflexivity. Qed.
Lemma generator_initialize_source : generator_initialize=statement_sequence
 (firstn 4 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf))))
 (Ssequence generator_set_denominator Sskip).
Proof. reflexivity. Qed.

Lemma exec_generator_initial_counters e le m :
 Clight2.exec_stmt secp_ge e le m generator_initial_counters E0 (generator_initial_temps le) m Out_normal.
Proof.
 rewrite generator_initial_counters_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_Sset;constructor|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_Sset;constructor|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_Sset;constructor|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_Sset;eapply eval_Ecast;[constructor|reflexivity]|constructor].
Qed.

Lemma generator_set_int_closed :
 closed_stmtb secp_closed_helpers (fn_body f_secp256k1_fe_set_int)=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.

Lemma generator_unchanged_preserved m mf :
 Mem.unchanged_on (fun _ _=>True) m mf -> readonly_preserved m mf.
Proof.
 intro Unchanged;split.
 - intros b Valid;split.
   + eapply Mem.valid_block_unchanged_on;[exact Unchanged|exact Valid].
   + intros pos p Perm;eapply Mem.perm_unchanged_on_2;
      [exact Unchanged|exact I|exact Valid|exact Perm].
 - eapply Mem.unchanged_on_implies;[exact Unchanged|intros;exact I].
Qed.

Theorem exec_generator_initialize e le m bz :
 e!_Z=Some (bz,Tstruct __5467 noattr) -> e!_secp256k1_fe_set_int=None ->
 Mem.range_perm m bz 0 40 Cur Freeable -> exists mi,
 Clight2.exec_stmt secp_ge e le m generator_initialize E0 (generator_initial_temps le) mi Out_normal /\
 fe_at mi bz 0 (words5 (point_set_bit_words true)) /\ Mem.range_perm mi bz 0 40 Cur Freeable /\
 lframe (fun b _=>b<>bz) m mi /\ readonly_preserved m mi.
Proof.
 intros ZLocal Symbol Owned.
 destruct (eval_fe_set_owned true m bz Owned) as (mi & Call & Field & Free & Frame).
 assert (Preserved:readonly_preserved m mi).
 { eapply secp_closed_function_preserved;[exact generator_set_int_closed|reflexivity|exact Call]. }
 exists mi;split;[|split;[exact Field|];split;[exact Free|];split;assumption].
 rewrite generator_initialize_source;apply exec_statement_prefix_then_last with
  (le1:=generator_initial_temps le) (m1:=m).
 - exact (exec_generator_initial_counters e le m).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=generator_initial_temps le);[|constructor].
   unfold generator_set_denominator;eapply exec_curve_call with
    (vargs:=[Vptr bz Ptrofs.zero;Vint Int.one]) (v:=Vundef).
   + unfold secp_pure;repeat first [left;reflexivity|right].
   + exact Symbol.
   + eapply eval_Econs with (v1:=Vptr bz Ptrofs.zero).
     * apply eval_Eaddrof;apply eval_Evar_local;exact ZLocal.
     * reflexivity.
     * eapply eval_Econs;[constructor|reflexivity|constructor].
   + exact Call.
Qed.

Lemma generator_initial_preserves le id : id<>_no -> id<>_bits -> id<>_bits_ng_128 -> id<>_bits_ng_1 ->
 (generator_initial_temps le)!id=le!id.
Proof.
 intros No Bits High Low;unfold generator_initial_temps.
 rewrite PTree.gso by exact No;rewrite PTree.gso by exact Bits;
 rewrite PTree.gso by exact High;rewrite PTree.gso by exact Low;reflexivity.
Qed.

Definition generator_prepare_non_generator := statement_sequence
 (firstn 8 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf)))) Sskip.
Definition generator_ready_temps le aptr zrptr :=
 generator_no_points_temps (generator_initial_temps le) aptr zrptr.
Lemma generator_prepare_non_generator_source : generator_prepare_non_generator=statement_sequence
 (firstn 5 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf)))) generator_no_points_phase.
Proof. reflexivity. Qed.

Theorem exec_generator_prepare_non_generator e le m bz bn nofs bs base ba aofs br zofs :
 e!_Z=Some (bz,Tstruct __5467 noattr) -> e!_secp256k1_fe_set_int=None ->
 e!_secp256k1_scalar_is_zero=None -> e!_secp256k1_ge_table_set_globalz=None ->
 le!_na=Some (Vptr bn (Ptrofs.repr nofs)) -> le!_num=Some (Vlong Int64.one) ->
 le!_state=Some (Vptr bs (Ptrofs.repr base)) ->
 Mem.range_perm m bz 0 40 Cur Freeable -> bn<>bz -> bs<>bz ->
 scalar_at m bn nofs [Int64.zero;Int64.zero;Int64.zero;Int64.zero] ->
 0<=base -> base+24<=Ptrofs.max_unsigned ->
 Mem.load Mptr m bs (base+8)=Some (Vptr ba aofs) ->
 Mem.load Mptr m bs (base+0)=Some (Vptr br zofs) -> exists mf,
 Clight2.exec_stmt secp_ge e le m generator_prepare_non_generator E0
  (generator_ready_temps le (Vptr ba aofs) (Vptr br zofs)) mf Out_normal /\
 fe_at mf bz 0 (words5 (point_set_bit_words true)) /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
 lframe (fun b _=>b<>bz) m mf /\ readonly_preserved m mf.
Proof.
 intros ZLocal SetSymbol ZeroSymbol GlobalSymbol NA Num State Owned NS SS Scalar Base Hi A Zr.
 destruct (exec_generator_initialize e le m bz ZLocal SetSymbol Owned)
  as (mi & Init & Field & FreeI & FrameI & PreservedI).
 set (li:=generator_initial_temps le).
 assert (NAi:li!_na=Some (Vptr bn (Ptrofs.repr nofs))).
 { unfold li;rewrite generator_initial_preserves by discriminate;exact NA. }
 assert (Numi:li!_num=Some (Vlong Int64.one)).
 { unfold li;rewrite generator_initial_preserves by discriminate;exact Num. }
 assert (Statei:li!_state=Some (Vptr bs (Ptrofs.repr base))).
 { unfold li;rewrite generator_initial_preserves by discriminate;exact State. }
 assert (Noi:li!_no=Some (Vlong Int64.zero)) by (unfold li,generator_initial_temps;apply PTree.gss).
 assert (Scalari:scalar_at mi bn nofs [Int64.zero;Int64.zero;Int64.zero;Int64.zero]).
 { eapply scalar_at_lframe;[exact Scalar|exact FrameI|intros;exact NS]. }
 assert (StateValid:Mem.valid_block m bs).
 { eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
   [eapply Mem.load_valid_access;exact A|apply perm_any_N]. }
 assert (Ai:Mem.load Mptr mi bs (base+8)=Some (Vptr ba aofs)).
 { rewrite (proj1 FrameI Mptr bs (base+8) StateValid ltac:(intros;exact SS));exact A. }
 assert (Zri:Mem.load Mptr mi bs (base+0)=Some (Vptr br zofs)).
 { rewrite (proj1 FrameI Mptr bs (base+0) StateValid ltac:(intros;exact SS));exact Zr. }
 destruct (exec_generator_no_points e li mi bn nofs bs base ba aofs br zofs
  ZeroSymbol GlobalSymbol NAi Numi Noi Statei Scalari Base Hi Ai Zri) as (mf & Phase & Unchanged).
 pose proof (lframe_unchanged _ _ _ Unchanged) as FrameF.
 exists mf;split.
 - rewrite generator_prepare_non_generator_source;eapply exec_statement_prefix_then_last;
    [exact Init|exact Phase].
 - split.
   + eapply field_at_lframe;[exact Field|exact FrameF|intros;exact I].
   + split.
     * intros pos Range;eapply Mem.perm_unchanged_on;[exact Unchanged|exact I|apply FreeI;exact Range].
     * split.
       -- eapply lframe_trans;[exact FrameI|];eapply lframe_implies;[exact FrameF|];intros;exact I.
       -- eapply preserved_trans;[exact PreservedI|apply generator_unchanged_preserved;exact Unchanged].
Qed.
