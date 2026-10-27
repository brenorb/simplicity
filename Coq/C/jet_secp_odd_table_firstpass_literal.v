(** Derive the complete first-pass literal result from the original head,
    seed and seven C iterations. Intermediate representation and arithmetic
    bounds are obtained from their checked executions, not caller premises. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_curve_statements C.jet_secp_field_read_preservation C.jet_secp_slice_permissions
 C.jet_clight_internal_permissions C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_double_all_calls C.jet_secp_double_literal C.jet_secp_odd_table_head C.jet_secp_odd_table_seed
 C.jet_secp_odd_table_loop C.jet_secp_odd_table_body C.jet_secp_odd_table_pass1_bridge
 C.jet_secp_odd_table_literal_walk C.jet_secp_odd_table_seed_literal C.jet_secp_field_zero_owned
 C.jet_secp_scalar_table_literal C.jet_secp_rescale_literal C.jet_secp_canonical_normalize
 C.jet_secp_odd_table_function.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge odd_table_final_state literal_pass1_8 literal_gej_double literal_gej_zinv
 rescale_field_output canonical_fe_normalize.
Local Ltac separate Distinct := clear -Distinct;
 repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct;intuition congruence.

Theorem odd_table_firstpass_literal e le x y z m br bp bd ba bg bz (ax ay az:Ty.tySem (Word 8)) :
 NoDup [br;bp;bd;ba;bg;bz] ->
 e!_d=Some (bd,Tstruct __6123 noattr) -> e!_ai=Some (ba,Tstruct __6123 noattr) ->
 e!_d_ge=Some (bg,curve_ge_type) ->
 e!_secp256k1_gej_double_var=None -> e!_secp256k1_ge_set_xy=None ->
 e!_secp256k1_ge_set_gej_zinv=None -> e!_secp256k1_gej_set_ge=None -> e!_secp256k1_gej_add_ge_var=None ->
 le!_n=Some (Vint (Int.repr 8)) -> le!_a=Some (Vptr bp Ptrofs.zero) ->
 le!_pre_a=Some (Vptr br Ptrofs.zero) -> le!_zr=Some (Vptr bz Ptrofs.zero) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bd 0 128 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bg 0 88 Cur Freeable -> Mem.range_perm m bz 0 320 Cur Freeable ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az -> field_zero_result z=Int.zero ->
 let d:Ty.tySem literal_table_gej:=@C.jet_secp_double_literal.literal_gej_double Alg.CoreFunSem ((ax,ay),az) in
 let start:Ty.tySem literal_table_gej:=(@literal_gej_zinv Alg.CoreFunSem ((ax,ay),snd d),az) in
 table_state_tree (odd_table_final_state x y z)=
  literal_table_normalize_tree 3 (fst (@literal_pass1_8 Alg.CoreFunSem (start,fst d))) /\
 rescale_field_output (odd_table_z (odd_table_final_state x y z))=
  @canonical_fe_normalize Alg.CoreFunSem (snd (@literal_pass1_8 Alg.CoreFunSem (start,fst d))) /\
 odd_table_accumulator_bounds (odd_table_final_state x y z).
Proof.
 intros Distinct D AI DG DoubleGlobal XYGlobal ZinvGlobal SetGlobal AddGlobal N A Table Ratios
  BX BY BZ X Y Z Flag FreeT FreeP FreeD FreeA FreeG FreeR HX HY HZ Finite;cbv zeta.
 assert (HeadSep:NoDup [br;bp;bd;bg]) by (repeat constructor;cbn [In];separate Distinct).
 destruct (exec_odd_table_head e le x y z m br bp bd bg HeadSep D DG DoubleGlobal XYGlobal ZinvGlobal A Table
  BX BY BZ X Y Z Flag FreeT FreeP FreeD FreeG)
  as (mh & Head & TX & TY & TFlag & PX & PY & PZ & PFlag & GX & GY & GFlag & DZ &
    BTX & BTY & BDX & BDY & BDZ & FreeTH & FreePH & FreeDH & FreeGH & KeepH & FrameH & ReadonlyH).
 assert (FreeAH:Mem.range_perm mh ba 0 128 Cur Freeable) by
  (eapply keeps_range_permissions;[exact KeepH|exact FreeA]).
 assert (FreeRH:Mem.range_perm mh bz 0 320 Cur Freeable) by
  (eapply keeps_range_permissions;[exact KeepH|exact FreeR]).
 assert (SeedSep:NoDup [ba;br;bp;bd;bz]) by (repeat constructor;cbn [In];separate Distinct).
 destruct (exec_odd_table_seed e le _ _ z _ mh ba br bp bd bz SeedSep AI D SetGlobal Table A Ratios
  BTX BTY BZ BDZ TX TY TFlag PZ DZ FreeAH FreeTH FreePH FreeDH FreeRH)
  as (ms & Seed & SeedFields & PrefixS & PrefixBoundsS & AccS & AccBoundsS & PZS & DZS &
    FreeAS & FreeTS & FreePS & FreeDS & FreeRS & KeepS & FrameS & ReadonlyS).
 assert (LoopSep:NoDup [br;ba;bg;bz]) by (repeat constructor;cbn [In];separate Distinct).
 assert (GXS:fe_at ms bg 0 (words5 (double_output_x_words x y))).
 { eapply field_at_lframe;[exact GX|exact FrameS|];intros;split;[separate Distinct|left;separate Distinct]. }
 assert (GYS:fe_at ms bg 40 (words5 (double_output_y_words x y))).
 { eapply field_at_lframe;[exact GY|exact FrameS|];intros;split;[separate Distinct|left;separate Distinct]. }
 assert (GFlagS:Mem.load Mint32 ms bg 80=Some (Vint Int.zero)).
 { rewrite (proj1 FrameS Mint32 bg 80);[exact GFlag| |].
   - eapply Mem.perm_valid_block;apply (FreeGH 0);lia.
   - intros;split;[separate Distinct|left;separate Distinct]. }
 assert (FreeGS:Mem.range_perm ms bg 0 88 Cur Freeable) by
  (eapply keeps_range_permissions;[exact KeepS|exact FreeGH]).
 destruct (odd_table_initial_literal x y z ax ay az BX BY BZ HX HY HZ Finite)
  as (AccLiteral & PrefixLiteral & UL & VL).
 set (le1:=PTree.set _i (Vint Int.one) le).
 assert (Other1:forall id,id<>_i -> le1!id=le!id) by
  (intros id Different;unfold le1;apply PTree.gso;exact Different).
 destruct (exec_odd_table_pass1_eight e le1 ms br ba bg bz (odd_table_initial_state x y z)
  (double_output_x_words x y) (double_output_y_words x y)
  (@literal_gej_zinv Alg.CoreFunSem ((ax,ay),snd (@C.jet_secp_double_literal.literal_gej_double Alg.CoreFunSem ((ax,ay),az))),az)
  (fst (@C.jet_secp_double_literal.literal_gej_double Alg.CoreFunSem ((ax,ay),az)))
  LoopSep AI DG AddGlobal XYGlobal ltac:(rewrite Other1 by discriminate;exact Table)
  ltac:(rewrite Other1 by discriminate;exact Ratios) ltac:(unfold le1;apply PTree.gss)
  ltac:(rewrite Other1 by discriminate;exact N) PrefixS PrefixBoundsS AccS AccBoundsS BDX BDY
  GXS GYS GFlagS FreeTS FreeAS FreeGS FreeRS AccLiteral PrefixLiteral UL VL)
  as (lef & mf & Run & Tree & ZLiteral & PrefixF & PrefixBoundsF & AccF & BoundsF & Rest).
 split;[exact Tree|];split;[exact ZLiteral|exact BoundsF].
Qed.

Local Ltac allocated_valid := first [assumption |
 match goal with Alloc:Mem.alloc _ _ _=(?mm,?bb) |- Mem.valid_block ?mm ?bb =>
  eapply Mem.valid_new_block;exact Alloc end |
 match goal with Alloc:Mem.alloc _ _ _=(?mm,_) |- Mem.valid_block ?mm _ =>
  eapply Mem.valid_block_alloc;[exact Alloc|allocated_valid] end].
Local Ltac allocated_distinct := first [assumption |
 match goal with Alloc:Mem.alloc _ _ _=(_,?bb) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ Alloc);rewrite <-Eq;allocated_valid end |
 match goal with Alloc:Mem.alloc _ _ _=(_,?ba) |- ?ba<>?bb =>
  let Eq:=fresh "Eq" in intro Eq;apply (Mem.fresh_block_alloc _ _ _ _ _ Alloc);rewrite Eq;allocated_valid end].

(** Establish the workspace rather than requiring the caller to supply
    locals, their initialization or any intermediate execution. *)
Theorem odd_table_firstpass_from_inputs x y z m br bp bz (bo:block) (ax ay az:Ty.tySem (Word 8)) :
 NoDup [br;bp;bz] -> square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bz 0 320 Cur Freeable ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az -> field_zero_result z=Int.zero ->
 let d:Ty.tySem literal_table_gej:=@literal_gej_double Alg.CoreFunSem ((ax,ay),az) in
 let start:Ty.tySem literal_table_gej:=(@literal_gej_zinv Alg.CoreFunSem ((ax,ay),snd d),az) in
 table_state_tree (odd_table_final_state x y z)=
  literal_table_normalize_tree 3 (fst (@literal_pass1_8 Alg.CoreFunSem (start,fst d))) /\
 rescale_field_output (odd_table_z (odd_table_final_state x y z))=
  @canonical_fe_normalize Alg.CoreFunSem (snd (@literal_pass1_8 Alg.CoreFunSem (start,fst d))) /\
 odd_table_accumulator_bounds (odd_table_final_state x y z).
Proof.
 intros Distinct BX BY BZ X Y Z Flag FreeT FreeP FreeR HX HY HZ Finite;cbv zeta.
 assert (VT:Mem.valid_block m br) by (eapply Mem.perm_valid_block;apply (FreeT 0);lia).
 assert (VP:Mem.valid_block m bp) by (eapply Mem.perm_valid_block;apply (FreeP 0);lia).
 assert (VR:Mem.valid_block m bz) by (eapply Mem.perm_valid_block;apply (FreeR 0);lia).
 destruct (Mem.alloc m 0 128) as (m1 & bd) eqn:AllocD.
 destruct (Mem.alloc m1 0 128) as (m2 & ba) eqn:AllocA.
 destruct (Mem.alloc m2 0 88) as (mi & bg) eqn:AllocG.
 assert (Old:forall b,Mem.valid_block m b -> b<>bd /\ b<>ba /\ b<>bg) by
  (intros b Valid;repeat split;allocated_distinct).
 assert (DA:bd<>ba) by allocated_distinct.
 assert (DG:bd<>bg) by allocated_distinct.
 assert (AG:ba<>bg) by allocated_distinct.
 assert (SepAll:NoDup [br;bp;bd;ba;bg;bz]).
 { repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;repeat split;
   try apply NoDup_nil;try apply in_nil;first [separate Distinct|congruence|allocated_distinct]. }
 assert (AllocFrame:lframe (fun _ _=>True) m mi).
 { eapply lframe_trans;[apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact AllocD|].
   eapply lframe_trans;eapply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption. }
 assert (AllocKeep:keeps_permissions m mi).
 { eapply keeps_permissions_trans;[eapply alloc_keeps_permissions;exact AllocD|].
   eapply keeps_permissions_trans;eapply alloc_keeps_permissions;eassumption. }
 assert (XI:fe_at mi bp 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact AllocFrame|];intros;exact Logic.I).
 assert (YI:fe_at mi bp 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact AllocFrame|];intros;exact Logic.I).
 assert (ZI:fe_at mi bp 80 (words5 z)) by (eapply field_at_lframe;[exact Z|exact AllocFrame|];intros;exact Logic.I).
 assert (FlagI:Mem.load Mint32 mi bp 120=Some (Vint Int.zero)) by
  (rewrite (proj1 AllocFrame Mint32 bp 120 VP);[exact Flag|intros;exact Logic.I]).
 assert (FreeTI:Mem.range_perm mi br 0 704 Cur Freeable) by (eapply keeps_range_permissions;[exact AllocKeep|exact FreeT]).
 assert (FreePI:Mem.range_perm mi bp 0 128 Cur Freeable) by (eapply keeps_range_permissions;[exact AllocKeep|exact FreeP]).
 assert (FreeRI:Mem.range_perm mi bz 0 320 Cur Freeable) by (eapply keeps_range_permissions;[exact AllocKeep|exact FreeR]).
 assert (FreeDI:Mem.range_perm mi bd 0 128 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_1;[exact AllocG|];eapply Mem.perm_alloc_1;[exact AllocA|];
   eapply Mem.perm_alloc_2;[exact AllocD|exact Range]. }
 assert (FreeAI:Mem.range_perm mi ba 0 128 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_1;[exact AllocG|];eapply Mem.perm_alloc_2;[exact AllocA|exact Range]. }
 assert (FreeGI:Mem.range_perm mi bg 0 88 Cur Freeable) by
  (intros pos Range;eapply Mem.perm_alloc_2;[exact AllocG|exact Range]).
 exact (odd_table_firstpass_literal (odd_table_env bd ba bg) (odd_table_entry_temps br bp bz bo)
  x y z mi br bp bd ba bg bz ax ay az SepAll eq_refl eq_refl eq_refl
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
  BX BY BZ XI YI ZI FlagI FreeTI FreePI FreeDI FreeAI FreeGI FreeRI HX HY HZ Finite).
Qed.
