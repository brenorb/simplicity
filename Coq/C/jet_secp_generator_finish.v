(** Actual generator affine/save/return tail, including the infinity branch.
    Reuse the original affine and saver executions from concrete owned fields.
    The finite affine call retains the explicitly deferred CTZ boundary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.extraMath C.jet_sx_mem C.jet_sx_state C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_field_add_initial C.jet_secp_field_pair_multiply
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
  C.jet_secp_square_numeric C.jet_secp_point_mul_storage
  C.jet_secp_modinfo_fe_caller C.jet_secp_fe_inverse_state C.jet_secp_invert_literal C.jet_secp_fe_inv_prefix
  C.jet_secp_affine_inverse_complete C.jet_secp_affine_infinite C.jet_secp_generator_affine_roundtrip
  C.jet_secp_generator_save C.jet_secp_generator_save_initial C.jet_secp_generator_save_storage
  C.jet_secp_generator_save_values C.jet_secp_generator_codec C.jet_secp_generator_field_roundtrip
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_statement_prefix
  C.jet_clight_internal_preserve C.jet_secp_sha_startup C.jet_secp_swu_startup C.jet_secp_generator_sha_absorb.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge generator_saved_bytes.

Theorem eval_generator_save_fields x y flag m br bg :
  br<>bg ->square_input_bounds x ->square_input_bounds y ->
  fe_at m br 0 (words5 x) ->fe_at m br 40 (words5 y) ->Mem.load Mint32 m br 80=Some (Vint flag) ->
  Mem.range_perm m br 0 88 Cur Freeable ->Mem.range_perm m bg 0 64 Cur Freeable ->exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_generator_save)
    [Vptr bg Ptrofs.zero;Vptr br Ptrofs.zero] E0 mf Vundef /\
  Mem.range_perm mf br 0 88 Cur Freeable /\Mem.range_perm mf bg 0 64 Cur Freeable /\
  Mem.load Mint32 mf br 80=Some (Vint flag) /\
  (forall (second:bool) i,(i<32)%nat ->
    Mem.load Mint8unsigned mf bg ((if second then 32 else 0)+Z.of_nat i)=
      Some (Vint (nth i (map Int.repr (generator_saved_bytes (field_pair_valuation x y)
        (if second then 5 else 0))) Int.zero))) /\
  lframe (fun b _=>b<>br /\b<>bg) m mf /\readonly_preserved m mf.
Proof.
  intros Sep BX BY X Y Flag FR FG.
  assert (PX:fe_at m br 0 (field_values (field_pair_valuation x y) 0)) by (rewrite field_pair_left;exact X).
  assert (PY:fe_at m br 40 (field_values (field_pair_valuation x y) 5)) by (rewrite field_pair_right;exact Y).
  destruct (eval_generator_save_bytes flag (field_pair_valuation x y) [(br,0);(bg,0)] m
    (generator_save_initial_from_fields _ flag m br bg Sep PX PY Flag FR FG)
    (generator_field_pair_bounds x y BX BY))
    as (mf & Call & FRF & FGF & FlagF & Bytes & Frame & Read).
  exists mf;split;[exact Call|];split;[exact FRF|];split;[exact FGF|];split;[exact FlagF|];
    split;[exact Bytes|];split;[|exact Read].
  exact (curve_frame_two (generator_save_regs flag) br bg m mf eq_refl Frame).
Qed.

Theorem eval_generator_affine_all x y z flag m bp br :
  (forall mc w,Int64.unsigned w<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong w]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned w))))) ->
  bp<>br ->square_input_bounds x ->square_input_bounds y ->square_input_bounds z ->
  fe_at m bp 0 (words5 x) ->fe_at m bp 40 (words5 y) ->fe_at m bp 80 (words5 z) ->
  Mem.load Mint32 m bp 120=Some (Vint flag) ->modinfo_fe_state m ->
  Mem.range_perm m bp 0 128 Cur Freeable ->Mem.range_perm m br 0 88 Cur Freeable ->exists mf ox oy,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_gej_var)
    [Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero] E0 mf Vundef /\
  fe_at mf br 0 (words5 ox) /\fe_at mf br 40 (words5 oy) /\
  Mem.load Mint32 mf br 80=Some (Vint (if Int.eq flag Int.zero then Int.zero else Int.one)) /\
  square_input_bounds ox /\square_input_bounds oy /\
  (flag=Int.zero ->exists zi,radix_value zi=literal_invert_numeric (fe_inv_value z) /\
    ox=point_mul_words x (square_words zi) /\oy=point_mul_words y (point_mul_words zi (square_words zi)) /\
    radix_value ox mod feP=(radix_value x*(radix_value zi*radix_value zi)) mod feP /\
    radix_value oy mod feP=(radix_value y*(radix_value zi*(radix_value zi*radix_value zi))) mod feP) /\
  (flag<>Int.zero ->ox=generator_infinite_words /\oy=generator_infinite_words) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\Mem.range_perm mf br 0 88 Cur Freeable /\
  lframe (fun b _=>b<>bp /\b<>br) m mf /\readonly_preserved m mf.
Proof.
  intros Count Sep BX BY BZ X Y Z Flag Ready FP FR.
  destruct (Int.eq_dec flag Int.zero) as [->|Nonzero].
  - destruct (eval_affine_finite_initialized x y z m bp br Count Sep BX BY BZ X Y Z Flag Ready FP FR)
      as (zi & mf & Call & XO & YO & FlagO & FPF & FRF & BXO & BYO & Inverse & VX & VY & ReadyF & Frame & Read).
    exists mf,(point_mul_words x (square_words zi)),(point_mul_words y (point_mul_words zi (square_words zi))).
    rewrite Int.eq_true;split;[exact Call|];split;[exact XO|];split;[exact YO|];split;[exact FlagO|];
      split;[exact BXO|];split;[exact BYO|];split.
    + intro;exists zi;rewrite field_prime_matches_normalizer in VX,VY;
      split;[exact Inverse|];split;[reflexivity|];split;[reflexivity|];split;assumption.
    + split;[contradiction|];split;[exact FPF|];split;[exact FRF|];split;assumption.
  - destruct (eval_affine_infinite_owned m bp br flag Sep Nonzero Flag FP FR)
      as (mf & Call & XO & YO & FlagO & FPF & FRF & Frame & Read).
    exists mf,generator_infinite_words,generator_infinite_words;rewrite Int.eq_false by exact Nonzero.
    split;[exact Call|];split;[exact XO|];split;[exact YO|];split;[exact FlagO|];
      split;[exact generator_infinite_bounds|];split;[exact generator_infinite_bounds|];split;[contradiction|];split.
    + intro;split;reflexivity.
    + split;[exact FPF|];split;[exact FRF|];split;[|exact Read].
      eapply lframe_implies;[exact Frame|];intros b pos [_ Other] Valid;exact Other.
Qed.

Theorem eval_generator_affine_save x y z flag m bp br bg :
  (forall mc w,Int64.unsigned w<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong w]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned w))))) ->
  bp<>br ->bp<>bg ->br<>bg ->square_input_bounds x ->square_input_bounds y ->square_input_bounds z ->
  fe_at m bp 0 (words5 x) ->fe_at m bp 40 (words5 y) ->fe_at m bp 80 (words5 z) ->
  Mem.load Mint32 m bp 120=Some (Vint flag) ->modinfo_fe_state m ->
  Mem.range_perm m bp 0 128 Cur Freeable ->Mem.range_perm m br 0 88 Cur Freeable ->
  Mem.range_perm m bg 0 64 Cur Freeable ->exists ma mf ox oy,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_gej_var)
    [Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero] E0 ma Vundef /\
  Clight2.eval_funcall secp_ge ma (Internal f_secp256k1_generator_save)
    [Vptr bg Ptrofs.zero;Vptr br Ptrofs.zero] E0 mf Vundef /\
  (forall (second:bool) i,(i<32)%nat ->
    Mem.load Mint8unsigned mf bg ((if second then 32 else 0)+Z.of_nat i)=
      Some (Vint (nth i (map Int.repr (generator_saved_bytes (field_pair_valuation ox oy)
        (if second then 5 else 0))) Int.zero))) /\
  square_input_bounds ox /\square_input_bounds oy /\
  (flag=Int.zero ->exists zi,radix_value zi=literal_invert_numeric (fe_inv_value z) /\
    ox=point_mul_words x (square_words zi) /\oy=point_mul_words y (point_mul_words zi (square_words zi)) /\
    radix_value ox mod feP=(radix_value x*(radix_value zi*radix_value zi)) mod feP /\
    radix_value oy mod feP=(radix_value y*(radix_value zi*(radix_value zi*radix_value zi))) mod feP) /\
  (flag<>Int.zero ->ox=generator_infinite_words /\oy=generator_infinite_words) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\Mem.range_perm mf br 0 88 Cur Freeable /\Mem.range_perm mf bg 0 64 Cur Freeable /\
  lframe (fun b _=>b<>bp /\b<>br /\b<>bg) m mf /\readonly_preserved m mf.
Proof.
  intros Count PR PG RG BX BY BZ X Y Z Flag Ready FP FR FG.
  destruct (eval_generator_affine_all x y z flag m bp br Count PR BX BY BZ X Y Z Flag Ready FP FR)
    as (ma & ox & oy & Affine & XA & YA & FlagA & BXA & BYA & Finite & Infinite & FPA & FRA & FrameA & ReadA).
  assert (FGA:Mem.range_perm ma bg 0 64 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FG|exact FrameA|];intros;split;congruence. }
  destruct (eval_generator_save_fields ox oy (if Int.eq flag Int.zero then Int.zero else Int.one) ma br bg
    RG BXA BYA XA YA FlagA FRA FGA) as (mf & Save & FRF & FGF & FlagF & Bytes & FrameS & ReadS).
  assert (FPF:Mem.range_perm mf bp 0 128 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FPA|exact FrameS|];intros;split;assumption. }
  exists ma,mf,ox,oy;split;[exact Affine|];split;[exact Save|];split;[exact Bytes|];
    split;[exact BXA|];split;[exact BYA|];split;[exact Finite|];split;[exact Infinite|];
    split;[exact FPF|];split;[exact FRF|];split;[exact FGF|];split.
  - eapply lframe_trans.
    + eapply lframe_implies;[exact FrameA|];intros b pos [NP [NR NG]] Valid;split;assumption.
    + eapply lframe_implies;[exact FrameS|];intros b pos [NP [NR NG]] Valid;split;assumption.
  - eapply preserved_trans;[exact ReadA|exact ReadS].
Qed.

Definition generator_finish := statement_sequence
  (skipn 15 (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))))
  (snd (split_statement_last (fn_body f_secp256k1_generator_generate_internal))).
Definition generator_affine_stmt := nth 15
  (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))) Sskip.
Definition generator_save_stmt := nth 16
  (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))) Sskip.
Lemma generator_finish_source : generator_finish=Ssequence generator_affine_stmt
  (Ssequence generator_save_stmt (Sreturn (Some (Etempvar _ret tint)))).
Proof. reflexivity. Qed.
Lemma generator_affine_source : generator_affine_stmt=Scall None
  (Evar _secp256k1_ge_set_gej_var (type_of_function f_secp256k1_ge_set_gej_var))
  [Eaddrof (Evar _add curve_ge_type) (tptr curve_ge_type);
   Eaddrof (Evar _accum (Tstruct __6123 noattr)) (tptr (Tstruct __6123 noattr))].
Proof. reflexivity. Qed.
Lemma generator_save_source : generator_save_stmt=Scall None
  (Evar _secp256k1_generator_save (type_of_function f_secp256k1_generator_save))
  [Etempvar _gen (tptr (Tstruct __6563 noattr));Eaddrof (Evar _add curve_ge_type) (tptr curve_ge_type)].
Proof. reflexivity. Qed.
Lemma generator_finish_links :
  Genv.find_symbol secp_ge _secp256k1_ge_set_gej_var=Some (secp_symbol_block _secp256k1_ge_set_gej_var) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block _secp256k1_ge_set_gej_var) Ptrofs.zero)=Some (Internal f_secp256k1_ge_set_gej_var) /\
  Genv.find_symbol secp_ge _secp256k1_generator_save=Some (secp_symbol_block _secp256k1_generator_save) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block _secp256k1_generator_save) Ptrofs.zero)=Some (Internal f_secp256k1_generator_save).
Proof. vm_compute;repeat split;reflexivity. Qed.

Theorem exec_generator_finish e le m bp br bg x y z flag ret :
  (forall mc w,Int64.unsigned w<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong w]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned w))))) ->
  e!_accum=Some (bp,Tstruct __6123 noattr) ->e!_add=Some (br,curve_ge_type) ->
  e!_secp256k1_ge_set_gej_var=None ->e!_secp256k1_generator_save=None ->
  le!_gen=Some (Vptr bg Ptrofs.zero) ->le!_ret=Some (Vint ret) ->
  bp<>br ->bp<>bg ->br<>bg ->square_input_bounds x ->square_input_bounds y ->square_input_bounds z ->
  fe_at m bp 0 (words5 x) ->fe_at m bp 40 (words5 y) ->fe_at m bp 80 (words5 z) ->
  Mem.load Mint32 m bp 120=Some (Vint flag) ->
  Mem.range_perm m bp 0 128 Cur Freeable ->Mem.range_perm m br 0 88 Cur Freeable ->Mem.range_perm m bg 0 64 Cur Freeable ->
  secp_sha_startup m ->swu_startup m ->(forall prefix,generator_sha_prefix_state prefix m) ->exists mf ox oy,
  Clight2.exec_stmt secp_ge e le m generator_finish E0 le mf (Out_return (Some (Vint ret,tint))) /\
  (forall (second:bool) i,(i<32)%nat ->
    Mem.load Mint8unsigned mf bg ((if second then 32 else 0)+Z.of_nat i)=
      Some (Vint (nth i (map Int.repr (generator_saved_bytes (field_pair_valuation ox oy)
        (if second then 5 else 0))) Int.zero))) /\
  square_input_bounds ox /\square_input_bounds oy /\
  (flag=Int.zero ->exists zi,radix_value zi=literal_invert_numeric (fe_inv_value z) /\
    ox=point_mul_words x (square_words zi) /\oy=point_mul_words y (point_mul_words zi (square_words zi)) /\
    radix_value ox mod feP=(radix_value x*(radix_value zi*radix_value zi)) mod feP /\
    radix_value oy mod feP=(radix_value y*(radix_value zi*(radix_value zi*radix_value zi))) mod feP) /\
  (flag<>Int.zero ->ox=generator_infinite_words /\oy=generator_infinite_words) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\Mem.range_perm mf br 0 88 Cur Freeable /\Mem.range_perm mf bg 0 64 Cur Freeable /\
  lframe (fun b _=>b<>bp /\b<>br /\b<>bg) m mf /\readonly_preserved m mf /\
  secp_sha_startup mf /\swu_startup mf /\(forall prefix,generator_sha_prefix_state prefix mf).
Proof.
  intros Count Acc Add AffFun SaveFun Gen Ret PR PG RG BX BY BZ X Y Z Flag FP FR FG SHA SWU Prefix.
  destruct (eval_generator_affine_save x y z flag m bp br bg Count PR PG RG BX BY BZ X Y Z Flag (proj2 SWU) FP FR FG)
    as (ma & mf & ox & oy & Affine & Save & Bytes & BXO & BYO & Finite & Infinite & FPF & FRF & FGF & Frame & Read).
  destruct generator_finish_links as (AffSym & AffF & SaveSym & SaveF).
  assert (CA:Clight2.exec_stmt secp_ge e le m generator_affine_stmt E0 le ma Out_normal).
  { rewrite generator_affine_source;change le with (set_opttemp None Vundef le) at 2.
    eapply exec_Scall with (vf:=Vptr (secp_symbol_block _secp256k1_ge_set_gej_var) Ptrofs.zero)
      (vargs:=[Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero]) (f:=Internal f_secp256k1_ge_set_gej_var) (vres:=Vundef).
    - reflexivity.
    - eapply eval_Elvalue;[apply eval_Evar_global;[exact AffFun|exact AffSym]|apply deref_loc_reference;reflexivity].
    - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Add|reflexivity|].
      eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Acc|reflexivity|constructor].
    - exact AffF.
    - reflexivity.
    - exact Affine. }
  assert (CS:Clight2.exec_stmt secp_ge e le ma generator_save_stmt E0 le mf Out_normal).
  { rewrite generator_save_source;change le with (set_opttemp None Vundef le) at 2.
    eapply exec_Scall with (vf:=Vptr (secp_symbol_block _secp256k1_generator_save) Ptrofs.zero)
      (vargs:=[Vptr bg Ptrofs.zero;Vptr br Ptrofs.zero]) (f:=Internal f_secp256k1_generator_save) (vres:=Vundef).
    - reflexivity.
    - eapply eval_Elvalue;[apply eval_Evar_global;[exact SaveFun|exact SaveSym]|apply deref_loc_reference;reflexivity].
    - eapply eval_Econs;[apply eval_Etempvar;exact Gen|reflexivity|].
      eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact Add|reflexivity|constructor].
    - exact SaveF.
    - reflexivity.
    - exact Save. }
  exists mf,ox,oy;split.
  - rewrite generator_finish_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact CA|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact CS|].
    apply exec_Sreturn_some;apply eval_Etempvar;exact Ret.
  - split;[exact Bytes|];split;[exact BXO|];split;[exact BYO|];split;[exact Finite|];split;[exact Infinite|];
    split;[exact FPF|];split;[exact FRF|];split;[exact FGF|];split;[exact Frame|];split;[exact Read|];split.
    + eapply secp_sha_startup_preserved;[exact SHA|exact Read|exact Frame|].
      pose proof (proj1 (secp_sha_startup_separate m bp 128 SHA ltac:(lia) FP)) as P.
      pose proof (proj1 (secp_sha_startup_separate m br 88 SHA ltac:(lia) FR)) as R.
      pose proof (proj1 (secp_sha_startup_separate m bg 64 SHA ltac:(lia) FG)) as G.
      intros;repeat split;congruence.
    + split;[eapply swu_startup_preserved;[exact SWU|exact Read]|].
      intro prefix;eapply generator_sha_prefix_preserved;[apply Prefix|exact Read].
Qed.
