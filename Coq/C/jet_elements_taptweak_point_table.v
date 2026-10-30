(** Original first-point table caller, reusing the verified table functions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_strauss_bits_max C.jet_secp_generator_globalz_call
 C.jet_secp_gej_copy_owned C.jet_secp_scalar_table_execution C.jet_secp_fe_nv
 C.jet_secp_square_columns C.jet_secp_point_mul_storage C.jet_secp_double_coordinate_numeric C.jet_secp_double_all_calls
 C.jet_secp_odd_table_loop C.jet_secp_odd_table_body C.jet_secp_scalar_table_literal C.jet_secp_table_field_equiv
 C.jet_secp_odd_table_literal_walk C.jet_secp_field_zero_owned
 C.jet_secp_globalz_loop C.jet_secp_globalz_word_walk C.jet_secp_globalz_pass2 C.jet_secp_field_mul_small
 C.jet_secp_rescale_literal C.jet_secp_multiply_normalize_bridge
 C.jet_secp_field_read_preservation C.jet_secp_slice_permissions
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Opaque secp_ge odd_table_final_state point_mul_words literal_scalar_table5.
Set Default Timeout 10.

Require Import C.jet_secp_generator_preprocess C.jet_secp_strauss_table_call C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_strauss_transport C.jet_elements_taptweak_curve_transport
 C.jet_elements_taptweak_load_body C.jet_elements_taptweak_beta_control C.jet_transport C.jet_transport_locals.
Definition elements_taptweak_preprocess_pure_statements:=
 [generator_preprocess_check;strauss_after_bits_max;strauss_table_prepare].
Lemma elements_taptweak_preprocess_pure_checked:
 forallb(locals_stmt_okb secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)))elements_taptweak_preprocess_pure_statements=true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_has_table_set_globalz:
 In(_secp256k1_ge_table_set_globalz,f_secp256k1_ge_table_set_globalz)elements_taptweak_curve_helpers.
Proof.
 assert(Found:find(fun it=>Pos.eqb(fst it)_secp256k1_ge_table_set_globalz)elements_taptweak_curve_helpers=
 Some(_secp256k1_ge_table_set_globalz,f_secp256k1_ge_table_set_globalz))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_curve_helpers.
Lemma elements_taptweak_preprocess_pure_transport e le m stmt trace lef mf out:
 edom e(fn_vars f_secp256k1_ecmult_strauss_wnaf) ->
 (forall id,In id(map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)) ->exists b ty,e!id=Some(b,ty)) ->
 In stmt elements_taptweak_preprocess_pure_statements ->
 Clight2.exec_stmt secp_ge e le m stmt trace lef mf out ->
 Clight2.exec_stmt elements_taptweak_ge e le m stmt trace lef mf out.
Proof.
 intros Domain Bound Member Run.
 eapply(proj1(locals_transport_main secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (locals_transportable_of_entries secp_ge elements_taptweak_ge elements_taptweak_curve_helpers
 elements_taptweak_curve_entries elements_taptweak_curve_ok)));
 [exact Run|exact Domain|exact Bound|].
 pose proof elements_taptweak_preprocess_pure_checked as Checked.
 rewrite forallb_forall in Checked;exact(Checked stmt Member).
Qed.
Lemma eval_elements_taptweak_strauss_table_width e le m :
 eval_expr elements_taptweak_ge e le m strauss_table_width (Vlong (Int64.repr 8)).
Proof.
 unfold strauss_table_width;eapply eval_Ebinop with (v1:=Vlong Int64.one) (v2:=Vint (Int.repr 3));
  [constructor|eapply eval_Ebinop;[constructor|constructor|reflexivity]|reflexivity].
Qed.
Lemma eval_elements_taptweak_strauss_globalz_count e le m : le!_no=Some (Vlong Int64.one) ->
 eval_expr elements_taptweak_ge e le m generator_globalz_count (Vlong (Int64.repr 8)).
Proof.
 intro No;unfold generator_globalz_count;eapply eval_Ebinop with
  (v1:=Vlong (Int64.repr 8)) (v2:=Vlong Int64.one);
  [apply eval_elements_taptweak_strauss_table_width|apply eval_Etempvar;exact No|reflexivity].
Qed.
Lemma exec_elements_taptweak_strauss_globalz_from_call e le m mf bs bt bx :
 e!_secp256k1_ge_table_set_globalz=None -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_no=Some (Vlong Int64.one) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_ge_table_set_globalz)
  [Vlong (Int64.repr 8);Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt elements_taptweak_ge e le m generator_globalz_statement E0
  (generator_globalz_call_temps le (Vptr bt Ptrofs.zero) (Vptr bx Ptrofs.zero)) mf Out_normal.
Proof.
 intros Symbol State No Table Aux Call;rewrite generator_globalz_statement_source.
 pose (lt:=PTree.set _t'32 (Vptr bt Ptrofs.zero) le).
 pose (lx:=generator_globalz_call_temps le (Vptr bt Ptrofs.zero) (Vptr bx Ptrofs.zero)).
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lt) (m1:=m).
 - apply exec_Sset;eapply eval_elements_taptweak_state_pointer with (base:=0) (delta:=8);
   [left;reflexivity|exact State|lia|change Ptrofs.max_unsigned with 18446744073709551615;lia|exact Table].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lx) (m1:=m).
   + apply exec_Sset;eapply eval_elements_taptweak_state_pointer with (base:=0) (delta:=0).
     * right;left;reflexivity.
     * unfold lt;rewrite PTree.gso by discriminate;exact State.
     * lia.
     * change Ptrofs.max_unsigned with 18446744073709551615;lia.
     * exact Aux.
   + eapply exec_elements_taptweak_arith_call with
     (vargs:=[Vlong (Int64.repr 8);Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero]) (v:=Vundef).
     * exact elements_taptweak_has_table_set_globalz.
     * exact Symbol.
     * eapply eval_Econs with (v1:=Vlong (Int64.repr 8)).
       -- apply eval_elements_taptweak_strauss_globalz_count;unfold lx,generator_globalz_call_temps;
          rewrite !PTree.gso by discriminate;exact No.
       -- reflexivity.
       -- eapply eval_Econs with (v1:=Vptr bt Ptrofs.zero).
          ++ apply eval_Etempvar;unfold lx,generator_globalz_call_temps;rewrite PTree.gso by discriminate;apply PTree.gss.
          ++ reflexivity.
          ++ eapply eval_Econs with (v1:=Vptr bx Ptrofs.zero);
             [apply eval_Etempvar;unfold lx,generator_globalz_call_temps;apply PTree.gss|reflexivity|constructor].
     * exact Call.
Qed.
Theorem exec_elements_taptweak_strauss_table_prepare e le m ba bs bt bx bo bj x y z
 (ax ay az:Ty.tySem (Word 8)) :
 edom e(fn_vars f_secp256k1_ecmult_strauss_wnaf) ->
 (forall id,In id(map fst(fn_vars f_secp256k1_ecmult_strauss_wnaf)) ->exists b ty,e!id=Some(b,ty)) ->
 e!_Z=Some (bo,Tstruct __5467 noattr) -> e!_tmp=Some (bj,Tstruct __6123 noattr) ->
 e!_secp256k1_ecmult_odd_multiples_table=None -> e!_secp256k1_ge_table_set_globalz=None ->
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_np=Some (Vlong Int64.zero) ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_no=Some (Vlong Int64.zero) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 (forall b hi,In (b,hi) [(bs,24);(ba,128);(bj,128);(bt,704);(bx,320);(bo,40)] ->
  Mem.range_perm m b 0 hi Cur Freeable) -> NoDup [ba;bs;bt;bx;bo;bj] ->
 table_word_literal x ax -> table_word_literal y ay -> table_word_literal z az -> field_zero_result z=Int.zero ->
 let sf:=odd_table_final_state x y z in exists mf xf yf,
 Clight2.exec_stmt elements_taptweak_ge e le m strauss_table_prepare E0 (strauss_table_prepare_temps le bt bx) mf Out_normal /\
 globalz_table_rep mf bt xf yf /\ globalz_table_bounds xf yf /\
 (forall k,(k<8)%nat -> mul_small_input_bounds (yf k)) /\
 fe_at mf bo 0 (words5 (point_mul_words (odd_table_z sf) (double_output_z_words y z))) /\
 square_input_bounds (point_mul_words (odd_table_z sf) (double_output_z_words y z)) /\
 (rescale_field_output (point_mul_words (odd_table_z sf) (double_output_z_words y z)),
  globalz_word_vector (globalz_decoded_points xf yf))=@literal_scalar_table5 Alg.CoreFunSem ((ax,ay),az) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
 Mem.load Mint32 mf ba 120=Some (Vint Int.zero) /\
 Mem.load Mptr mf bs 8=Some (Vptr bt Ptrofs.zero) /\ Mem.load Mptr mf bs 0=Some (Vptr bx Ptrofs.zero) /\
 (forall b hi,In (b,hi) [(bs,24);(ba,128);(bj,128);(bt,704);(bx,320);(bo,40)] ->
  Mem.range_perm mf b 0 hi Cur Freeable) /\ keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun b _=>b<>bt /\ b<>bj /\ b<>bx /\ b<>bo) m mf /\
 (strauss_table_prepare_temps le bt bx)!_no=Some (Vlong Int64.one) /\
 (forall id,~In id [_no;_t'32;_t'33;_t'36;_t'37] ->
  (strauss_table_prepare_temps le bt bx)!id=le!id) /\
 (exists m1,
  Clight2.exec_stmt elements_taptweak_ge e le m strauss_after_bits_max E0 (strauss_first_table_temps le bt bx) m1 Out_normal /\
  Clight2.eval_funcall elements_taptweak_ge m1 (Internal f_secp256k1_ge_table_set_globalz)
   [Vlong (Int64.repr 8);Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero] E0 mf Vundef /\
  Mem.load Mptr m1 bs 8=Some (Vptr bt Ptrofs.zero) /\ Mem.load Mptr m1 bs 0=Some (Vptr bx Ptrofs.zero)).
Proof.
 intros Domain Bound LocalZ LocalTmp OddSymbol GlobalSymbol A NP State No Table Aux BX BY BZ X Y Z Flag Owned Separate HX HY HZ Finite;cbv zeta.
 destruct(exec_strauss_table_prepare e le m ba bs bt bx bo bj x y z ax ay az LocalZ LocalTmp OddSymbol GlobalSymbol A NP State No Table Aux BX BY BZ X Y Z Flag Owned Separate HX HY HZ Finite)
 as(mf & xf & yf & Run & TableF & BoundsF & TightY & Product & ProductBound & Literal & XA & YA & ZA & FlagA & TableFinal & AuxFinal & OwnedF & Keep & Readonly & Frame & NoF & Other & m1 & Caller & Global & Table1 & Aux1).
 exists mf,xf,yf;split.
 - eapply elements_taptweak_preprocess_pure_transport;[exact Domain|exact Bound|right;right;left;reflexivity|exact Run].
 - split;[exact TableF|];split;[exact BoundsF|];split;[exact TightY|];split;[exact Product|];
   split;[exact ProductBound|];split;[exact Literal|];split;[exact XA|];split;[exact YA|];split;[exact ZA|];
   split;[exact FlagA|];split;[exact TableFinal|];split;[exact AuxFinal|];split;[exact OwnedF|];
   split;[exact Keep|];split;[exact Readonly|];split;[exact Frame|];split;[exact NoF|];split;[exact Other|].
   exists m1;split.
   + eapply elements_taptweak_preprocess_pure_transport;[exact Domain|exact Bound|right;left;reflexivity|exact Caller].
   + split.
     * eapply elements_taptweak_curve_transport;[exact elements_taptweak_has_table_set_globalz|exact Global].
     * split;[exact Table1|exact Aux1].
Qed.
