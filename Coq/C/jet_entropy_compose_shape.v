(** Composition of the unchanged outer entropy function's exact statement tree.
    All call/store/free premises are internal and discharged by Local. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Values Events Globalenvs.
Require Import C.jets_elements C.jet_elements_linkage.
Require Import C.jet_frame_layout.
Require Import C.jet_entropy_frame_entry C.jet_entropy_compose_common C.jet_entropy_compose_inputs.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition entropy_helper_type := Tfunction
  (Tcons calc_mid_ptr (Tcons (tptr entropy_op) (Tcons calc_mid_ptr Tnil))) tvoid calc_cc.
Definition entropy_helper_statement :=
  Scall None (Evar _simplicity_generateIssuanceEntropy entropy_helper_type)
    [Eaddrof (Evar __res calc_mid) calc_mid_ptr;
     Eaddrof (Evar _op entropy_op) (tptr entropy_op);
     Eaddrof (Evar _contract calc_mid) calc_mid_ptr].
Definition entropy_jet_body :=
  Ssequence calc_copy_src
    (Ssequence (entropy_read_array entropy_txid_array)
      (Ssequence (Ssequence entropy_read_index entropy_store_index)
        (Ssequence (entropy_read_array entropy_contract_array)
          (Ssequence (Ssequence entropy_helper_statement calc_copy_result)
            (Ssequence calc_write (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))).

Lemma entropy_jet_body_shape : fn_body f_simplicity_calculate_issuance_entropy = entropy_jet_body.
Proof. reflexivity. Qed.

Lemma entropy_helper_symbol :
  Genv.find_symbol (Clight.genv_genv elements_ge) _simplicity_generateIssuanceEntropy =
    Some (elements_symbol_block _simplicity_generateIssuanceEntropy).
Proof. vm_compute; reflexivity. Qed.
Lemma entropy_helper_funct :
  Genv.find_funct (Clight.genv_genv elements_ge)
    (Vptr (elements_symbol_block _simplicity_generateIssuanceEntropy) Ptrofs.zero) =
    Some (Internal f_simplicity_generateIssuanceEntropy).
Proof. vm_compute; reflexivity. Qed.

Lemma exec_entropy_helper e le m mf bo bc bt :
  e!_simplicity_generateIssuanceEntropy = None ->
  e!__res = Some (bt, calc_mid) -> e!_op = Some (bo, entropy_op) ->
  e!_contract = Some (bc, calc_mid) ->
  Clight2.eval_funcall elements_ge m (Internal f_simplicity_generateIssuanceEntropy)
    [Vptr bt Ptrofs.zero; Vptr bo Ptrofs.zero; Vptr bc Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt elements_ge e le m entropy_helper_statement E0 le mf Out_normal.
Proof.
  intros HNone HT HO HC HCall. unfold entropy_helper_statement.
  change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (elements_symbol_block _simplicity_generateIssuanceEntropy) Ptrofs.zero)
    (f := Internal f_simplicity_generateIssuanceEntropy)
    (vargs := [Vptr bt Ptrofs.zero; Vptr bo Ptrofs.zero; Vptr bc Ptrofs.zero]) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact HNone|exact entropy_helper_symbol]|
      apply deref_loc_reference; reflexivity].
  - eapply eval_Econs; [apply calc_local_addr; exact HT|reflexivity|].
    eapply eval_Econs; [apply eval_Eaddrof, eval_Evar_local; exact HO|reflexivity|].
    eapply eval_Econs; [apply calc_local_addr; exact HC|reflexivity|apply eval_Enil].
  - exact entropy_helper_funct.
  - reflexivity.
  - exact HCall.
Qed.

Theorem entropy_function_composes env m m1 m2 m3 m4 m5 mcp mtx mi ms mr mt mc me mf
    bl bo bc br bt bd dbase bs sbase r bytes0 bytes1 :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs -> br <> bt ->
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 40 = (m2, bo) ->
  Mem.alloc m2 0 32 = (m3, bc) -> Mem.alloc m3 0 32 = (m4, br) ->
  Mem.alloc m4 0 32 = (m5, bt) ->
  Mem.loadbytes m5 bs sbase 16 = Some bytes0 -> Mem.storebytes m5 bl 0 bytes0 = Some mcp ->
  Clight2.eval_funcall elements_ge mcp (Internal f_read32s)
    [Vptr bo Ptrofs.zero; Vlong (Int64.repr 8); Vptr bl Ptrofs.zero] E0 mtx Vundef ->
  Clight2.eval_funcall elements_ge mtx (Internal f_simplicity_read32)
    [Vptr bl Ptrofs.zero] E0 mi (Vlong r) ->
  Mem.store Mint64 mi bo 32 (Vlong r) = Some ms ->
  Clight2.eval_funcall elements_ge ms (Internal f_read32s)
    [Vptr bc Ptrofs.zero; Vlong (Int64.repr 8); Vptr bl Ptrofs.zero] E0 mr Vundef ->
  Clight2.eval_funcall elements_ge mr (Internal f_simplicity_generateIssuanceEntropy)
    [Vptr bt Ptrofs.zero; Vptr bo Ptrofs.zero; Vptr bc Ptrofs.zero] E0 mt Vundef ->
  Mem.loadbytes mt bt 0 32 = Some bytes1 -> Mem.storebytes mt br 0 bytes1 = Some mc ->
  Clight2.eval_funcall elements_ge mc (Internal f_writeHash)
    [Vptr bd (Ptrofs.repr dbase); Vptr br Ptrofs.zero] E0 me Vundef ->
  Mem.free_list me [(bo, 0, 40); (bc, 0, 32); (bl, 0, 16); (bt, 0, 32); (br, 0, 32)] = Some mf ->
  Clight2.eval_funcall elements_ge m (Internal f_simplicity_calculate_issuance_entropy)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HA Hls Hrt A1 A2 A3 A4 A5 B0 S0 HCTX HCI SI HCC HCH B1 S1 HCW HFree.
  set (e := entropy_frame_env bl bo bc br bt).
  set (le := entropy_frame_temps env bd dbase bs sbase).
  set (li := PTree.set _t'1 (Vlong r) le).
  eapply eval_funcall_internal with (e := e) (le1 := le) (le2 := li) (m1 := m5) (m2 := me)
    (out := Out_return (Some (Vint Int.one, tint))).
  - exact (entropy_frame_entry env m m1 m2 m3 m4 m5 bl bo bc br bt bd dbase bs sbase A1 A2 A3 A4 A5).
  - rewrite entropy_jet_body_shape. unfold entropy_jet_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mcp) (le1 := le).
    + eapply exec_source_copy with (bs := bs) (sbase := sbase) (bytes := bytes0); try eassumption; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mtx) (le1 := le).
      * eapply exec_entropy_read_array with (bx := bo); try eassumption; try reflexivity.
        apply entropy_local_txid. reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ms) (le1 := li).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi) (le1 := li).
           ++ apply exec_entropy_read_index with (bl := bl); try eassumption; reflexivity.
           ++ apply exec_entropy_store_index with (bo := bo) (r := r); try eassumption; reflexivity.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := li).
           ++ eapply exec_entropy_read_array with (bx := bc); try eassumption; try reflexivity.
              apply calc_local_array. reflexivity.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := li).
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mt) (le1 := li).
                 --- eapply exec_entropy_helper; try eassumption; reflexivity.
                 --- eapply exec_calc_result_copy with (bytes := bytes1); try eassumption; reflexivity.
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := li).
                 --- eapply exec_calc_write; try eassumption; reflexivity.
                 --- apply exec_Sreturn_some, eval_Econst_int.
  - split; [discriminate|reflexivity].
  - unfold e. rewrite entropy_env_blocks. exact HFree.
Qed.
