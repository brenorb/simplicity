(** Actual frozen generator-table initializers: readable words and readonly
    permission bounds. This is initialization, not table/spec equivalence. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight Memory Values Globalenvs.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_affine_storage
 C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_table_decode C.jet_secp_table_index C.jet_secp_table_call
 C.jet_clight_readonly_frame C.jet_secp_beta_global.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Local Opaque v_secp256k1_pre_g v_secp256k1_pre_g_128.
Require Import C.jet_secp_table_internal C.jet_secp_generator_globals C.jet_elements_taptweak_program C.jet_elements_taptweak_pure
 C.jet_elements_taptweak_globals C.jet_elements_taptweak_startup C.jet_elements_taptweak_curve_transport
 C.jet_clight_internal_preserve.
Lemma elements_taptweak_has_table_get_ge_storage:
 In(_secp256k1_ecmult_table_get_ge_storage,f_secp256k1_ecmult_table_get_ge_storage)elements_taptweak_curve_helpers.
Proof.
 assert(Found:find(fun it=>Pos.eqb(fst it)_secp256k1_ecmult_table_get_ge_storage)elements_taptweak_curve_helpers=
 Some(_secp256k1_ecmult_table_get_ge_storage,f_secp256k1_ecmult_table_get_ge_storage))by(vm_compute;reflexivity).
 apply find_some in Found;exact(proj1 Found).
Qed.
From compcert Require Import Maps.
Require Import C.jet_elements_taptweak_import.
Lemma elements_taptweak_imported_variable_info id gv source:
 In id taptweak_import_names ->
 Genv.find_symbol (Genv.globalenv jets_secp.prog) id=Some source ->
 Genv.find_def (Genv.globalenv jets_secp.prog) source=Some(Gvar gv) ->
 Genv.find_var_info elements_taptweak_ge(elements_taptweak_symbol_block id)=Some gv.
Proof.
 intros Member Symbol Def.
 assert(Source:(AST.prog_defmap(Ctypes.program_of_program jets_secp.prog))!id=Some(Gvar gv)).
 { apply(proj2(@Genv.find_def_symbol Clight.fundef type (Ctypes.program_of_program jets_secp.prog) id (Gvar gv))).
   exists source;split;assumption. }
 assert(Target:(AST.prog_defmap(Ctypes.program_of_program elements_taptweak_linked_program))!id=Some(Gvar gv)).
 { rewrite elements_taptweak_program_ast_exact.
   exact(eq_trans(elements_taptweak_import_preserved id Member)Source). }
 destruct(proj1(@Genv.find_def_symbol Clight.fundef type
 (Ctypes.program_of_program elements_taptweak_linked_program)id(Gvar gv))Target)as(b & SymbolT & DefT).
 change(Genv.find_symbol elements_taptweak_ge id=Some b)in SymbolT.
 change(Genv.find_def elements_taptweak_ge b=Some(Gvar gv))in DefT.
 unfold elements_taptweak_symbol_block;rewrite SymbolT.
 unfold Genv.find_var_info;rewrite DefT;reflexivity.
Qed.
Lemma elements_taptweak_generator_imported high:
 In(generator_table_id high)taptweak_import_names.
Proof.
 assert(Found:existsb(Pos.eqb(generator_table_id high))taptweak_import_names=true)
 by(destruct high;vm_compute;reflexivity).
 apply existsb_exists in Found as(other & Member & Eq).
 apply Pos.eqb_eq in Eq;subst other;exact Member.
Qed.
Lemma elements_taptweak_source_generator_def high:
 Genv.find_def(Genv.globalenv jets_secp.prog)(generator_table_block high)=Some(Gvar(generator_table_global high)).
Proof. destruct high;reflexivity. Qed.
Definition elements_taptweak_generator_table_block high:block:=elements_taptweak_symbol_block(generator_table_id high).
Lemma elements_taptweak_generator_table_symbol high : Genv.find_symbol (genv_genv elements_taptweak_ge) (generator_table_id high)=
 Some (elements_taptweak_generator_table_block high).
Proof. destruct high;vm_compute;reflexivity. Qed.
Lemma elements_taptweak_generator_table_info high : Genv.find_var_info (genv_genv elements_taptweak_ge) (elements_taptweak_generator_table_block high)=
 Some (generator_table_global high).
Proof.
 apply(elements_taptweak_imported_variable_info (generator_table_id high) (generator_table_global high) (generator_table_block high)).
 - apply elements_taptweak_generator_imported.
 - rewrite <-generator_genv_projection;exact(generator_table_symbol high).
 - exact(elements_taptweak_source_generator_def high).
Qed.
Lemma elements_taptweak_generator_genv_projection : genv_genv elements_taptweak_ge=Genv.globalenv elements_taptweak_linked_program.
Proof. reflexivity. Qed.
Local Opaque elements_taptweak_linked_program elements_taptweak_ge elements_taptweak_generator_table_block generator_table_init generator_table_global.

Definition elements_taptweak_generator_table_rep high m :=
 Mem.valid_block m (elements_taptweak_generator_table_block high) /\
 Mem.range_perm m (elements_taptweak_generator_table_block high) 0 524288 Cur Readable /\
 forall i,Z.of_nat i<65536 -> Mem.load Mint64 m (elements_taptweak_generator_table_block high) (8*Z.of_nat i)=
 Some (Vlong (generator_table_word high i)).
Definition elements_taptweak_generator_table_state high m := elements_taptweak_generator_table_rep high m /\
 readonly_region_bounds m (elements_taptweak_generator_table_block high) 0 524288.

Theorem elements_taptweak_generator_table_initializes high m : Genv.init_mem elements_taptweak_linked_program=Some m ->
 elements_taptweak_generator_table_state high m.
Proof.
 intro Init;pose proof (elements_taptweak_generator_table_info high) as Info;rewrite elements_taptweak_generator_genv_projection in Info.
 destruct (Genv.init_mem_characterization elements_taptweak_linked_program _ Info Init) as (Range & Bounds & Loads & Bytes).
 change (Mem.range_perm m (elements_taptweak_generator_table_block high) 0 (init_data_list_size (generator_table_init high))
   Cur (Genv.perm_globvar (generator_table_global high))) in Range.
 rewrite generator_table_size,generator_table_readonly in Range.
 assert (Valid : Mem.valid_block m (elements_taptweak_generator_table_block high)) by
   (eapply Genv.find_var_info_not_fresh;eassumption).
 split.
 - split;[exact Valid|];split;[exact Range|].
   intros i HI;unfold generator_table_word.
   change (Mem.load Mint64 m (elements_taptweak_generator_table_block high) (0+8*Z.of_nat i)=
     Some (Vlong (init_word64 (nth i (generator_table_init high) (Init_int64 Int64.zero))))).
   apply (init64_array_loads (Genv.globalenv elements_taptweak_linked_program) (generator_table_init high));
     [apply generator_table_all64|apply Loads;apply generator_table_volatile|pose proof (generator_table_length high);lia].
 - intros ofs k p;split.
   + intro H;specialize (Bounds ofs k p H).
     change (0<=ofs<init_data_list_size (generator_table_init high) /\
       perm_order (Genv.perm_globvar (generator_table_global high)) p) in Bounds.
     rewrite generator_table_size,generator_table_readonly in Bounds;exact Bounds.
   + intros [HB HO];eapply Mem.perm_implies;[|exact HO].
     destruct k;[apply Mem.perm_cur_max;apply Range|apply Range];exact HB.
Qed.

Theorem elements_taptweak_generator_entry_readable high index m : Z.of_nat index<8192 -> elements_taptweak_generator_table_rep high m ->
 affine_storage_readable m (elements_taptweak_generator_table_block high) (64*Z.of_nat index) (generator_entry_words high index).
Proof.
 intros Index (Valid & Range & Loads).
 assert (ZI : 0<=Z.of_nat index<8192) by (pose proof (Nat2Z.is_nonneg index);lia).
 split;[lia|];split;[exists (8*Z.of_nat index);lia|];split.
 - change Ptrofs.max_unsigned with 18446744073709551615;lia.
 - split.
   + intros pos HP;apply Range;lia.
   + intros i HI;unfold generator_entry_words.
     replace (64*Z.of_nat index+8*Z.of_nat i) with (8*Z.of_nat (8*index+i))
       by (rewrite Nat2Z.inj_add,Nat2Z.inj_mul;cbn [Z.of_nat];ring).
     apply Loads;rewrite Nat2Z.inj_add,Nat2Z.inj_mul;cbn [Z.of_nat];lia.
Qed.

Lemma elements_taptweak_generator_table_rep_lframe high m mf P : elements_taptweak_generator_table_rep high m ->
 lframe P m mf -> (forall pos,P (elements_taptweak_generator_table_block high) pos) -> elements_taptweak_generator_table_rep high mf.
Proof.
 intros (HV & HP & HL) HF HOutside.
 split;[apply (proj2 (proj2 HF));exact HV|];split.
 - intros pos HI;apply (proj1 (proj2 HF));[exact HV|apply HOutside|apply HP;exact HI].
 - intros i HI;rewrite (proj1 HF Mint64 _ (8*Z.of_nat i) HV);
     [apply HL;exact HI|intros;apply HOutside].
Qed.

Theorem elements_taptweak_eval_generator_table_lookup high n m bout :
 0<Z.abs n<16384 -> elements_taptweak_generator_table_state high m -> Mem.range_perm m bout 0 88 Cur Freeable ->
 exists mf,
 ClightBigstep.Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_ecmult_table_get_ge_storage)
 [Vptr bout Ptrofs.zero;Vptr (elements_taptweak_generator_table_block high) Ptrofs.zero;
  Vint (Int.repr n);Vint (Int.repr 15)] Events.E0 mf Vundef /\
 Mem.range_perm mf bout 0 88 Cur Freeable /\
 (forall k : bool,fe_at mf bout (if k then 40 else 0)
   (table_signed_coordinate (generator_entry_words high (Z.to_nat (table_storage_index n))) (negb (0<?n)) k)) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\ elements_taptweak_generator_table_state high mf /\
 lframe (fun b pos => b<>bout \/ pos<0 \/ 84<=pos) m mf.
Proof.
 intros Bound [Table RO] Free.
 assert (Sep : bout<>elements_taptweak_generator_table_block high).
 { intro E;subst bout.
   destruct (proj1 (RO 0 Cur Freeable) (Free 0 ltac:(lia))) as [_ Order];inversion Order. }
 pose proof (table_storage_index_bound n Bound) as Index.
 assert (NZ : Z.of_nat (Z.to_nat (table_storage_index n))=table_storage_index n)
   by (apply Z2Nat.id;lia).
 pose proof (elements_taptweak_generator_entry_readable high (Z.to_nat (table_storage_index n)) m
   ltac:(rewrite NZ;lia) Table) as Source.
 rewrite NZ in Source.
 destruct (eval_ecmult_table_get_ge_storage_internal n
   (generator_entry_words high (Z.to_nat (table_storage_index n))) m bout (elements_taptweak_generator_table_block high)
   0 0 524288 Bound ltac:(lia) Sep Free Source RO)
   as (mf & Exec & Owned & Fields & Infinity & Input & RF & Frame).
 pose proof (elements_taptweak_generator_table_rep_lframe high m mf _ Table Frame
   ltac:(intro pos;left;congruence)) as TF.
 exists mf;split.
 { exact(elements_taptweak_curve_transport _ _ m _ _ mf _ elements_taptweak_has_table_get_ge_storage Exec). }
 split;[exact Owned|];split;[exact Fields|];
   split;[exact Infinity|];split;[split;assumption|exact Frame].
Qed.

Lemma elements_taptweak_generator_table_state_unchanged high m mf :
 Mem.unchanged_on (fun b _ => b=elements_taptweak_generator_table_block high) m mf ->
 elements_taptweak_generator_table_state high m -> elements_taptweak_generator_table_state high mf.
Proof.
 intros HU [Table Bounds];pose proof Table as [Valid _];split.
 - eapply elements_taptweak_generator_table_rep_lframe;[exact Table|apply lframe_unchanged;exact HU|intros;reflexivity].
 - intros ofs k p;split;intro H.
   + apply (proj1 (Bounds ofs k p)).
     eapply Mem.perm_unchanged_on_2;[exact HU|reflexivity|exact Valid|exact H].
   + eapply Mem.perm_unchanged_on;[exact HU|reflexivity|apply (proj2 (Bounds ofs k p));exact H].
Qed.

Lemma elements_taptweak_generator_table_state_alloc high m lo hi mf fresh :
 Mem.alloc m lo hi=(mf,fresh) -> elements_taptweak_generator_table_state high m -> elements_taptweak_generator_table_state high mf.
Proof.
 intros Alloc State;eapply elements_taptweak_generator_table_state_unchanged;[eapply Mem.alloc_unchanged_on;exact Alloc|exact State].
Qed.

Theorem elements_taptweak_generator_initial_memory:
 exists m,Genv.init_mem elements_taptweak_linked_program=Some m /\
 elements_taptweak_generator_table_state false m /\elements_taptweak_generator_table_state true m.
Proof.
 destruct elements_taptweak_initial_memory_exists as(m & Init);exists m;split;
 [exact Init|split;apply elements_taptweak_generator_table_initializes;exact Init].
Qed.
Theorem elements_taptweak_generator_readonly high m mf:
 elements_taptweak_generator_table_state high m ->readonly_preserved m mf ->elements_taptweak_generator_table_state high mf.
Proof.
 intros State [Forward Unchanged];pose proof State as[[Valid _] Bounds].
 eapply elements_taptweak_generator_table_state_unchanged;[|exact State].
 eapply Mem.unchanged_on_implies;[exact Unchanged|].
 intros b ofs Eq Valid';subst b;split;[exact Valid|].
 intros Write;destruct(proj1(Bounds ofs Max Writable)Write)as[_ Order];inversion Order.
Qed.
