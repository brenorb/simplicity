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

Definition init_is64 d := match d with Init_int64 _ => true | _ => false end.
Definition init_word64 d := match d with Init_int64 x => x | _ => Int64.zero end.
Lemma init64_array_size ds : forallb init_is64 ds=true ->
 init_data_list_size ds=8*Z.of_nat (length ds).
Proof.
 induction ds as [|d ds IH];cbn [forallb length init_data_list_size];[reflexivity|].
 destruct d;cbn [init_is64 andb];try discriminate.
 intro H;rewrite IH by exact H;rewrite Nat2Z.inj_succ;cbn [init_data_size];lia.
Qed.

Lemma init64_array_loads {F V} (ge : Genv.t F V) ds m b : forall base,
 forallb init_is64 ds=true -> Genv.load_store_init_data ge m b base ds ->
 forall i,(i<length ds)%nat ->
 Mem.load Mint64 m b (base+8*Z.of_nat i)=Some (Vlong (init_word64 (nth i ds (Init_int64 Int64.zero)))).
Proof.
 induction ds as [|d ds IH];intros base All Loads i HI;[cbn in HI;lia|].
 destruct d;cbn [forallb init_is64 andb] in All;try discriminate.
 cbn [Genv.load_store_init_data] in Loads;destruct Loads as [Head Tail].
 destruct i;cbn [nth init_word64];[rewrite Z.mul_0_r,Z.add_0_r;exact Head|].
 replace (base+8*Z.of_nat (S i)) with (base+8+8*Z.of_nat i) by lia.
 apply IH;[exact All|exact Tail|cbn [length] in HI;lia].
Qed.

Definition generator_table_id (high : bool) := if high then _secp256k1_pre_g_128 else _secp256k1_pre_g.
Definition generator_table_global (high : bool) := if high then v_secp256k1_pre_g_128 else v_secp256k1_pre_g.
Definition generator_table_init high := gvar_init (generator_table_global high).
Definition generator_table_block high : block := secp_symbol_block (generator_table_id high).
Definition generator_table_word high i := init_word64 (nth i (generator_table_init high) (Init_int64 Int64.zero)).
Definition generator_entry_words high index i := generator_table_word high (8*index+i)%nat.

Lemma generator_table_length high : Z.of_nat (length (generator_table_init high))=65536.
Proof. destruct high;vm_compute;reflexivity. Qed.
Lemma generator_table_all64 high : forallb init_is64 (generator_table_init high)=true.
Proof. destruct high;vm_compute;reflexivity. Qed.
Lemma generator_table_size high : init_data_list_size (generator_table_init high)=524288.
Proof. rewrite init64_array_size by apply generator_table_all64;rewrite generator_table_length;reflexivity. Qed.
Lemma generator_table_readonly high : Genv.perm_globvar (generator_table_global high)=Readable.
Proof. destruct high;reflexivity. Qed.
Lemma generator_table_volatile high : gvar_volatile (generator_table_global high)=false.
Proof. destruct high;reflexivity. Qed.
Local Opaque v_secp256k1_pre_g v_secp256k1_pre_g_128.
Lemma generator_table_symbol high : Genv.find_symbol (genv_genv secp_ge) (generator_table_id high)=
 Some (generator_table_block high).
Proof. destruct high;vm_compute;reflexivity. Qed.
Lemma generator_table_info high : Genv.find_var_info (genv_genv secp_ge) (generator_table_block high)=
 Some (generator_table_global high).
Proof. destruct high;reflexivity. Qed.
Lemma generator_genv_projection : genv_genv secp_ge=Genv.globalenv jets_secp.prog.
Proof. reflexivity. Qed.
Local Opaque secp_ge generator_table_block generator_table_init generator_table_global.

Definition generator_table_rep high m :=
 Mem.valid_block m (generator_table_block high) /\
 Mem.range_perm m (generator_table_block high) 0 524288 Cur Readable /\
 forall i,Z.of_nat i<65536 -> Mem.load Mint64 m (generator_table_block high) (8*Z.of_nat i)=
 Some (Vlong (generator_table_word high i)).
Definition generator_table_state high m := generator_table_rep high m /\
 readonly_region_bounds m (generator_table_block high) 0 524288.

Theorem generator_table_initializes high m : Genv.init_mem jets_secp.prog=Some m ->
 generator_table_state high m.
Proof.
 intro Init;pose proof (generator_table_info high) as Info;rewrite generator_genv_projection in Info.
 destruct (Genv.init_mem_characterization jets_secp.prog _ Info Init) as (Range & Bounds & Loads & Bytes).
 change (Mem.range_perm m (generator_table_block high) 0 (init_data_list_size (generator_table_init high))
   Cur (Genv.perm_globvar (generator_table_global high))) in Range.
 rewrite generator_table_size,generator_table_readonly in Range.
 assert (Valid : Mem.valid_block m (generator_table_block high)) by
   (eapply Genv.find_var_info_not_fresh;eassumption).
 split.
 - split;[exact Valid|];split;[exact Range|].
   intros i HI;unfold generator_table_word.
   change (Mem.load Mint64 m (generator_table_block high) (0+8*Z.of_nat i)=
     Some (Vlong (init_word64 (nth i (generator_table_init high) (Init_int64 Int64.zero))))).
   apply (init64_array_loads (Genv.globalenv jets_secp.prog) (generator_table_init high));
     [apply generator_table_all64|apply Loads;apply generator_table_volatile|pose proof (generator_table_length high);lia].
 - intros ofs k p;split.
   + intro H;specialize (Bounds ofs k p H).
     change (0<=ofs<init_data_list_size (generator_table_init high) /\
       perm_order (Genv.perm_globvar (generator_table_global high)) p) in Bounds.
     rewrite generator_table_size,generator_table_readonly in Bounds;exact Bounds.
   + intros [HB HO];eapply Mem.perm_implies;[|exact HO].
     destruct k;[apply Mem.perm_cur_max;apply Range|apply Range];exact HB.
Qed.

Theorem generator_entry_readable high index m : Z.of_nat index<8192 -> generator_table_rep high m ->
 affine_storage_readable m (generator_table_block high) (64*Z.of_nat index) (generator_entry_words high index).
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

Lemma generator_table_rep_lframe high m mf P : generator_table_rep high m ->
 lframe P m mf -> (forall pos,P (generator_table_block high) pos) -> generator_table_rep high mf.
Proof.
 intros (HV & HP & HL) HF HOutside.
 split;[apply (proj2 (proj2 HF));exact HV|];split.
 - intros pos HI;apply (proj1 (proj2 HF));[exact HV|apply HOutside|apply HP;exact HI].
 - intros i HI;rewrite (proj1 HF Mint64 _ (8*Z.of_nat i) HV);
     [apply HL;exact HI|intros;apply HOutside].
Qed.

Theorem eval_generator_table_lookup high n m bout :
 0<Z.abs n<16384 -> generator_table_state high m -> Mem.range_perm m bout 0 88 Cur Freeable ->
 exists mf,
 ClightBigstep.Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_table_get_ge_storage)
 [Vptr bout Ptrofs.zero;Vptr (generator_table_block high) Ptrofs.zero;
  Vint (Int.repr n);Vint (Int.repr 15)] Events.E0 mf Vundef /\
 Mem.range_perm mf bout 0 88 Cur Freeable /\
 (forall k : bool,fe_at mf bout (if k then 40 else 0)
   (table_signed_coordinate (generator_entry_words high (Z.to_nat (table_storage_index n))) (negb (0<?n)) k)) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\ generator_table_state high mf /\
 lframe (fun b pos => b<>bout \/ pos<0 \/ 84<=pos) m mf.
Proof.
 intros Bound [Table RO] Free.
 assert (Sep : bout<>generator_table_block high).
 { intro E;subst bout.
   destruct (proj1 (RO 0 Cur Freeable) (Free 0 ltac:(lia))) as [_ Order];inversion Order. }
 pose proof (table_storage_index_bound n Bound) as Index.
 assert (NZ : Z.of_nat (Z.to_nat (table_storage_index n))=table_storage_index n)
   by (apply Z2Nat.id;lia).
 pose proof (generator_entry_readable high (Z.to_nat (table_storage_index n)) m
   ltac:(rewrite NZ;lia) Table) as Source.
 rewrite NZ in Source.
 destruct (eval_ecmult_table_get_ge_storage n
   (generator_entry_words high (Z.to_nat (table_storage_index n))) m bout (generator_table_block high)
   0 0 524288 Bound ltac:(lia) Sep Free Source RO)
   as (mf & Exec & Owned & Fields & Infinity & Input & RF & Frame).
 pose proof (generator_table_rep_lframe high m mf _ Table Frame
   ltac:(intro pos;left;congruence)) as TF.
 exists mf;split;[exact Exec|];split;[exact Owned|];split;[exact Fields|];
   split;[exact Infinity|];split;[split;assumption|exact Frame].
Qed.

Lemma generator_table_state_unchanged high m mf :
 Mem.unchanged_on (fun b _ => b=generator_table_block high) m mf ->
 generator_table_state high m -> generator_table_state high mf.
Proof.
 intros HU [Table Bounds];pose proof Table as [Valid _];split.
 - eapply generator_table_rep_lframe;[exact Table|apply lframe_unchanged;exact HU|intros;reflexivity].
 - intros ofs k p;split;intro H.
   + apply (proj1 (Bounds ofs k p)).
     eapply Mem.perm_unchanged_on_2;[exact HU|reflexivity|exact Valid|exact H].
   + eapply Mem.perm_unchanged_on;[exact HU|reflexivity|apply (proj2 (Bounds ofs k p));exact H].
Qed.

Lemma generator_table_state_alloc high m lo hi mf fresh :
 Mem.alloc m lo hi=(mf,fresh) -> generator_table_state high m -> generator_table_state high mf.
Proof.
 intros Alloc State;eapply generator_table_state_unchanged;[eapply Mem.alloc_unchanged_on;exact Alloc|exact State].
Qed.

Theorem generator_tables_initialized_memory_exists :
 exists m,Genv.init_mem jets_secp.prog=Some m /\
 generator_table_state false m /\ generator_table_state true m.
Proof.
 destruct beta_initialized_memory_exists as (m & Init & Beta).
 exists m;split;[exact Init|];split;apply generator_table_initializes;exact Init.
Qed.

Theorem generator_table_lookup_fresh high n : 0<Z.abs n<16384 ->
 exists m0 m bout mf,
 Genv.init_mem jets_secp.prog=Some m0 /\ Mem.alloc m0 0 88=(m,bout) /\
 ClightBigstep.Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_table_get_ge_storage)
 [Vptr bout Ptrofs.zero;Vptr (generator_table_block high) Ptrofs.zero;
  Vint (Int.repr n);Vint (Int.repr 15)] Events.E0 mf Vundef /\
 Mem.range_perm mf bout 0 88 Cur Freeable /\
 (forall k : bool,fe_at mf bout (if k then 40 else 0)
   (table_signed_coordinate (generator_entry_words high (Z.to_nat (table_storage_index n))) (negb (0<?n)) k)) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\ generator_table_state high mf /\
 lframe (fun b pos => b<>bout \/ pos<0 \/ 84<=pos) m mf.
Proof.
 intro Bound;destruct generator_tables_initialized_memory_exists as (m0 & Init & Low & High).
 assert (State : generator_table_state high m0) by (destruct high;assumption).
 destruct (Mem.alloc m0 0 88) as [m bout] eqn:Alloc.
 pose proof (generator_table_state_alloc high m0 0 88 m bout Alloc State) as Ready.
 assert (Owned : Mem.range_perm m bout 0 88 Cur Freeable).
 { intros pos HP;eapply Mem.perm_alloc_2;[exact Alloc|exact HP]. }
 destruct (eval_generator_table_lookup high n m bout Bound Ready Owned)
   as (mf & Call & Free & Fields & Infinity & Table & Frame).
 exists m0,m,bout,mf;split;[exact Init|];split;[exact Alloc|];split;[exact Call|];
   split;[exact Free|];split;[exact Fields|];split;[exact Infinity|];split;assumption.
Qed.
