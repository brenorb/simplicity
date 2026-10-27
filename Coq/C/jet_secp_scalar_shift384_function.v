(** Whole original scalar_mul_shift_var at shift 384. The incoming operand
    representation permits the second scalar to be a readonly global. The
    destination is caller-owned and distinct from both retained operands. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
 C.jet_sx_u64_transport C.jet_sx_region_lframe C.jet_secp_linkage C.jets_secp
 C.jet_secp_scalar_shift384_control C.jet_secp_scalar_shift384_stores C.jet_secp_scalar_shift384_numeric
 C.jet_secp_scalar_shift384_suffix C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_add_reader_support C.jet_secp_scalar_mul_caller_body C.jet_secp_scalar_mul_caller_alloc
 C.jet_secp_scalar_mul512_run C.jet_secp_scalar_mul512_borrowed C.jet_secp_scalar_mul512_owned_product
 C.jet_secp_scalar_mul512_machine C.jet_secp_scalar_mul512_low C.jet_secp_scalar_mul512_accumulate
 C.jet_secp_scalar_mul512_product
 C.jet_secp_scalar_mul_borrowed_alloc C.jet_secp_scalar_mul_borrowed_function
 C.jet_secp_slice_permissions C.jet_secp_closed_helpers C.jet_clight_internal_frame
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition shift384_entry_temps beta br := PTree.set _shift (Vint (Int.repr 384))
 (PTree.set _b (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1)))
 (PTree.set _a (Vptr (blk beta 0) (Ptrofs.repr (bas beta 0)))
 (PTree.set _r (Vptr br Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_scalar_mul_shift_var))))).
Definition shift384_output_value rho :=
 (scalar_mul512_input_value rho 0*scalar_mul512_input_value rho 4+2^383)/2^384.

Lemma shift384_entry beta br m ma bl : Mem.alloc m 0 64=(ma,bl) ->
 function_entry2 secp_ge f_secp256k1_scalar_mul_shift_var
 [Vptr br Ptrofs.zero;Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
  Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));Vint (Int.repr 384)]
 m (shift384_env bl) (shift384_entry_temps beta br) ma.
Proof.
 intro Alloc;assert (Ok:fn_okb f_secp256k1_scalar_mul_shift_var=true) by reflexivity.
 destruct (fn_okb_true _ Ok) as (Vars & Params & Disjoint).
 constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
 eapply alloc_variables_cons;[exact Alloc|constructor].
Qed.
Lemma shift384_closed : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_scalar_mul_shift_var)=true.
Proof. timeout 10 (vm_compute;reflexivity). Qed.
Lemma shift384_product_closed : closed_stmtb secp_closed_helpers (fn_body f_secp256k1_scalar_mul_512)=true.
Proof. timeout 10 (vm_compute;reflexivity). Qed.

Lemma shift384_inputs_after_product rho beta bl m mp : rep rho beta scalar_mul_borrowed_inputs m ->
 rep rho (scalar_mul_stack_layout beta bl) scalar_mul512_borrowed_output_regs mp ->
 rep rho beta scalar_mul_borrowed_inputs mp.
Proof.
 intros (Length & Sep & Regions) Product;split;[exact Length|];split;[exact Sep|].
 intros r reg Nth;destruct r as [|[|r]];
 cbn [scalar_mul_borrowed_inputs nth_error] in Nth;try (destruct r;discriminate);injection Nth as <-.
 - eapply region_u64_transport with (beta:=scalar_mul_stack_layout beta bl) (r:=1%nat)
   (rho:=rho) (rho':=rho) (xs:=[XLv 0;XLv 1;XLv 2;XLv 3])
   (ys:=[XLv 0;XLv 1;XLv 2;XLv 3]) (w:=true) (owned:=Some 32);
   try reflexivity;exact (rep_region _ _ _ _ 1 _ Product eq_refl).
 - eapply region_u64_transport with (beta:=scalar_mul_stack_layout beta bl) (r:=2%nat)
   (rho:=rho) (rho':=rho) (xs:=[XLv 4;XLv 5;XLv 6;XLv 7])
   (ys:=[XLv 4;XLv 5;XLv 6;XLv 7]) (w:=false) (owned:=None);
   try reflexivity;exact (rep_region _ _ _ _ 2 _ Product eq_refl).
Qed.

Lemma shift384_inputs_lframe rho beta ma mb P : rep rho beta scalar_mul_borrowed_inputs ma ->
 lframe P ma mb -> (forall r pos,(r<2)%nat -> P (blk beta r) pos) ->
 rep rho beta scalar_mul_borrowed_inputs mb.
Proof.
 intros (Length & Sep & Regions) Frame Preserved;split;[exact Length|];split;[exact Sep|].
 intros r reg Nth;eapply region_ok_lframe;[exact Frame| |exact (Regions r reg Nth)].
 intro pos;apply Preserved;change (r<length scalar_mul_borrowed_inputs)%nat.
 apply nth_error_Some;congruence.
Qed.

Lemma shift384_machine_value rho :
 shift384_product_value (fun j=>nth j (scalar_mul512_machine_outputs rho) Int64.zero)=
 scalar_mul512_input_value rho 0*scalar_mul512_input_value rho 4.
Proof.
 change (column_words_value (scalar_mul512_machine_outputs rho)=
  scalar_mul512_input_value rho 0*scalar_mul512_input_value rho 4).
 apply scalar_mul512_machine_product.
Qed.
Corollary shift384_output_bounds rho : 0<=shift384_output_value rho<=2^128.
Proof.
 unfold shift384_output_value;rewrite <-(shift384_machine_value rho);apply shift384_rounded_bounds.
Qed.

Theorem eval_scalar_mul_shift384_borrowed rho beta m br :
 rep rho beta scalar_mul_borrowed_inputs m -> Mem.range_perm m br 0 32 Cur Freeable ->
 (forall r,(r<2)%nat -> br<>blk beta r) ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul_shift_var)
 [Vptr br Ptrofs.zero;Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
  Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));Vint (Int.repr 384)] E0 mf Vundef /\
 scalar_at mf br 0 (map Int64.repr (scalar_limbs_of (shift384_output_value rho))) /\
 rep rho beta scalar_mul_borrowed_inputs mf /\ Mem.range_perm mf br 0 32 Cur Freeable /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun b ofs=>b<>br /\ ~foot beta (map rshape scalar_mul_borrowed_inputs) b ofs) m mf.
Proof.
 intros Inputs Free Separate;destruct (Mem.alloc m 0 64) as [ma bl] eqn:Alloc.
 pose proof (scalar_mul_borrowed_allocates rho beta m ma bl Inputs Alloc) as Initial.
 destruct (eval_scalar_mul512_borrowed_product rho (scalar_mul_stack_layout beta bl) ma Initial)
  as (mp & ProductCall & Loads & Value & ProductRep & ProductFrame).
 set (w:=fun j=>nth j (scalar_mul512_machine_outputs rho) Int64.zero).
 assert (Product:shift384_product w bl mp).
 { intros j J;apply Loads;unfold w;apply nth_error_nth';rewrite scalar_mul512_machine_length;exact J. }
 assert (ProductValue:shift384_product_value w=scalar_mul512_input_value rho 0*scalar_mul512_input_value rho 4).
 { apply shift384_machine_value. }
 assert (KeepP:keeps_permissions ma mp).
 { eapply secp_internal_keeps_permissions;[exact shift384_product_closed|reflexivity|exact ProductCall]. }
 assert (FreeP:Mem.range_perm mp br 0 32 Cur Freeable).
 { intros pos Range;apply KeepP;eapply Mem.perm_alloc_1;[exact Alloc|apply Free;exact Range]. }
 assert (Fresh:~Mem.valid_block m bl) by (eapply Mem.fresh_block_alloc;exact Alloc).
 assert (Different:br<>bl).
 { intro Eq;apply Fresh;rewrite <-Eq;eapply Mem.perm_valid_block;apply (Free 0);lia. }
 set (le:=shift384_entry_temps beta br).
 assert (R:le!_r=Some (Vptr br Ptrofs.zero)) by reflexivity.
 assert (Shift:le!_shift=Some (Vint (Int.repr 384))) by reflexivity.
 destruct (exec_shift384_suffix w (shift384_env bl) le mp br bl Different eq_refl eq_refl R Shift Product FreeP)
  as (lef & mb & Suffix & Output & ProductF & FreeB & KeepS & SuffixFrame).
 rewrite ProductValue in Output;change (scalar_at mb br 0 (map Int64.repr (scalar_limbs_of (shift384_output_value rho)))) in Output.
 assert (FreeL:Mem.range_perm mb bl 0 64 Cur Freeable).
 { pose proof (rep_region _ _ _ mp 0 _ ProductRep eq_refl) as (_ & _ & _ & _ & (_ & _ & FL & _)).
   intros pos Range;apply KeepS;apply FL;exact Range. }
 destruct (free_list_exists [(bl,0,64)] mb) as (mf & Freed & Unchanged).
 { constructor;[cbn;tauto|constructor]. }
 { intros b lo hi [Eq|[]];injection Eq as <- <- <-;exact FreeL. }
 assert (FreeFrame:lframe (fun b _=>b<>bl) mb mf).
 { apply lframe_unchanged;eapply Mem.unchanged_on_implies;[exact Unchanged|].
   intros b pos Away Valid;change (~(bl=b \/ False));intros [Eq|[]];congruence. }
 assert (InputValid:forall r,(r<2)%nat -> Mem.valid_block m (blk beta r)).
 { intros r J;apply (scalar_mul_borrowed_inputs_valid rho beta m Inputs);apply blk_in;destruct Inputs as (Len & _);rewrite Len;exact J. }
 assert (NotLocal:forall r,(r<2)%nat -> blk beta r<>bl).
 { intros r J Eq;apply Fresh;rewrite <-Eq;apply InputValid;exact J. }
 assert (InputsP:rep rho beta scalar_mul_borrowed_inputs mp)
  by exact (shift384_inputs_after_product rho beta bl m mp Inputs ProductRep).
 assert (InputsB:rep rho beta scalar_mul_borrowed_inputs mb).
 { eapply shift384_inputs_lframe;[exact InputsP|exact SuffixFrame|intros;intro Eq;apply (Separate r H);symmetry;exact Eq]. }
 assert (InputsF:rep rho beta scalar_mul_borrowed_inputs mf).
 { eapply shift384_inputs_lframe;[exact InputsB|exact FreeFrame|intros;apply NotLocal;assumption]. }
 assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul_shift_var)
  [Vptr br Ptrofs.zero;Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
   Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));Vint (Int.repr 384)] E0 mf Vundef).
 { eapply eval_funcall_internal with (e:=shift384_env bl) (le1:=le) (le2:=lef)
   (m1:=ma) (m2:=mb) (out:=Out_normal).
   - apply shift384_entry;exact Alloc.
   - rewrite shift384_suffix_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ma) (le1:=le).
     + eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=ma) (le1:=le)
       (out1:=Out_normal) (out2:=Out_break);constructor.
     + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mp) (le1:=le).
       * change (Clight2.exec_stmt secp_ge (scalar_mul_caller_env (scalar_mul_stack_layout beta bl)) le ma
          scalar_mul_product_stmt E0 le mp Out_normal).
         apply exec_scalar_mul_product_call;try reflexivity;exact ProductCall.
       * exact Suffix.
   - constructor.
   - exact Freed. }
 exists mf;split;[exact Call|];split.
 - eapply scalar_at_lframe;[exact Output|exact FreeFrame|intros;exact Different].
 - split;[exact InputsF|];split.
   + intros pos Range;apply (proj1 (proj2 FreeFrame)) with (b:=br);
     [eapply Mem.perm_valid_block;apply (FreeB 0);lia|exact Different|apply FreeB;exact Range].
   + split.
     * eapply secp_internal_keeps_permissions;[exact shift384_closed|reflexivity|exact Call].
     * split.
       { eapply (secp_closed_function_preserved f_secp256k1_scalar_mul_shift_var);[exact shift384_closed|reflexivity|exact Call]. }
       set (P:=fun b ofs=>Mem.valid_block m b /\ b<>br /\ ~foot beta (map rshape scalar_mul_borrowed_inputs) b ofs).
       assert (Frame:lframe P m mf).
       { eapply lframe_trans with (m2:=ma).
         - apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc.
         - eapply lframe_trans with (m2:=mp).
           + eapply lframe_implies;[exact ProductFrame|].
             intros b ofs (Valid & NE & Outside) ValidA Foot.
             destruct (borrowed_stack_foot_cases beta bl b ofs Foot) as [Eq|Inside];
              [subst b;contradiction|contradiction].
           + eapply lframe_trans with (m2:=mb).
             * eapply lframe_implies;[exact SuffixFrame|];intros b ofs (Valid & NE & Outside) ValidP;exact NE.
             * eapply lframe_implies;[exact FreeFrame|];intros b ofs (Valid & NE & Outside) ValidB Eq;subst b;contradiction. }
       eapply lframe_implies;[exact Frame|];intros b ofs Outside Valid;split;[exact Valid|exact Outside].
Qed.
