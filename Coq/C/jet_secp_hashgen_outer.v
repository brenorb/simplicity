(** Original generator_generate wrapper: both pointer checks, NULL-blinding
    call, result conversion and return. The public jet still supplies its
    fresh key/gen allocations and frame lifecycle. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.extraMath C.jet_memcpy_model C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_field_cmov C.jet_buffer_input C.jet_read8s_layout C.jet_clight_internal_preserve
 C.jet_secp_sha_startup C.jet_secp_swu_startup C.jet_secp_generator_sha_absorb
 C.jet_secp_generator_hash_map C.jet_secp_hashgen_function.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition hashgen_nonnull_check id ty := Sloop
 (Sifthenelse (Eunop Onotbool (Ebinop One (Etempvar id (tptr ty))
   (Ecast (Econst_int Int.zero tint) (tptr tvoid)) tint) tint)
   (Sreturn (Some (Econst_int Int.zero tint))) Sskip) Sbreak.
Definition hashgen_outer_temps bg ba oa := PTree.set _key32 (Vptr ba oa)
 (PTree.set _gen (Vptr bg Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_generator_generate))).
Definition hashgen_outer_call := Scall (Some _t'1)
 (Evar _secp256k1_generator_generate_internal (type_of_function f_secp256k1_generator_generate_internal))
 [Etempvar _gen (tptr (Tstruct __6563 noattr));Etempvar _key32 (tptr tuchar);
  Ecast (Econst_int Int.zero tint) (tptr tvoid)].
Lemma hashgen_outer_source : fn_body f_secp256k1_generator_generate=
 Ssequence (hashgen_nonnull_check _gen (Tstruct __6563 noattr))
 (Ssequence (hashgen_nonnull_check _key32 tuchar)
 (Ssequence hashgen_outer_call (Sreturn (Some (Etempvar _t'1 tint))))).
Proof. reflexivity. Qed.
Lemma hashgen_outer_entry m bg ba oa : function_entry2 secp_ge f_secp256k1_generator_generate
 [Vptr bg Ptrofs.zero;Vptr ba oa] m empty_env (hashgen_outer_temps bg ba oa) m.
Proof.
 assert (Ok:fn_okb f_secp256k1_generator_generate=true) by reflexivity.
 destruct (fn_okb_true _ Ok) as (Vars & Params & Disjoint).
 constructor;[exact Vars|exact Params|exact Disjoint|constructor|reflexivity].
Qed.
Lemma hashgen_outer_link :
 Genv.find_symbol secp_ge _secp256k1_generator_generate_internal=
   Some (secp_symbol_block _secp256k1_generator_generate_internal) /\
 Genv.find_funct secp_ge (Vptr (secp_symbol_block _secp256k1_generator_generate_internal) Ptrofs.zero)=
   Some (Internal f_secp256k1_generator_generate_internal).
Proof. vm_compute;split;reflexivity. Qed.
Local Opaque secp_ge.

Lemma exec_hashgen_nonnull e le m id ty b ofs : le!id=Some (Vptr b ofs) ->
 Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs)=true ->
 Clight2.exec_stmt secp_ge e le m (hashgen_nonnull_check id ty) E0 le m Out_normal.
Proof.
 intros Pointer Valid;unfold hashgen_nonnull_check.
 change E0 with (E0**E0);eapply exec_Sloop_stop2 with (out1:=Out_normal) (out2:=Out_break).
 - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
   eapply eval_Eunop with (v1:=Vint Int.one);[|reflexivity].
   eapply eval_Ebinop with (v1:=Vptr b ofs) (v2:=Vlong Int64.zero).
   + apply eval_Etempvar;exact Pointer.
   + eapply eval_Ecast;[constructor|reflexivity].
   + change (option_map Val.of_bool
       (if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some true else None)=Some (Vint Int.one)).
     rewrite Valid;reflexivity.
 - constructor.
 - constructor.
 - constructor.
Qed.

Theorem eval_hashgen_generate (Hmodel:memcpy_model) (key:Ty.tySem (Word 8)) m bg ba oa :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
     E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
 ba<>bg ->Ptrofs.unsigned oa+32<=Ptrofs.max_unsigned ->
 secp_sha_startup m ->swu_startup m ->(forall prefix,generator_sha_prefix_state prefix m) ->
 Mem.range_perm m bg 0 64 Cur Freeable ->
 (forall i,(i<32)%nat ->Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa+Z.of_nat i)=
   Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))) ->
 exists mf sx sy sz sumflag ox oy,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_generator_generate)
   [Vptr bg Ptrofs.zero;Vptr ba oa] E0 mf
   (Vint (cmov_int (generator_hash_accepted false key && generator_hash_accepted true key))) /\
 hashgen_result key mf bg sx sy sz sumflag ox oy /\Mem.range_perm mf bg 0 64 Cur Freeable /\
 (forall i,(i<32)%nat ->Mem.load Mint8unsigned mf ba (Ptrofs.unsigned oa+Z.of_nat i)=
   Some (Vint (nth i (map word8_array_value (vector_values (Word 3) 5 key)) Int.zero))) /\
 lframe (fun b _=>b<>bg) m mf /\readonly_preserved m mf /\
 secp_sha_startup mf /\swu_startup mf /\(forall prefix,generator_sha_prefix_state prefix mf).
Proof.
 intros Count Apart Hi SHA SWU Prefixes FG Input.
 assert (GenValid:Mem.weak_valid_pointer m bg (Ptrofs.unsigned Ptrofs.zero)=true).
 { change (Mem.weak_valid_pointer m bg 0=true);apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm.
   eapply Mem.perm_implies;[apply (FG 0);clear;lia|apply perm_any_N]. }
 assert (KeyValid:Mem.weak_valid_pointer m ba (Ptrofs.unsigned oa)=true).
 { pose proof (Input 0%nat ltac:(clear;lia)) as Load;apply Mem.load_valid_access in Load.
   destruct Load as [Readable Align];apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm.
   eapply Mem.perm_implies;[apply Readable;change (Ptrofs.unsigned oa+0<=Ptrofs.unsigned oa<Ptrofs.unsigned oa+0+1);lia|apply perm_any_N]. }
 destruct (eval_hashgen_internal Hmodel key m bg ba oa Count Apart Hi SHA SWU Prefixes FG Input)
   as (mf & sx & sy & sz & sumflag & ox & oy & Call & Result & FGF & KeyF & Frame & Read & SHAF & SWUF & PrefixF).
 set (ret:=cmov_int (generator_hash_accepted false key && generator_hash_accepted true key)) in *.
 pose proof (hashgen_outer_entry m bg ba oa) as Entry.
 destruct hashgen_outer_link as [Symbol Funct].
 assert (Invoke:Clight2.exec_stmt secp_ge empty_env (hashgen_outer_temps bg ba oa) m hashgen_outer_call E0
   (PTree.set _t'1 (Vint ret) (hashgen_outer_temps bg ba oa)) mf Out_normal).
 { unfold hashgen_outer_call;eapply exec_Scall with
     (vf:=Vptr (secp_symbol_block _secp256k1_generator_generate_internal) Ptrofs.zero)
     (vargs:=[Vptr bg Ptrofs.zero;Vptr ba oa;Vlong Int64.zero])
     (f:=Internal f_secp256k1_generator_generate_internal) (vres:=Vint ret).
   - reflexivity.
   - eapply eval_Elvalue;[apply eval_Evar_global;[reflexivity|exact Symbol]|apply deref_loc_reference;reflexivity].
   - eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;reflexivity|reflexivity|].
     eapply eval_Econs;[eapply eval_Ecast;[constructor|reflexivity]|reflexivity|constructor].
   - exact Funct.
   - reflexivity.
   - exact Call. }
 exists mf,sx,sy,sz,sumflag,ox,oy;split.
 - eapply eval_funcall_internal with (e:=empty_env) (le1:=hashgen_outer_temps bg ba oa)
     (le2:=PTree.set _t'1 (Vint ret) (hashgen_outer_temps bg ba oa)) (m1:=m) (m2:=mf)
     (out:=Out_return (Some (Vint ret,tint))).
   + exact Entry.
   + rewrite hashgen_outer_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
     * apply exec_hashgen_nonnull with (b:=bg) (ofs:=Ptrofs.zero);[reflexivity|exact GenValid].
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
       -- apply exec_hashgen_nonnull with (b:=ba) (ofs:=oa);[reflexivity|exact KeyValid].
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Invoke|].
          apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
   + split;[discriminate|reflexivity].
   + reflexivity.
 - split;[exact Result|];split;[exact FGF|];split;[exact KeyF|];split;[exact Frame|];split;[exact Read|];
   split;[exact SHAF|];split;[exact SWUF|exact PrefixF].
Qed.
