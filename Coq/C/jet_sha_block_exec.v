(** Actual three-local entry, source copy and call boundaries of the
    sha_256_block jet in the SHA translation unit.  Helper executions are
    premises here; [jet_sha_block_local.v] derives them from initial frames. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_frame_layout.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_transport.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Definition sha_block_env (bl bh bb : block) : Clight.env :=
  PTree.set _block (bb, tarray tuint 16) (PTree.set _h (bh, tarray tuint 8)
    (PTree.set _src (bl, Tstruct _frameItem noattr) empty_env)).

Definition sha_block_temps (env : val) bd dbase bs sbase : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_sha_256_block)))).

Lemma sha_read32s_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _read32s = Some (sha_symbol_block _read32s).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_read32s_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _read32s) Ptrofs.zero) =
    Some (Internal jets.f_read32s).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_write32s_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _write32s = Some (sha_symbol_block _write32s).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_write32s_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _write32s) Ptrofs.zero) =
    Some (Internal jets.f_write32s).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_dispatch_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _simplicity_sha256_compression =
    Some (sha_symbol_block _simplicity_sha256_compression).
Proof. vm_compute; reflexivity. Qed.

Lemma sha_block_blocks bl bh bb :
  blocks_of_env sha_ge (sha_block_env bl bh bb) = [(bl, 0, 16); (bh, 0, 32); (bb, 0, 64)].
Proof. vm_compute. reflexivity. Qed.

Lemma sha_block_entry env m ma mb mc bl bh bb bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 32 = (mb, bh) -> Mem.alloc mb 0 64 = (mc, bb) ->
  function_entry2 sha_ge f_simplicity_sha_256_block
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
    m (sha_block_env bl bh bb) (sha_block_temps env bd dbase bs sbase) mc.
Proof.
  intros HA HB HC. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma, bl)); exact HA.
    + eapply alloc_variables_cons with (m1 := mb) (b1 := bh).
      * change (Mem.alloc ma 0 32 = (mb, bh)); exact HB.
      * eapply alloc_variables_cons with (m1 := mc) (b1 := bb).
        -- change (Mem.alloc mb 0 64 = (mc, bb)); exact HC.
        -- constructor.
  - reflexivity.
Qed.

Lemma exec_sha_block_copy m mc bl bh bb bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt sha_ge (sha_block_env bl bh bb) le m
    (Sassign (Evar _src (Tstruct _frameItem noattr))
      (Etempvar _src (Tstruct _frameItem noattr))) E0 le mc Out_normal.
Proof.
  intros HB HS HD HL Hload Hstore.
  assert (HA : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr. unfold frame_base_valid in HB; lia. }
  eapply exec_Sassign_copy.
  - apply eval_Evar_local; reflexivity.
  - apply eval_Etempvar; exact HL.
  - reflexivity.
  - eapply assign_loc_copy with (b' := bs) (ofs' := Ptrofs.repr sbase) (bytes := bytes).
    + reflexivity.
    + intros _. change (8 | Ptrofs.unsigned (Ptrofs.repr sbase)). rewrite HA; exact HS.
    + intros _. change (8 | 0); exists 0; reflexivity.
    + left; congruence.
    + change (Mem.loadbytes m bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16 = Some bytes).
      rewrite HA; exact Hload.
    + exact Hstore.
Qed.

Local Opaque sha_ge.

Definition read32s_ty : type :=
  Tfunction (Tcons (tptr tuint) (Tcons tulong (Tcons (tptr (Tstruct _frameItem noattr)) Tnil)))
    tvoid cc_default.
Definition compression_ty : type :=
  Tfunction (Tcons (tptr tuint) (Tcons (tptr tuint) Tnil)) tvoid cc_default.

Lemma call_sha_read32s (arr : ident) (n k : Z) bl bh bb ba le m mf :
  (sha_block_env bl bh bb)!arr = Some (ba, tarray tuint n) -> 0 <= k <= 1000 ->
  Clight2.eval_funcall sha_ge m (Internal jets.f_read32s)
    [Vptr ba Ptrofs.zero; Vlong (Int64.repr k); Vptr bl Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt sha_ge (sha_block_env bl bh bb) le m
    (Scall None (Evar _read32s read32s_ty)
      [Evar arr (tarray tuint n); Econst_int (Int.repr k) tint;
       Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))])
    E0 le mf Out_normal.
Proof.
  intros HE Hk HR.
  change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _read32s) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero; Vlong (Int64.repr k); Vptr bl Ptrofs.zero])
    (f := Internal jets.f_read32s) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [eapply eval_Evar_global; [reflexivity|apply sha_read32s_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + eapply eval_Elvalue; [eapply eval_Evar_local; exact HE|].
      apply deref_loc_reference; reflexivity.
    + reflexivity.
    + eapply eval_Econs; [apply eval_Econst_int| |].
      * cbn. unfold sem_cast. cbn. rewrite Int.signed_repr; [reflexivity|].
        change Int.min_signed with (-2147483648). change Int.max_signed with 2147483647. lia.
      * eapply eval_Econs; [eapply eval_Eaddrof; eapply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
  - apply sha_read32s_funct.
  - reflexivity.
  - exact HR.
Qed.

Theorem eval_sha_block_composes env m ma mb mc mcp mr1 mr2 m4 me mf bl bh bb bd dbase bs sbase bytes :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 32 = (mb, bh) -> Mem.alloc mb 0 64 = (mc, bb) ->
  Mem.loadbytes mc bs sbase 16 = Some bytes -> Mem.storebytes mc bl 0 bytes = Some mcp ->
  Clight2.eval_funcall sha_ge mcp (Internal jets.f_read32s)
    [Vptr bh Ptrofs.zero; Vlong (Int64.repr 8); Vptr bl Ptrofs.zero] E0 mr1 Vundef ->
  Clight2.eval_funcall sha_ge mr1 (Internal jets.f_read32s)
    [Vptr bb Ptrofs.zero; Vlong (Int64.repr 16); Vptr bl Ptrofs.zero] E0 mr2 Vundef ->
  Mem.load Mptr mr2 (sha_symbol_block _simplicity_sha256_compression) 0 =
    Some (Vptr (sha_symbol_block _sha256_compression_portable) Ptrofs.zero) ->
  Clight2.eval_funcall sha_ge mr2 (Internal f_sha256_compression_portable)
    [Vptr bh Ptrofs.zero; Vptr bb Ptrofs.zero] E0 m4 Vundef ->
  Clight2.eval_funcall sha_ge m4 (Internal jets.f_write32s)
    [Vptr bd (Ptrofs.repr dbase); Vptr bh Ptrofs.zero; Vlong (Int64.repr 8)] E0 me Vundef ->
  Mem.free_list me [(bl, 0, 16); (bh, 0, 32); (bb, 0, 64)] = Some mf ->
  Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha_256_block)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HS HA HD A1 A2 A3 Hbytes Hstore Hr1 Hr2 Hptr Hcomp Hwrite Hfree.
  set (le := sha_block_temps env bd dbase bs sbase).
  set (le1 := PTree.set _t'1 (Vptr (sha_symbol_block _sha256_compression_portable) Ptrofs.zero) le).
  eapply eval_funcall_internal with (e := sha_block_env bl bh bb) (le1 := le) (le2 := le1)
    (m1 := mc) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply sha_block_entry; eauto.
  - cbn [f_simplicity_sha_256_block fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mcp) (le1 := le).
    + eapply exec_sha_block_copy; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr1) (le1 := le).
      * eapply (call_sha_read32s _h 8 8) with (ba := bh); [reflexivity|lia|exact Hr1].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := le).
        -- eapply (call_sha_read32s _block 16 16) with (ba := bb); [reflexivity|lia|exact Hr2].
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m4) (le1 := le1).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := le1).
              ** constructor. eapply eval_Elvalue.
                 --- apply eval_Evar_global; [reflexivity|exact sha_dispatch_symbol].
                 --- eapply deref_loc_value; [reflexivity|]. exact Hptr.
              ** change le1 with (set_opttemp None Vundef le1) at 2.
                 eapply exec_Scall with
                   (vf := Vptr (sha_symbol_block _sha256_compression_portable) Ptrofs.zero)
                   (vargs := [Vptr bh Ptrofs.zero; Vptr bb Ptrofs.zero])
                   (f := Internal f_sha256_compression_portable) (vres := Vundef).
                 --- reflexivity.
                 --- apply eval_Etempvar. apply PTree.gss.
                 --- eapply eval_Econs.
                     +++ eapply eval_Elvalue; [eapply eval_Evar_local; reflexivity|].
                         apply deref_loc_reference; reflexivity.
                     +++ reflexivity.
                     +++ eapply eval_Econs with (v1 := Vptr bb Ptrofs.zero); [|reflexivity|apply eval_Enil].
                         eapply eval_Elvalue; [eapply eval_Evar_local; reflexivity|].
                         apply deref_loc_reference; reflexivity.
                 --- exact sha_compression_funct.
                 --- reflexivity.
                 --- exact Hcomp.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := le1).
              ** change le1 with (set_opttemp None Vundef le1) at 2.
                 eapply exec_Scall with (vf := Vptr (sha_symbol_block _write32s) Ptrofs.zero)
                   (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bh Ptrofs.zero; Vlong (Int64.repr 8)])
                   (f := Internal jets.f_write32s) (vres := Vundef).
                 --- reflexivity.
                 --- eapply eval_Elvalue; [eapply eval_Evar_global; [reflexivity|apply sha_write32s_symbol]|].
                     apply deref_loc_reference; reflexivity.
                 --- eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
                     eapply eval_Econs.
                     +++ eapply eval_Elvalue; [eapply eval_Evar_local; reflexivity|].
                         apply deref_loc_reference; reflexivity.
                     +++ reflexivity.
                     +++ eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
                 --- apply sha_write32s_funct.
                 --- reflexivity.
                 --- exact Hwrite.
              ** apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; [discriminate|reflexivity].
  - rewrite sha_block_blocks. exact Hfree.
Qed.
