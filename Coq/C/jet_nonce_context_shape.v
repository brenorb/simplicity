(** Exact original nonce_hash statement tree and four-local function entry.
    This is preparation; it assumes no helper execution or output. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_elements_support_sha_add_n_init C.jets_elements C.jet_elements_linkage.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition nc_fr := Tstruct _frameItem noattr.
Definition nc_readbit (id : ident) :=
  Scall (Some id) (Evar _readBit (Tfunction (Tcons FRP Tnil) tbool cc_default))
    [Eaddrof (Evar _src nc_fr) FRP].
Definition nc_uchar (k : Z) :=
  Scall None (Evar _sha256_uchar (Tfunction (Tcons CTXP (Tcons tuchar Tnil)) tbool cc_default))
    [Eaddrof (Evar _ctx CTX) CTXP; Econst_int (Int.repr k) tint].
Definition nc_forward :=
  Scall None (Evar _forwardBits (Tfunction (Tcons FRP (Tcons tulong Tnil)) tvoid cc_default))
    [Eaddrof (Evar _src nc_fr) FRP; Econst_int (Int.repr 1) tint].
Definition nc_readbytes :=
  Scall None (Evar _read8s (Tfunction (Tcons (tptr tuchar) (Tcons tulong (Tcons FRP Tnil))) tvoid cc_default))
    [Evar _buf (tarray tuchar 32); Econst_int (Int.repr 32) tint; Eaddrof (Evar _src nc_fr) FRP].
Definition nc_uchars :=
  Scall None (Evar _sha256_uchars (Tfunction (Tcons CTXP (Tcons (tptr tuchar) (Tcons tulong Tnil))) tbool cc_default))
    [Eaddrof (Evar _ctx CTX) CTXP; Evar _buf (tarray tuchar 32); Econst_int (Int.repr 32) tint].
Definition nc_prefix :=
  Ssequence (nc_readbit _t'3)
    (Sifthenelse (Etempvar _t'3 tbool) (Ssequence nc_forward (nc_uchar 1))
      (Ssequence (nc_readbit _t'2) (Sifthenelse (Etempvar _t'2 tbool) (nc_uchar 3) (nc_uchar 2)))).
Definition nc_nonce :=
  Ssequence (nc_readbit _t'4)
    (Sifthenelse (Etempvar _t'4 tbool)
      (Ssequence nc_prefix (Ssequence nc_readbytes nc_uchars)) (nc_uchar 0)).
Definition nc_context_read :=
  Ssequence
    (Scall (Some _t'1) (Evar _simplicity_read_sha256_context
      (Tfunction (Tcons CTXP (Tcons FRP Tnil)) tbool cc_default))
      [Eaddrof (Evar _ctx CTX) CTXP; Eaddrof (Evar _src nc_fr) FRP])
    (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tbool) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip).
Definition nc_context_write :=
  Ssequence
    (Scall (Some _t'5) (Evar _simplicity_write_sha256_context
      (Tfunction (Tcons FRP (Tcons CTXP Tnil)) tbool cc_default))
      [Etempvar _dst FRP; Eaddrof (Evar _ctx CTX) CTXP])
    (Sreturn (Some (Etempvar _t'5 tbool))).

Lemma nc_body_shape : fn_body f_simplicity_nonce_hash =
  Ssequence (Sassign (Evar _src nc_fr) (Etempvar _src nc_fr))
    (an_init (Ssequence nc_context_read (Ssequence nc_nonce nc_context_write))).
Proof. reflexivity. Qed.

Definition nc_env (bl bm bb bx : block) : env :=
  PTree.set _ctx (bx, CTX) (PTree.set _buf (bb, tarray tuchar 32)
    (PTree.set _midstate (bm, MID) (PTree.set _src (bl, nc_fr) empty_env))).
Definition nc_temps (env : val) bd dbase bs sbase : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase)) (create_undef_temps (fn_temps f_simplicity_nonce_hash)))).

Lemma nc_header :
  fn_vars f_simplicity_nonce_hash = [(_src, nc_fr); (_midstate, MID); (_buf, tarray tuchar 32); (_ctx, CTX)] /\
  fn_temps f_simplicity_nonce_hash = [(_t'5, tbool); (_t'4, tbool); (_t'3, tbool); (_t'2, tbool); (_t'1, tbool)] /\
  fn_return f_simplicity_nonce_hash = tbool /\ fn_callconv f_simplicity_nonce_hash = cc_default.
Proof. repeat split; reflexivity. Qed.

Lemma nc_blocks bl bm bb bx :
  blocks_of_env elements_ge (nc_env bl bm bb bx) = [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32); (bb, 0, 32)].
Proof. vm_compute; reflexivity. Qed.

Theorem nc_entry env m m1 m2 m3 m4 bl bm bb bx bd dbase bs sbase :
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 32 = (m2, bm) ->
  Mem.alloc m2 0 32 = (m3, bb) -> Mem.alloc m3 0 88 = (m4, bx) ->
  function_entry2 elements_ge f_simplicity_nonce_hash
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] m
    (nc_env bl bm bb bx) (nc_temps env bd dbase bs sbase) m4.
Proof.
  intros A1 A2 A3 A4. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bl);
      [change (Mem.alloc m 0 16 = (m1, bl)); exact A1|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := bm);
      [change (Mem.alloc m1 0 32 = (m2, bm)); exact A2|].
    eapply alloc_variables_cons with (m1 := m3) (b1 := bb);
      [change (Mem.alloc m2 0 32 = (m3, bb)); exact A3|].
    eapply alloc_variables_cons with (m1 := m4) (b1 := bx);
      [change (Mem.alloc m3 0 88 = (m4, bx)); exact A4|constructor].
  - reflexivity.
Qed.
