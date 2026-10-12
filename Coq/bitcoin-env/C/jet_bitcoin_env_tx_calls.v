(** Clight call statements for the context operations of sha256.h, for any
    local context variable. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_add_n_init C.jet_sha_hash_exec C.jet_sha_finalize_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Lemma sha_u32be_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_u32be = Some (sha_symbol_block _sha256_u32be).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_u32be_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_u32be) Ptrofs.zero) =
    Some (Internal f_sha256_u32be).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_u64be_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_u64be = Some (sha_symbol_block _sha256_u64be).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_u64be_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_u64be) Ptrofs.zero) =
    Some (Internal f_sha256_u64be).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_uchar_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_uchar = Some (sha_symbol_block _sha256_uchar).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_uchar_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_uchar) Ptrofs.zero) =
    Some (Internal f_sha256_uchar).
Proof. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

Lemma mt_call_hash e le m m' (id : ident) bx (a2 : expr) bt ot :
  e!_sha256_hash = None -> e!id = Some (bx, CTX) ->
  eval_expr sha_ge e le m a2 (Vptr bt ot) -> typeof a2 = tptr MID ->
  Clight2.eval_funcall sha_ge m (Internal f_sha256_hash) [Vptr bx (Ptrofs.repr 0); Vptr bt ot] E0 m' Vundef ->
  Clight2.exec_stmt sha_ge e le m
    (Scall None (Evar _sha256_hash (Tfunction (Tcons CTXP (Tcons (tptr MID) Tnil)) tvoid cc_default))
       [Eaddrof (Evar id CTX) CTXP; a2]) E0 le m' Out_normal.
Proof.
  intros He Hc H2 T2 HC. change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_hash) Ptrofs.zero)
    (vargs := [Vptr bx Ptrofs.zero; Vptr bt ot]) (f := Internal f_sha256_hash).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact sha_hash_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact Hc|reflexivity|].
    eapply eval_Econs; [exact H2|rewrite T2; reflexivity|apply eval_Enil].
  - exact sha_hash_funct.
  - reflexivity.
  - exact HC.
Qed.

Lemma mt_call_u32be e le m m' (id : ident) bx (a2 : expr) (x : int64) vr :
  e!_sha256_u32be = None -> e!id = Some (bx, CTX) ->
  eval_expr sha_ge e le m a2 (Vlong x) -> typeof a2 = tulong ->
  Clight2.eval_funcall sha_ge m (Internal f_sha256_u32be) [Vptr bx (Ptrofs.repr 0); Vlong x] E0 m' vr ->
  Clight2.exec_stmt sha_ge e le m
    (Scall None (Evar _sha256_u32be (Tfunction (Tcons CTXP (Tcons tulong Tnil)) tbool cc_default))
       [Eaddrof (Evar id CTX) CTXP; a2]) E0 le m' Out_normal.
Proof.
  intros He Hc H2 T2 HC. change le with (set_opttemp None vr le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_u32be) Ptrofs.zero)
    (vargs := [Vptr bx Ptrofs.zero; Vlong x]) (f := Internal f_sha256_u32be).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact sha_u32be_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact Hc|reflexivity|].
    eapply eval_Econs; [exact H2|rewrite T2; reflexivity|apply eval_Enil].
  - exact sha_u32be_funct.
  - reflexivity.
  - exact HC.
Qed.

Lemma mt_call_u64be e le m m' (id : ident) bx (a2 : expr) (x : int64) vr :
  e!_sha256_u64be = None -> e!id = Some (bx, CTX) ->
  eval_expr sha_ge e le m a2 (Vlong x) -> typeof a2 = tulong ->
  Clight2.eval_funcall sha_ge m (Internal f_sha256_u64be) [Vptr bx (Ptrofs.repr 0); Vlong x] E0 m' vr ->
  Clight2.exec_stmt sha_ge e le m
    (Scall None (Evar _sha256_u64be (Tfunction (Tcons CTXP (Tcons tulong Tnil)) tbool cc_default))
       [Eaddrof (Evar id CTX) CTXP; a2]) E0 le m' Out_normal.
Proof.
  intros He Hc H2 T2 HC. change le with (set_opttemp None vr le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_u64be) Ptrofs.zero)
    (vargs := [Vptr bx Ptrofs.zero; Vlong x]) (f := Internal f_sha256_u64be).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact sha_u64be_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact Hc|reflexivity|].
    eapply eval_Econs; [exact H2|rewrite T2; reflexivity|apply eval_Enil].
  - exact sha_u64be_funct.
  - reflexivity.
  - exact HC.
Qed.

Lemma mt_call_finalize e le m m' (id : ident) bx vr :
  e!_sha256_finalize = None -> e!id = Some (bx, CTX) ->
  Clight2.eval_funcall sha_ge m (Internal f_sha256_finalize) [Vptr bx (Ptrofs.repr 0)] E0 m' vr ->
  Clight2.exec_stmt sha_ge e le m
    (Scall None (Evar _sha256_finalize (Tfunction (Tcons CTXP Tnil) tbool cc_default))
       [Eaddrof (Evar id CTX) CTXP]) E0 le m' Out_normal.
Proof.
  intros He Hx HC. change le with (set_opttemp None vr le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_finalize) Ptrofs.zero)
    (vargs := [Vptr bx Ptrofs.zero]) (f := Internal f_sha256_finalize).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact sha_finalize_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact Hx|reflexivity|apply eval_Enil].
  - exact sha_finalize_funct.
  - reflexivity.
  - exact HC.
Qed.
