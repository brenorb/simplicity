(** The original wNAF digit-buffer clear, [memset(wnaf, 0, len*sizeof(int))],
    executed under the explicit [memset_model] premise (see [jet_memset_model]).
    Nothing about the call is assumed beyond that model: the callee lookup,
    argument evaluation and casts are those of the frozen AST. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Cop Clight Clightdefs ClightBigstep Integers Maps
  Memory Values Events Globalenvs.
Require Import C.jet_memset_model C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_wnaf_digit C.jet_secp_wnaf_entry15 C.jet_secp_wnaf_loop.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Require Import C.jet_elements_taptweak_pure C.jet_elements_taptweak_globals.
Lemma elements_taptweak_wnaf_memset_linked : exists bf,
  Genv.find_symbol elements_taptweak_ge _memset=Some bf /\
  Genv.find_funct_ptr elements_taptweak_ge bf=Some
    (External (EF_external "memset" memset_sig)
      (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid) cc_default).
Proof. exists(elements_taptweak_symbol_block _memset);split;vm_compute;reflexivity. Qed.
Local Opaque elements_taptweak_ge.

Lemma elements_taptweak_wnaf_memset_args e le m b base len :
  le!_wnaf=Some (Vptr b (Ptrofs.repr base)) -> le!_len=Some (Vint (Int.repr len)) -> 0<=len<=256 ->
  eval_exprlist elements_taptweak_ge e le m
   [Etempvar _wnaf (tptr tint);Econst_int Int.zero tint;
    Ebinop Omul (Etempvar _len tint) (Esizeof tint tulong) tulong]
   (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil)))
   [Vptr b (Ptrofs.repr base);Vint Int.zero;Vlong (Int64.repr (4*len))].
Proof.
  intros W L Range.
  assert (Product : Int64.mul (Int64.repr (Int.signed (Int.repr len))) (Int64.repr 4)=Int64.repr (4*len)).
  { rewrite Int.signed_repr by (unfold Int.min_signed,Int.max_signed;cbn;lia).
    unfold Int64.mul;rewrite !Int64.unsigned_repr
      by (unfold Int64.max_unsigned;cbn;lia);f_equal;lia. }
  eapply eval_Econs;[apply eval_Etempvar;exact W|reflexivity|].
  eapply eval_Econs;[constructor|reflexivity|].
  eapply eval_Econs with (v1:=Vlong (Int64.repr (4*len)));[|reflexivity|constructor].
  eapply eval_Ebinop;
    [apply eval_Etempvar;exact L|apply eval_Esizeof|].
  change (Some (Vlong (Int64.mul (Int64.repr (Int.signed (Int.repr len))) (Int64.repr 4)))=
    Some (Vlong (Int64.repr (4*len))));rewrite Product;reflexivity.
Qed.

(** Generic for any digit-buffer length and caller environment. *)
Theorem exec_elements_taptweak_wnaf_memset (Model:memset_model) e le m b base len :
  e!_memset=None ->
  le!_wnaf=Some (Vptr b (Ptrofs.repr base)) -> le!_len=Some (Vint (Int.repr len)) ->
  0<len<=256 -> 0<=base -> base+4*len<=Ptrofs.max_unsigned ->
  Mem.range_perm m b base (base+4*len) Cur Writable ->
  exists mz, Clight2.exec_stmt elements_taptweak_ge e le m wnaf_memset_call E0 le mz Out_normal /\
    Mem.storebytes m b base (memset_bytes Int.zero (4*len))=Some mz.
Proof.
  intros Local W L Range Base Fits Perm.
  assert (Offset:Ptrofs.unsigned (Ptrofs.repr base)=base) by (apply Ptrofs.unsigned_repr;lia).
  assert (Valid:Mem.valid_block m b) by (eapply Mem.perm_valid_block;apply (Perm base);lia).
  destruct (Model elements_taptweak_ge m b (Ptrofs.repr base) Int.zero (4*len) Valid
    ltac:(rewrite Offset;exact Perm) ltac:(lia)) as (mz & Store & Ext).
  rewrite Offset in Store;exists mz;split;[|exact Store].
  destruct elements_taptweak_wnaf_memset_linked as (bf & HS & HF).
  rewrite wnaf_memset_call_source.
  eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
    (vargs:=[Vptr b (Ptrofs.repr base);Vint Int.zero;Vlong (Int64.repr (4*len))])
    (f:=External (EF_external "memset" memset_sig)
      (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid) cc_default)
    (vres:=Vptr b (Ptrofs.repr base)).
  - reflexivity.
  - eapply eval_Elvalue;[eapply eval_Evar_global;[exact Local|exact HS]|apply deref_loc_reference;reflexivity].
  - apply elements_taptweak_wnaf_memset_args;[exact W|exact L|lia].
  - exact HF.
  - reflexivity.
  - apply eval_funcall_external;exact Ext.
Qed.

