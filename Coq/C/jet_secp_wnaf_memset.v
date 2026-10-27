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

Lemma memset_linked : exists bf,
  Genv.find_symbol secp_ge _memset=Some bf /\
  Genv.find_funct_ptr secp_ge bf=Some
    (External (EF_external "memset" memset_sig)
      (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid) cc_default).
Proof. exists (secp_symbol_block _memset);split;reflexivity. Qed.
Local Opaque secp_ge.

Lemma wnaf_memset_args_eval e le m b base len :
  le!_wnaf=Some (Vptr b (Ptrofs.repr base)) -> le!_len=Some (Vint (Int.repr len)) -> 0<=len<=256 ->
  eval_exprlist secp_ge e le m
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
Theorem exec_wnaf_memset (Model:memset_model) e le m b base len :
  e!_memset=None ->
  le!_wnaf=Some (Vptr b (Ptrofs.repr base)) -> le!_len=Some (Vint (Int.repr len)) ->
  0<len<=256 -> 0<=base -> base+4*len<=Ptrofs.max_unsigned ->
  Mem.range_perm m b base (base+4*len) Cur Writable ->
  exists mz, Clight2.exec_stmt secp_ge e le m wnaf_memset_call E0 le mz Out_normal /\
    Mem.storebytes m b base (memset_bytes Int.zero (4*len))=Some mz.
Proof.
  intros Local W L Range Base Fits Perm.
  assert (Offset:Ptrofs.unsigned (Ptrofs.repr base)=base) by (apply Ptrofs.unsigned_repr;lia).
  assert (Valid:Mem.valid_block m b) by (eapply Mem.perm_valid_block;apply (Perm base);lia).
  destruct (Model secp_ge m b (Ptrofs.repr base) Int.zero (4*len) Valid
    ltac:(rewrite Offset;exact Perm) ltac:(lia)) as (mz & Store & Ext).
  rewrite Offset in Store;exists mz;split;[|exact Store].
  destruct memset_linked as (bf & HS & HF).
  rewrite wnaf_memset_call_source.
  eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
    (vargs:=[Vptr b (Ptrofs.repr base);Vint Int.zero;Vlong (Int64.repr (4*len))])
    (f:=External (EF_external "memset" memset_sig)
      (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid) cc_default)
    (vres:=Vptr b (Ptrofs.repr base)).
  - reflexivity.
  - eapply eval_Elvalue;[eapply eval_Evar_global;[exact Local|exact HS]|apply deref_loc_reference;reflexivity].
  - apply wnaf_memset_args_eval;[exact W|exact L|lia].
  - exact HF.
  - reflexivity.
  - apply eval_funcall_external;exact Ext.
Qed.

(** Facts about the cleared buffer derived from the stored bytes. *)
Lemma memset_bytes_app c a d : 0<=a -> 0<=d ->
  memset_bytes c (a+d)=memset_bytes c a++memset_bytes c d.
Proof.
  intros A D;unfold memset_bytes;rewrite Z2Nat.inj_add by lia.
  induction (Z.to_nat a) as [|k IH];[reflexivity|cbn;f_equal;exact IH].
Qed.

Lemma app_length_inv {A} (a b c d:list A) : length a=length c -> a++b=c++d -> a=c /\ b=d.
Proof.
  revert c;induction a as [|x a IH];intros [|y c] Len E;try discriminate;[split;[reflexivity|exact E]|].
  injection E as -> E;injection Len as Len;destruct (IH c Len E) as [-> ->];split;reflexivity.
Qed.

Lemma memset_zero_load m b base len mz i :
  Mem.storebytes m b base (memset_bytes Int.zero (4*len))=Some mz -> (4|base) -> 0<=i<len ->
  Mem.load Mint32 mz b (base+4*i)=Some (Vint Int.zero).
Proof.
  intros Store Align Range.
  pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ Store) as All.
  rewrite memset_bytes_length in All by lia.
  replace (4*len) with (4*i+(4+4*(len-i-1))) in All by lia.
  rewrite (memset_bytes_app _ (4*i)) in All by lia.
  rewrite (memset_bytes_app _ 4) in All by lia.
  destruct (Mem.loadbytes_split _ _ _ _ _ _ All ltac:(lia) ltac:(lia)) as (l1 & l2 & L1 & L2 & E).
  assert (Len1:length l1=length (memset_bytes Int.zero (4*i))).
  { apply Nat2Z.inj;rewrite (Mem.loadbytes_length _ _ _ _ _ L1),memset_bytes_length by lia;lia. }
  destruct (app_length_inv _ _ _ _ (eq_sym Len1) E) as [_ E2].
  destruct (Mem.loadbytes_split _ _ _ _ _ _ L2 ltac:(lia) ltac:(lia)) as (l3 & l4 & L3 & L4 & E3).
  assert (Len3:length l3=length (memset_bytes Int.zero 4)).
  { apply Nat2Z.inj;rewrite (Mem.loadbytes_length _ _ _ _ _ L3),memset_bytes_length by lia;lia. }
  rewrite E3 in E2.
  destruct (app_length_inv _ _ _ _ (eq_sym Len3) E2) as [Word _];subst l3.
  rewrite (Mem.loadbytes_load Mint32 _ _ _ _ L3);[reflexivity|].
  change (align_chunk Mint32) with 4;apply Z.divide_add_r;[exact Align|exists i;lia].
Qed.

Lemma memset_memory_effect m b base len mz :
  Mem.storebytes m b base (memset_bytes Int.zero (4*len))=Some mz -> wnaf_memory_effect b m mz.
Proof.
  intro Store;split;[eapply Mem.nextblock_storebytes;exact Store|];split.
  - intros;split;intro P;[eapply Mem.perm_storebytes_1|eapply Mem.perm_storebytes_2];eassumption.
  - apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|].
    intros pos Range NE;apply NE;reflexivity.
Qed.

(** The exact deferred step of [generate_initialized_local_spec_from_memset_steps]. *)
Theorem generate_memset_steps (Model:memset_model) :
  forall ma mi local ba b,Mem.alloc ma 0 32=(mi,local) ->
    Mem.range_perm ma b 0 516 Cur Freeable -> exists mz,
    Clight2.exec_stmt secp_ge (wnaf_env local)
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero))) mi wnaf_memset_call E0
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero))) mz Out_normal /\
    (forall i,0<=i<129 -> Mem.load Mint32 mz b (4*i)=Some (Vint Int.zero)) /\
    wnaf_memory_effect b mi mz.
Proof.
  intros ma mi local ba b Alloc Perm.
  assert (PermI:Mem.range_perm mi b 0 (0+4*129) Cur Writable).
  { intros pos Range;eapply Mem.perm_alloc_1;[exact Alloc|].
    eapply Mem.perm_implies;[apply Perm;lia|constructor]. }
  destruct (exec_wnaf_memset Model (wnaf_env local)
    (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero))) mi b 0 129
    eq_refl eq_refl eq_refl ltac:(lia) ltac:(lia)
    ltac:(unfold Ptrofs.max_unsigned;cbn;lia) PermI) as (mz & Run & Store).
  exists mz;split;[exact Run|];split.
  - intros i Range;exact (memset_zero_load _ _ _ _ _ _ Store (Z.divide_0_r 4) Range).
  - exact (memset_memory_effect _ _ _ _ _ Store).
Qed.
