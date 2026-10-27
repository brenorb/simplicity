(** Execute the original wNAF negative-sign preparation. The scalar-negation
    call is the existing checked in-place function, including its local
    allocation/free. No unchanged-nextblock claim is made for that call. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep
 Maps Memory Values Events.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_canonical_scalar C.jet_secp_scalar_overflow_numeric
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_scalar_negate_canonical C.jet_secp_scalar_negate_storage
 C.jet_secp_scalar_writer_run C.jet_secp_scalar_writer_storage C.jet_secp_scalar_get_bits
 C.jet_secp_wnaf_digit C.jet_secp_wnaf_control C.jet_secp_wnaf_prepare
 C.jet_secp_curve_statements C.jet_secp_fns C.jet_secp_closed_helpers
 C.jet_secp_slice_permissions C.jet_clight_internal_frame C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma wnaf_scalar_negate_closed :
 closed_stmtb secp_closed_helpers (fn_body f_secp256k1_scalar_negate)=true.
Proof. reflexivity. Qed.

Theorem eval_wnaf_scalar_negate n m bs : 0<=n<canonical_group_order ->
 scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) ->
 Mem.range_perm m bs 0 32 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_negate)
  [Vptr bs Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef /\
 scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of ((-n) mod canonical_group_order))) /\
 Mem.range_perm mf bs 0 32 Cur Freeable /\
 lframe (fun old _=>old<>bs) m mf /\ keeps_permissions m mf /\ readonly_preserved m mf.
Proof.
 intros N Storage Free.
 assert (N256:0<=n<2^256).
 { pose proof canonical_group_order_range as [[Pos Max] _].
   change (canonical_group_order<2^256) in Max;lia. }
 pose proof (scalar_writer_initial_rep_from_storage n m bs Storage Free) as Rep.
 assert (Value:scalar_limb_value (scalar_limb_rho n)=n) by (apply scalar_limb_rho_value;exact N256).
 destruct (eval_scalar_negate_numeric_owned (scalar_limb_rho n) [(bs,0)] m Rep
  ltac:(rewrite Value;exact N)) as (mf & Call & Output & FreeF & Frame).
 rewrite Value in Output.
 change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_negate)
  [Vptr bs Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef) in Call.
 exists mf;split;[exact Call|];split;[exact Output|];split;[exact FreeF|];split.
 - eapply lframe_implies;[exact Frame|].
   intros old pos Different Valid (r & shape & d & ch & Lookup & Member & Same & Bounds).
   destruct r as [|r];[|destruct r;discriminate Lookup].
   change (old=bs) in Same;congruence.
 - split.
   + eapply secp_internal_keeps_permissions;[exact wnaf_scalar_negate_closed|reflexivity|exact Call].
   + eapply secp_closed_function_preserved;[exact wnaf_scalar_negate_closed|reflexivity|exact Call].
Qed.

Definition wnaf_negative_temps le := PTree.set _sign (Vint (Int.repr (-1)))
 (PTree.set _t'1 (Vint Int.one) le).
Definition wnaf_scalar_local := Eaddrof (Evar _s (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr)).
Lemma wnaf_negative_source : wnaf_negative_branch=
 Ssequence (curve_call _secp256k1_scalar_negate f_secp256k1_scalar_negate None
  [wnaf_scalar_local;wnaf_scalar_local])
  (Sset _sign (Eunop Oneg (Econst_int Int.one tint) tint)).
Proof. reflexivity. Qed.

Theorem exec_wnaf_sign_large le m n bs : 2^255<=n<canonical_group_order ->
 scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) ->
 Mem.range_perm m bs 0 32 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_sign_select E0 (wnaf_negative_temps le) mf Out_normal /\
 scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of ((-n) mod canonical_group_order))) /\
 Mem.range_perm mf bs 0 32 Cur Freeable /\ lframe (fun old _=>old<>bs) m mf /\
 keeps_permissions m mf /\ readonly_preserved m mf.
Proof.
 intros N Storage Free.
 assert (N256:0<=n<2^256).
 { pose proof canonical_group_order_range as [[Pos Max] _].
   change (canonical_group_order<2^256) in Max;lia. }
 assert (High:n/2^255=1).
 { symmetry;apply Z.div_unique with (r:=n-2^255);[lia|ring]. }
 pose proof (eval_scalar_get_bits_slice m bs 0 n 255 1 ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(cbn;lia) Storage) as Bits.
 change (2^1) with 2 in Bits;rewrite High in Bits.
 change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_get_bits)
  [Vptr bs Ptrofs.zero;Vint (Int.repr 255);Vint Int.one] E0 m (Vint Int.one)) in Bits.
 destruct (eval_wnaf_scalar_negate n m bs ltac:(lia) Storage Free)
  as (mf & Negate & Output & FreeF & Frame & Keep & Readonly).
 exists mf;split;[|split;[exact Output|];split;[exact FreeF|];split;[exact Frame|];split;assumption].
 rewrite wnaf_sign_select_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0)
  (le1:=PTree.set _t'1 (Vint Int.one) le) (m1:=m).
 - rewrite wnaf_top_call_source.
   eapply exec_curve_call with
    (vargs:=[Vptr bs Ptrofs.zero;Vint (Int.repr 255);Vint Int.one]) (v:=Vint Int.one).
   + unfold secp_pure;repeat (first [left;reflexivity|right]).
   + reflexivity.
   + eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
     eapply eval_Econs;[constructor|reflexivity|];eapply eval_Econs;[constructor|reflexivity|constructor].
   + exact Bits.
 - eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[apply eval_Etempvar;apply PTree.gss|reflexivity|].
   rewrite wnaf_negative_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf).
   + eapply exec_curve_call with (vargs:=[Vptr bs Ptrofs.zero;Vptr bs Ptrofs.zero]) (v:=Vundef).
     * unfold secp_pure;repeat (first [left;reflexivity|right]).
     * reflexivity.
     * unfold wnaf_scalar_local;eapply eval_Econs;
       [apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
       eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
     * exact Negate.
   + apply exec_Sset;eapply eval_Eunop;[constructor|reflexivity].
Qed.

Lemma wnaf_negative_fields le bit len w carry sign b base last :
 wnaf_loop_fields le bit len w carry sign b base last ->
 wnaf_loop_fields (wnaf_negative_temps le) bit len w carry (-1) b base last.
Proof.
 intros (HB & HL & HW & HC & HS & HP & HT);unfold wnaf_loop_fields,wnaf_negative_temps.
 repeat split;first [apply PTree.gss|rewrite !PTree.gso by discriminate;assumption].
Qed.
