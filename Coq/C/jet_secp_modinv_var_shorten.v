(** Original inverse shortening: actual execution, ownership and integer values. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix C.jet_secp_modinv_var_entry.
Require Import C.jet_secp_modinv_var_zero C.jet_secp_modinv_fg_index C.jet_secp_modinv_normalize62_words C.jet_secp_fe_math.
Require Import C.jet_secp_u128_shift64_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition inv_sign_word a := a=Int64.zero \/ a=Int64.mone.
Definition inv_len_sign len := Int64.shr
 (Int64.sub (Int64.repr (Z.of_nat len)) (Int64.repr 2)) (Int64.repr 63).
Definition inv_word_sign_test a := Int64.xor a (Int64.shr a (Int64.repr 63)).
Definition inv_shorten_cond len f g := Int64.or
 (Int64.or (inv_len_sign len) (inv_word_sign_test f)) (inv_word_sign_test g).
Definition inv_shorten_guard len f g := Int64.eq (inv_shorten_cond len f g) Int64.zero.
Lemma inv_word_sign_test_zero a : inv_word_sign_test a=Int64.zero <-> inv_sign_word a.
Proof.
 unfold inv_word_sign_test,inv_sign_word.
 change (Int64.repr 63) with (Int64.repr (Int64.zwordsize-1)).
 rewrite Int64.shr_lt_zero;split.
 - intro E;apply Int64.xor_zero_equal in E;destruct (Int64.lt a Int64.zero);auto.
 - intros [Zero|Mone];subst a;vm_compute;reflexivity.
Qed.
Lemma inv_len_sign_value len : (0<len<=5)%nat ->
 inv_len_sign len=if (2<=?len)%nat then Int64.zero else Int64.mone.
Proof. destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;vm_compute;reflexivity. Qed.
Lemma inv_shorten_guard_correct len f g : (0<len<=5)%nat ->
 inv_shorten_guard len f g=true <-> (2<=len)%nat /\ inv_sign_word f /\ inv_sign_word g.
Proof.
 intro Len;unfold inv_shorten_guard,inv_shorten_cond;rewrite inv_int64_zero_eq,!inv_or_zero,
  !inv_word_sign_test_zero,inv_len_sign_value by exact Len.
 destruct (Nat.leb_spec 2 len);[tauto|].
 assert (NZ : Int64.mone<>Int64.zero) by discriminate.
 assert (Short : ~ (2<=len)%nat) by lia;tauto.
Qed.

Definition inv_shorten_limb low high := Int64.or low (Int64.shl high (Int64.repr 62)).
Lemma inv_shorten_zero_shift : Int64.shl Int64.zero (Int64.repr 62)=Int64.zero.
Proof. vm_compute;reflexivity. Qed.
Lemma inv_shorten_mone_shift : Int64.shl Int64.mone (Int64.repr 62)=Int64.repr (3*2^62).
Proof. apply Int64.same_if_eq;vm_compute;reflexivity. Qed.
Lemma inv_shorten_limb_signed low high :
 0<=Int64.signed low<2^62 -> inv_sign_word high ->
 Int64.signed (inv_shorten_limb low high)=Int64.signed low+2^62*Int64.signed high.
Proof.
 intros Low [Zero|Mone];subst high;unfold inv_shorten_limb.
 - rewrite inv_shorten_zero_shift,Int64.or_zero,Int64.signed_zero;ring.
 - rewrite inv_shorten_mone_shift.
   assert (Or : Int64.or low (Int64.repr (3*2^62))=Int64.repr (Int64.signed low-2^62)).
   { unfold Int64.or;rewrite <-(Int64.repr_signed low) at 1.
     rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with (2^64-1);lia).
     rewrite (lor_shift_add (Int64.signed low) 3 62) by lia.
     apply Int64.eqm_samerepr;change (exists k,Int64.signed low+3*2^62=k*2^64+(Int64.signed low-2^62)).
     exists 1;ring. }
   rewrite Or,Int64.signed_repr,Int64.signed_mone;
    [ring|change Int64.min_signed with (-2^63);change Int64.max_signed with (2^63-1);lia].
Qed.

Definition inv_shorten_words len (w : nat->int64) i :=
 if Nat.eqb i (len-2) then inv_shorten_limb (w i) (w (len-1)%nat) else w i.
Lemma inv_shorten_preserves_value len w : (2<=len<=5)%nat -> inv_active_low_bounds len w ->
 inv_sign_word (w (len-1)%nat) ->
 inv_active_value (len-1) (inv_shorten_words len w)=inv_active_value len w.
Proof.
 intros Len Low Top;unfold inv_active_value.
 assert (Carry : Int64.signed (inv_shorten_limb (w (len-2)%nat) (w (len-1)%nat))=
  Int64.signed (w (len-2)%nat)+2^62*Int64.signed (w (len-1)%nat)).
 { apply inv_shorten_limb_signed;[apply Low;lia|exact Top]. }
 destruct len as [|[|[|[|[|[|len]]]]]];try lia;
  cbn [Nat.sub inv_shorten_words Nat.eqb norm62_value_z] in Carry |- *;rewrite Carry;ring.
Qed.

Definition inv_shorten_parts := split_statement_last inv_shortening.
Definition inv_shorten_prefix := statement_sequence (fst inv_shorten_parts) Sskip.
Definition inv_shorten_body := match snd inv_shorten_parts with Sifthenelse _ yes _=>yes | _=>Sskip end.
Lemma inv_shorten_source : inv_shortening=statement_sequence (fst inv_shorten_parts)
 (Sifthenelse (Ebinop Oeq (Etempvar _cond tlong) (Econst_int Int.zero tint) tint) inv_shorten_body Sskip).
Proof. reflexivity. Qed.

Definition inv_local_array id := Efield (Evar id fg_s62_type) _v (tarray tlong 5).
Definition inv_local_index id ix := Ederef (Ebinop Oadd (inv_local_array id) ix (tptr tlong)) tlong.
Definition inv_len_sub k := Ebinop Osub (Etempvar _len tint) (Econst_int (Int.repr (Z.of_nat k)) tint) tint.
Definition inv_shorten_id (high : bool) := if high then _g else _f.
Definition inv_shorten_tmp (high : bool) := if high then _t'3 else _t'4.
Definition inv_shorten_top (high : bool) := if high then _gn else _fn.
Definition inv_shorten_offset (high : bool) : nat := if high then 10 else 5.
Definition inv_shorten_region (high : bool) : nat := if high then 5 else 4.
Definition inv_shorten_expr len high := XLb Bor
 (XLv (inv_shorten_offset high+(len-2))%nat)
 (XLsh Hshl (XLv (inv_shorten_offset high+(len-1))%nat) 62).
Definition inv_shorten_f_regs len := match xstore inv_control_regs 4 (8*Z.of_nat (len-2)) Mint64
 (inv_shorten_expr len false) with Some regs=>regs | None=>inv_control_regs end.
Definition inv_shorten_fg_regs len := match xstore (inv_shorten_f_regs len) 5 (8*Z.of_nat (len-2)) Mint64
 (inv_shorten_expr len true) with Some regs=>regs | None=>inv_shorten_f_regs len end.
Definition inv_shorten_in len (high : bool) := if high then inv_shorten_f_regs len else inv_control_regs.
Definition inv_shorten_out len (high : bool) := if high then inv_shorten_fg_regs len else inv_shorten_f_regs len.
Definition inv_shorten_array_step (high : bool) := if high then
 match inv_shorten_body with Ssequence _ (Ssequence s _) =>s | _=>Sskip end else
 match inv_shorten_body with Ssequence s _ =>s | _=>Sskip end.
Definition inv_shorten_len_step := match inv_shorten_body with Ssequence _ (Ssequence _ s)=>s | _=>Sskip end.
Lemma inv_shorten_body_source : inv_shorten_body=Ssequence (inv_shorten_array_step false)
 (Ssequence (inv_shorten_array_step true) inv_shorten_len_step).
Proof. reflexivity. Qed.
Lemma inv_shorten_array_source high : inv_shorten_array_step high=Ssequence
 (Sset (inv_shorten_tmp high) (inv_local_index (inv_shorten_id high) (inv_len_sub 2)))
 (Sassign (inv_local_index (inv_shorten_id high) (inv_len_sub 2))
  (Ebinop Oor (Etempvar (inv_shorten_tmp high) tlong)
   (Ebinop Oshl (Ecast (Etempvar (inv_shorten_top high) tlong) tulong) (Econst_int (Int.repr 62) tint) tulong) tulong)).
Proof. destruct high;reflexivity. Qed.
Lemma inv_shorten_store len high : (2<=len<=5)%nat ->
 xstore (inv_shorten_in len high) (inv_shorten_region high) (8*Z.of_nat (len-2)) Mint64
 (inv_shorten_expr len high)=Some (inv_shorten_out len high).
Proof. destruct high;destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;vm_compute;reflexivity. Qed.
Lemma inv_shorten_load len high : (2<=len<=5)%nat ->
 xload (inv_shorten_in len high) (inv_shorten_region high) (8*Z.of_nat (len-2)) tulong=
 Some (XLv (inv_shorten_offset high+(len-2))%nat).
Proof. destruct high;destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;vm_compute;reflexivity. Qed.
Lemma inv_shorten_region_owned len high : (2<=len<=5)%nat ->
 rfree (nth (inv_shorten_region high) (inv_shorten_in len high) (mkreg [] true None))=Some 40.
Proof. destruct high;destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;reflexivity. Qed.
Lemma inv_shorten_in_length len high : (2<=len<=5)%nat -> length (inv_shorten_in len high)=7%nat.
Proof. destruct high;destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;reflexivity. Qed.

Lemma eval_inv_local_array e le m id b : e!id=Some (b,fg_s62_type) ->
 eval_expr secp_ge e le m (inv_local_array id) (Vptr b Ptrofs.zero).
Proof.
 intro Ptr;destruct fg_array_layout as (co & Composite & Offset).
 eapply eval_Elvalue with (loc:=b) (ofs:=Ptrofs.zero).
 - change Ptrofs.zero with (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0)) at 1.
   unfold inv_local_array;eapply eval_Efield_struct with (co:=co) (delta:=0).
   + eapply eval_Elvalue;[apply eval_Evar_local;exact Ptr|apply deref_loc_copy;reflexivity].
   + reflexivity.
   + exact Composite.
   + exact Offset.
 - apply deref_loc_reference;reflexivity.
Qed.
Lemma eval_inv_local_index e le m id b ix j : (j<5)%nat -> typeof ix=tint ->
 e!id=Some (b,fg_s62_type) -> eval_expr secp_ge e le m ix (Vint (Int.repr (Z.of_nat j))) ->
 eval_lvalue secp_ge e le m (inv_local_index id ix) b (Ptrofs.repr (8*Z.of_nat j)) Full.
Proof.
 intros J Ty Ptr Index.
 assert (Signed : Int.signed (Int.repr (Z.of_nat j))=Z.of_nat j).
 { apply Int.signed_repr;change (-2147483648<=Z.of_nat j<=2147483647);lia. }
 assert (Addr : Ptrofs.add Ptrofs.zero
  (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr (Z.of_nat j))))=Ptrofs.repr (8*Z.of_nat j)).
 { unfold Ptrofs.of_ints;rewrite Signed,Ptrofs.add_zero_l;unfold Ptrofs.mul;
   rewrite (Ptrofs.unsigned_repr (Z.of_nat j)) by (change Ptrofs.max_unsigned with (2^64-1);lia);reflexivity. }
 unfold inv_local_index;apply eval_Ederef;eapply eval_Ebinop with
  (v1:=Vptr b Ptrofs.zero) (v2:=Vint (Int.repr (Z.of_nat j))).
 - apply eval_inv_local_array;exact Ptr.
 - exact Index.
 - rewrite Ty;change (Some (Vptr b (Ptrofs.add Ptrofs.zero
     (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr (Z.of_nat j))))))=
     Some (Vptr b (Ptrofs.repr (8*Z.of_nat j))));rewrite Addr;reflexivity.
Qed.
Lemma eval_inv_local_load e le m id b ix j w : (j<5)%nat -> typeof ix=tint ->
 e!id=Some (b,fg_s62_type) -> eval_expr secp_ge e le m ix (Vint (Int.repr (Z.of_nat j))) ->
 Mem.load Mint64 m b (8*Z.of_nat j)=Some (Vlong w) ->
 eval_expr secp_ge e le m (inv_local_index id ix) (Vlong w).
Proof.
 intros J Ty Ptr Index Load;eapply eval_Elvalue with (loc:=b) (ofs:=Ptrofs.repr (8*Z.of_nat j));
  [apply eval_inv_local_index;assumption|].
 apply deref_loc_value with (chunk:=Mint64);[reflexivity|].
 unfold Mem.loadv;rewrite Ptrofs.unsigned_repr;
  [exact Load|change Ptrofs.max_unsigned with (2^64-1);lia].
Qed.
Lemma eval_inv_len_sub e le m len k : (k<=len<=5)%nat ->
 le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 eval_expr secp_ge e le m (inv_len_sub k) (Vint (Int.repr (Z.of_nat (len-k)))).
Proof.
 intros Bound Len;unfold inv_len_sub;eapply eval_Ebinop;
  [apply eval_Etempvar;exact Len|constructor|].
 change (Some (Vint (Int.sub (Int.repr (Z.of_nat len)) (Int.repr (Z.of_nat k))))=
  Some (Vint (Int.repr (Z.of_nat (len-k))))).
 unfold Int.sub;rewrite !Int.unsigned_repr by (change Int.max_unsigned with (2^32-1);lia).
 f_equal;f_equal;f_equal;lia.
Qed.

Theorem exec_inv_shorten_array len high rho beta e le m : (2<=len<=5)%nat ->
 rep rho beta (inv_shorten_in len high) m ->
 e!(inv_shorten_id high)=Some (blk beta (inv_shorten_region high),fg_s62_type) ->
 le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 le!(inv_shorten_top high)=Some (Vlong (rho (inv_shorten_offset high+(len-1))%nat)) -> exists mf,
 Clight2.exec_stmt secp_ge e le m (inv_shorten_array_step high) E0
  (PTree.set (inv_shorten_tmp high) (Vlong (rho (inv_shorten_offset high+(len-2))%nat)) le) mf Out_normal /\
 rep rho beta (inv_shorten_out len high) mf /\
 lframe (fun b _=>b<>blk beta (inv_shorten_region high)) m mf.
Proof.
 intros Len Rep Env Length Top.
 assert (At : nth_error (inv_shorten_in len high) (inv_shorten_region high)=
  Some (nth (inv_shorten_region high) (inv_shorten_in len high) (mkreg [] true None))).
 { apply nth_error_nth';rewrite inv_shorten_in_length by exact Len;destruct high;cbn [inv_shorten_region];lia. }
 pose proof (rep_owned_region_base_zero rho beta _ m _ _ 40 Rep At (inv_shorten_region_owned len high Len)) as Base.
 pose proof (xload_u64_defined_sound rho beta _ m _ _ _ Rep (inv_shorten_load len high Len)) as Load.
 rewrite Base,Z.add_0_l in Load.
 destruct (xstore_sound rho beta _ m _ _ Mint64 _ _ Rep (inv_shorten_store len high Len))
  as (mf & Store & Addr & Out & Frame).
 rewrite Base,Z.add_0_l in Store.
 exists mf;split.
 - rewrite inv_shorten_array_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set (inv_shorten_tmp high) (Vlong (rho (inv_shorten_offset high+(len-2))%nat)) le).
   + apply exec_Sset;eapply eval_inv_local_load with (j:=(len-2)%nat);
     [lia|reflexivity|exact Env|apply eval_inv_len_sub;[lia|exact Length]|exact Load].
   + eapply exec_Sassign with (loc:=blk beta (inv_shorten_region high))
      (ofs:=Ptrofs.repr (8*Z.of_nat (len-2))) (bf:=Full)
      (v2:=den rho (lay beta) (inv_shorten_expr len high))
      (v:=den rho (lay beta) (inv_shorten_expr len high)).
     * apply eval_inv_local_index;[lia|reflexivity|exact Env|].
       apply eval_inv_len_sub;[lia|rewrite PTree.gso;[exact Length|destruct high;discriminate]].
     * unfold inv_shorten_expr;eapply eval_Ebinop.
       -- apply eval_Etempvar;apply PTree.gss.
       -- eapply eval_Ebinop.
          ++ eapply eval_Ecast;[apply eval_Etempvar;rewrite PTree.gso;[exact Top|destruct high;discriminate]|reflexivity].
          ++ constructor.
          ++ reflexivity.
       -- reflexivity.
     * reflexivity.
     * apply assign_loc_value with (chunk:=Mint64);[reflexivity|].
       unfold Mem.storev;rewrite Ptrofs.unsigned_repr;
        [exact Store|change Ptrofs.max_unsigned with (2^64-1);lia].
 - split;[exact Out|].
   apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|].
   intros pos Range Other;contradiction.
Qed.

Definition inv_cond_sign_expr id := Ebinop Oxor (Etempvar id tlong)
 (Ebinop Oshr (Etempvar id tlong) (Econst_int (Int.repr 63) tint) tlong) tlong.
Definition inv_cond_merge id := Ebinop Oor (Etempvar _cond tlong) (inv_cond_sign_expr id) tlong.
Definition inv_cond_length_expr := Ebinop Oshr
 (Ebinop Osub (Ecast (Etempvar _len tint) tlong) (Econst_int (Int.repr 2) tint) tlong)
 (Econst_int (Int.repr 63) tint) tlong.
Lemma inv_shorten_prefix_source : inv_shorten_prefix=Ssequence
 (Sset _fn (inv_local_index _f (inv_len_sub 1)))
 (Ssequence (Sset _gn (inv_local_index _g (inv_len_sub 1)))
 (Ssequence (Sset _cond inv_cond_length_expr)
 (Ssequence (Sset _cond (inv_cond_merge _fn))
 (Ssequence (Sset _cond (inv_cond_merge _gn)) Sskip)))).
Proof. reflexivity. Qed.
Lemma eval_inv_cond_length e le m len : (0<len<=5)%nat ->
 le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 eval_expr secp_ge e le m inv_cond_length_expr (Vlong (inv_len_sign len)).
Proof.
 intros Bound Len;unfold inv_cond_length_expr,inv_len_sign;eapply eval_Ebinop with
  (v1:=Vlong (Int64.sub (Int64.repr (Z.of_nat len)) (Int64.repr 2))) (v2:=Vint (Int.repr 63)).
 - eapply eval_Ebinop with (v1:=Vlong (Int64.repr (Z.of_nat len))) (v2:=Vint (Int.repr 2)).
   + eapply eval_Ecast with (v1:=Vint (Int.repr (Z.of_nat len))).
     * apply eval_Etempvar;exact Len.
     * change (Some (Vlong (Int64.repr (Int.signed (Int.repr (Z.of_nat len)))) )=
        Some (Vlong (Int64.repr (Z.of_nat len)))).
       rewrite Int.signed_repr;[reflexivity|change Int.min_signed with (-2^31);change Int.max_signed with (2^31-1);lia].
   + constructor.
   + reflexivity.
 - constructor.
 - reflexivity.
Qed.
Lemma eval_inv_cond_merge e le m id a c : le!id=Some (Vlong a) -> le!_cond=Some (Vlong c) ->
 eval_expr secp_ge e le m (inv_cond_merge id) (Vlong (Int64.or c (inv_word_sign_test a))).
Proof.
 intros A C;unfold inv_cond_merge,inv_cond_sign_expr,inv_word_sign_test;eapply eval_Ebinop with
  (v1:=Vlong c) (v2:=Vlong (Int64.xor a (Int64.shr a (Int64.repr 63)))).
 - apply eval_Etempvar;exact C.
 - eapply eval_Ebinop with (v1:=Vlong a) (v2:=Vlong (Int64.shr a (Int64.repr 63)));
   [apply eval_Etempvar;exact A| |reflexivity].
   eapply eval_Ebinop;[apply eval_Etempvar;exact A|constructor|reflexivity].
 - reflexivity.
Qed.

Definition inv_short_loaded le f g := PTree.set _gn (Vlong g) (PTree.set _fn (Vlong f) le).
Definition inv_short_c1 le len := PTree.set _cond (Vlong (inv_len_sign len)) le.
Definition inv_short_c2 le len f := PTree.set _cond (Vlong (Int64.or (inv_len_sign len) (inv_word_sign_test f)))
 (inv_short_c1 le len).
Definition inv_short_prefix_env le len f g := PTree.set _cond (Vlong (inv_shorten_cond len f g))
 (inv_short_c2 (inv_short_loaded le f g) len f).
Lemma inv_short_prefix_len le len f g :
 (inv_short_prefix_env le len f g)!_len=le!_len.
Proof. unfold inv_short_prefix_env,inv_short_c2,inv_short_c1,inv_short_loaded;rewrite !PTree.gso by discriminate;reflexivity. Qed.
Lemma inv_short_prefix_top le len f g high :
 (inv_short_prefix_env le len f g)!(inv_shorten_top high)=Some (Vlong (if high then g else f)).
Proof.
 destruct high;unfold inv_short_prefix_env,inv_short_c2,inv_short_c1,inv_short_loaded,inv_shorten_top;
  rewrite !PTree.gso by discriminate;apply PTree.gss.
Qed.
Lemma inv_short_prefix_cond le len f g :
 (inv_short_prefix_env le len f g)!_cond=Some (Vlong (inv_shorten_cond len f g)).
Proof. apply PTree.gss. Qed.

Theorem exec_inv_short_prefix len f g bf bg e le m : (0<len<=5)%nat ->
 e!_f=Some (bf,fg_s62_type) -> e!_g=Some (bg,fg_s62_type) ->
 le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 Mem.load Mint64 m bf (8*Z.of_nat (len-1))=Some (Vlong f) ->
 Mem.load Mint64 m bg (8*Z.of_nat (len-1))=Some (Vlong g) ->
 Clight2.exec_stmt secp_ge e le m inv_shorten_prefix E0 (inv_short_prefix_env le len f g) m Out_normal.
Proof.
 intros Bound F G Len LF LG;rewrite inv_shorten_prefix_source.
 set (l1:=PTree.set _fn (Vlong f) le).
 set (l2:=inv_short_loaded le f g).
 set (l3:=inv_short_c1 l2 len).
 set (l4:=inv_short_c2 l2 len f).
 assert (L1 : l1!_len=Some (Vint (Int.repr (Z.of_nat len)))).
 { unfold l1;rewrite PTree.gso by discriminate;exact Len. }
 assert (L2 : l2!_len=Some (Vint (Int.repr (Z.of_nat len)))).
 { unfold l2,inv_short_loaded;rewrite !PTree.gso by discriminate;exact Len. }
 assert (F3 : l3!_fn=Some (Vlong f)).
 { unfold l3,l2,inv_short_c1,inv_short_loaded;rewrite !PTree.gso by discriminate;apply PTree.gss. }
 assert (G4 : l4!_gn=Some (Vlong g)).
 { unfold l4,l2,inv_short_c2,inv_short_c1,inv_short_loaded;rewrite !PTree.gso by discriminate;apply PTree.gss. }
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=l1) (m1:=m).
 - apply exec_Sset;eapply eval_inv_local_load with (j:=(len-1)%nat);
   [lia|reflexivity|exact F|apply eval_inv_len_sub;[lia|exact Len]|exact LF].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=l2) (m1:=m).
   + apply exec_Sset;eapply eval_inv_local_load with (j:=(len-1)%nat);
     [lia|reflexivity|exact G|apply eval_inv_len_sub;[lia|exact L1]|exact LG].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=l3) (m1:=m).
     * apply exec_Sset;apply eval_inv_cond_length;[exact Bound|exact L2].
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=l4) (m1:=m).
       -- apply exec_Sset;apply eval_inv_cond_merge;[exact F3|apply PTree.gss].
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=inv_short_prefix_env le len f g) (m1:=m).
          ++ apply exec_Sset;apply eval_inv_cond_merge;[exact G4|apply PTree.gss].
          ++ constructor.
Qed.

Definition inv_control_word (rho : nat->int64) high i := rho (inv_shorten_offset high+i)%nat.
Definition inv_control_shrink len rho := inv_shorten_guard len
 (inv_control_word rho false (len-1)) (inv_control_word rho true (len-1)).
Definition inv_shortened_length len rho := if inv_control_shrink len rho then (len-1)%nat else len.
Definition inv_shortened_regs len rho := if inv_control_shrink len rho then inv_shorten_fg_regs len else inv_control_regs.
Definition inv_shorten_modified := [_fn;_gn;_cond;_t'4;_t'3;_len].
Definition inv_shorten_temp_frame (le lf : temp_env) := forall id,~In id inv_shorten_modified -> lf!id=le!id.

Lemma inv_control_top_load len high : (0<len<=5)%nat ->
 xload inv_control_regs (inv_shorten_region high) (8*Z.of_nat (len-1)) tulong=
 Some (XLv (inv_shorten_offset high+(len-1))%nat).
Proof. destruct high;destruct len as [|[|[|[|[|[|len]]]]]];intro Len;try lia;vm_compute;reflexivity. Qed.
Lemma inv_shorten_len_source : inv_shorten_len_step=Sset _len (inv_len_sub 1).
Proof. reflexivity. Qed.
Lemma inv_short_prefix_frame le len f g : inv_shorten_temp_frame le (inv_short_prefix_env le len f g).
Proof.
 intros id Outside;unfold inv_short_prefix_env,inv_short_c2,inv_short_c1,inv_short_loaded.
 rewrite !PTree.gso;try reflexivity;unfold inv_shorten_modified in Outside;cbn [In] in Outside;intuition congruence.
Qed.

Theorem exec_inv_shortening len rho beta e le m : (0<len<=5)%nat ->
 rep rho beta inv_control_regs m -> tmatch rho beta (inv_control_temps len) le ->
 ematch beta (snd inv_start_alloc) e -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m inv_shortening E0 lef mf Out_normal /\
 rep rho beta (inv_shortened_regs len rho) mf /\
 lef!_len=Some (Vint (Int.repr (Z.of_nat (inv_shortened_length len rho)))) /\
 (0<inv_shortened_length len rho<=5)%nat /\ inv_shorten_temp_frame le lef /\
 lframe (fun b _=>b<>blk beta 4 /\ b<>blk beta 5) m mf.
Proof.
 intros Bound Rep Temps Env.
 assert (Length : le!_len=Some (Vint (Int.repr (Z.of_nat len)))) by exact (Temps _len _ eq_refl).
 assert (Base : forall high,bas beta (inv_shorten_region high)=0).
 { intro high;destruct high;eapply rep_owned_region_base_zero;[exact Rep|reflexivity|reflexivity|exact Rep|reflexivity|reflexivity]. }
 assert (Loads : forall high,Mem.load Mint64 m (blk beta (inv_shorten_region high))
  (8*Z.of_nat (len-1))=Some (Vlong (inv_control_word rho high (len-1)))).
 { intro high;pose proof (xload_u64_defined_sound rho beta _ m _ _ _ Rep (inv_control_top_load len high Bound)) as Load.
   rewrite Base,Z.add_0_l in Load;exact Load. }
 set (f:=inv_control_word rho false (len-1)).
 set (g:=inv_control_word rho true (len-1)).
 set (lp:=inv_short_prefix_env le len f g).
 pose proof (exec_inv_short_prefix len f g (blk beta 4) (blk beta 5) e le m Bound
  (proj1 (Env _f)) (proj1 (Env _g)) Length (Loads false) (Loads true)) as Prefix.
 assert (LP : lp!_len=Some (Vint (Int.repr (Z.of_nat len)))) by (unfold lp;rewrite inv_short_prefix_len;exact Length).
 assert (Cond : lp!_cond=Some (Vlong (inv_shorten_cond len f g))) by apply PTree.gss.
 pose proof (eval_inv_long_zero e lp m _cond (inv_shorten_cond len f g) Cond) as Check.
 change (eval_expr secp_ge e lp m
  (Ebinop Oeq (Etempvar _cond tlong) (Econst_int Int.zero tint) tint)
  (Vint (if inv_control_shrink len rho then Int.one else Int.zero))) in Check.
 destruct (inv_control_shrink len rho) eqn:Shrink.
 - assert (Can : inv_shorten_guard len f g=true) by exact Shrink.
   destruct (proj1 (inv_shorten_guard_correct len f g Bound) Can) as (Len2 & SignF & SignG).
   destruct (exec_inv_shorten_array len false rho beta e lp m ltac:(lia) Rep
    (proj1 (Env _f)) LP (inv_short_prefix_top le len f g false))
    as (m1 & CopyF & RepF & FrameF).
   set (l1:=PTree.set _t'4 (Vlong (inv_control_word rho false (len-2))) lp).
   assert (L1 : l1!_len=Some (Vint (Int.repr (Z.of_nat len)))).
   { unfold l1;rewrite PTree.gso by discriminate;exact LP. }
   assert (G1 : l1!_gn=Some (Vlong g)).
   { unfold l1;rewrite PTree.gso by discriminate;exact (inv_short_prefix_top le len f g true). }
   destruct (exec_inv_shorten_array len true rho beta e l1 m1 ltac:(lia) RepF (proj1 (Env _g)) L1 G1)
    as (mf & CopyG & RepG & FrameG).
   set (l2:=PTree.set _t'3 (Vlong (inv_control_word rho true (len-2))) l1).
   set (lf:=PTree.set _len (Vint (Int.repr (Z.of_nat (len-1)))) l2).
   exists lf,mf;split.
   + rewrite inv_shorten_source;eapply exec_statement_prefix_then_last;[exact Prefix|].
     eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[exact Check|reflexivity|].
     rewrite inv_shorten_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=l1) (m1:=m1);[exact CopyF|].
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=l2) (m1:=mf);[exact CopyG|].
     rewrite inv_shorten_len_source;apply exec_Sset;apply eval_inv_len_sub;[lia|].
     unfold l2;rewrite PTree.gso by discriminate;exact L1.
   + unfold inv_shortened_regs,inv_shortened_length;rewrite Shrink;split;[exact RepG|];split;[apply PTree.gss|];split;[lia|];split.
     * intros id Outside;unfold lf,l2,l1;rewrite !PTree.gso;
        try (apply inv_short_prefix_frame;exact Outside);
        unfold inv_shorten_modified in Outside;cbn [In] in Outside;intuition congruence.
     * eapply lframe_trans;[eapply lframe_implies;[exact FrameF|]|eapply lframe_implies;[exact FrameG|]];
        intros b pos [F G] Valid;assumption.
 - exists lp,m;split.
   + rewrite inv_shorten_source;eapply exec_statement_prefix_then_last;[exact Prefix|].
     eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[exact Check|reflexivity|constructor].
   + unfold inv_shortened_regs,inv_shortened_length;rewrite Shrink;split;[exact Rep|];split;[exact LP|];split;[exact Bound|].
     split;[apply inv_short_prefix_frame|apply lframe_refl].
Qed.

Definition inv_shorten_get_expr len high i := if Nat.eqb i (len-2) then inv_shorten_expr len high
 else XLv (inv_shorten_offset high+i)%nat.
Definition inv_control_short_word len rho high i := if inv_control_shrink len rho
 then inv_shorten_words len (inv_control_word rho high) i else inv_control_word rho high i.
Lemma inv_shorten_get len high i : (2<=len<=5)%nat -> (i<5)%nat ->
 xload (inv_shorten_fg_regs len) (inv_shorten_region high) (8*Z.of_nat i) tulong=
 Some (inv_shorten_get_expr len high i).
Proof.
 destruct high;destruct len as [|[|[|[|[|[|len]]]]]];
  destruct i as [|[|[|[|[|i]]]]];intros Len I;try lia;vm_compute;reflexivity.
Qed.
Lemma inv_shorten_get_den rho beta len high i :
 den rho beta (inv_shorten_get_expr len high i)=
 Vlong (inv_shorten_words len (inv_control_word rho high) i).
Proof.
 unfold inv_shorten_get_expr,inv_shorten_words;destruct (Nat.eqb i (len-2)) eqn:E.
 - apply Nat.eqb_eq in E;subst i;reflexivity.
 - reflexivity.
Qed.
Lemma inv_control_word_load high i : (i<5)%nat ->
 xload inv_control_regs (inv_shorten_region high) (8*Z.of_nat i) tulong=
 Some (XLv (inv_shorten_offset high+i)%nat).
Proof. destruct high;destruct i as [|[|[|[|[|i]]]]];intro I;try lia;reflexivity. Qed.
Lemma inv_shortened_loads len rho beta m : (0<len<=5)%nat -> rep rho beta (inv_shortened_regs len rho) m ->
 forall high i,(i<5)%nat -> Mem.load Mint64 m (blk beta (inv_shorten_region high))
 (bas beta (inv_shorten_region high)+8*Z.of_nat i)=Some (Vlong (inv_control_short_word len rho high i)).
Proof.
 intros Len Rep high i I;unfold inv_shortened_regs in Rep;unfold inv_control_short_word.
 destruct (inv_control_shrink len rho) eqn:Shrink.
 - assert (Len2 : (2<=len<=5)%nat).
   { pose proof (proj1 (inv_shorten_guard_correct len _ _ Len) Shrink) as [Two _];lia. }
   pose proof (xload_u64_defined_sound rho beta _ m _ _ _ Rep (inv_shorten_get len high i Len2 I)) as Load.
   rewrite inv_shorten_get_den in Load;exact Load.
 - exact (xload_u64_defined_sound rho beta _ m _ _ _ Rep (inv_control_word_load high i I)).
Qed.
Lemma inv_shortened_numeric len rho high : (0<len<=5)%nat -> inv_active_low_bounds len (inv_control_word rho high) ->
 inv_active_value (inv_shortened_length len rho) (inv_control_short_word len rho high)=
 inv_active_value len (inv_control_word rho high) /\
 inv_active_low_bounds (inv_shortened_length len rho) (inv_control_short_word len rho high).
Proof.
 intros Len Low;unfold inv_shortened_length,inv_control_short_word;destruct (inv_control_shrink len rho) eqn:Shrink.
 - destruct (proj1 (inv_shorten_guard_correct len _ _ Len) Shrink) as (Two & F & G);split.
   + apply inv_shorten_preserves_value;[lia|exact Low|destruct high;assumption].
   + intros i I;unfold inv_shorten_words.
     rewrite (proj2 (Nat.eqb_neq i (len-2)) ltac:(lia));apply Low;lia.
 - split;[reflexivity|exact Low].
Qed.

Corollary exec_inv_shortening_numeric len rho beta e le m : (0<len<=5)%nat ->
 rep rho beta inv_control_regs m -> tmatch rho beta (inv_control_temps len) le ->
 ematch beta (snd inv_start_alloc) e ->
 (forall high,inv_active_low_bounds len (inv_control_word rho high)) -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m inv_shortening E0 lef mf Out_normal /\
 rep rho beta (inv_shortened_regs len rho) mf /\
 (forall high i,(i<5)%nat -> Mem.load Mint64 mf (blk beta (inv_shorten_region high))
   (bas beta (inv_shorten_region high)+8*Z.of_nat i)=Some (Vlong (inv_control_short_word len rho high i))) /\
 (forall high,inv_active_value (inv_shortened_length len rho) (inv_control_short_word len rho high)=
   inv_active_value len (inv_control_word rho high) /\
   inv_active_low_bounds (inv_shortened_length len rho) (inv_control_short_word len rho high)) /\
 lef!_len=Some (Vint (Int.repr (Z.of_nat (inv_shortened_length len rho)))) /\
 (0<inv_shortened_length len rho<=5)%nat /\ inv_shorten_temp_frame le lef /\
 lframe (fun b _=>b<>blk beta 4 /\ b<>blk beta 5) m mf.
Proof.
 intros Len Rep Temps Env Bounds;destruct (exec_inv_shortening len rho beta e le m Len Rep Temps Env)
  as (lef & mf & Exec & Out & Length & Range & Frame & MemFrame).
 exists lef,mf;split;[exact Exec|];split;[exact Out|];split.
 - apply inv_shortened_loads;assumption.
 - split;[intro high;apply inv_shortened_numeric;[exact Len|apply Bounds]|].
   split;[exact Length|];split;[exact Range|];split;assumption.
Qed.
