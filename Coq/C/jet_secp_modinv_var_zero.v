(** The original inverse caller's zero-test, without any callee assumption. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix.
Require Import C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_copies C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_modinv_fg_index C.jet_secp_u128_shift64_rep.
Require Import C.jet_secp_modinv_normalize62_words.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition inv_caller_loop := match inv_after_ready with Ssequence s _=>s | _=>Sskip end.
Definition inv_caller_loop_body := match inv_caller_loop with Sloop s _=>s | _=>Sskip end.
Definition inv_caller_loop_parts := split_statement_last inv_caller_loop_body.
Definition inv_zero_test := nth 4 (fst inv_caller_loop_parts) Sskip.
Definition inv_shortening := statement_sequence (skipn 5 (fst inv_caller_loop_parts)) (snd inv_caller_loop_parts).
Lemma inv_caller_loop_source : inv_caller_loop=Sloop inv_caller_loop_body Sskip.
Proof. reflexivity. Qed.
Lemma inv_caller_control_source : inv_caller_loop_body=
 statement_sequence (firstn 4 (fst inv_caller_loop_parts)) (Ssequence inv_zero_test inv_shortening).
Proof. reflexivity. Qed.

Definition inv_control_regs := upd (upd (sregs inv_start_state) 4
 (mkreg (u64_cells 0 (vars5 5)) true (Some 40))) 5
 (mkreg (u64_cells 0 (vars5 10)) true (Some 40)).
Definition inv_control_temps len := PTree.set _len (XIc (Int.repr (Z.of_nat len))) (PTree.empty sx).

Definition inv_g_array := Efield (Evar _g fg_s62_type) _v (tarray tlong 5).
Definition inv_g_index ix := Ederef (Ebinop Oadd inv_g_array ix (tptr tlong)) tlong.
Definition inv_gather_guard := Ebinop Olt (Etempvar _j tint) (Etempvar _len tint) tint.
Definition inv_gather_work := Ssequence
 (Sset _t'6 (inv_g_index (Etempvar _j tint)))
 (Sset _cond (Ebinop Oor (Etempvar _cond tlong) (Etempvar _t'6 tlong) tlong)).
Definition inv_gather_step := Sset _j (Ebinop Oadd (Etempvar _j tint) (Econst_int Int.one tint) tint).
Definition inv_gather_loop := Sloop
 (Ssequence (Sifthenelse inv_gather_guard Sskip Sbreak) inv_gather_work) inv_gather_step.
Lemma inv_zero_test_source : inv_zero_test=Ssequence
 (Sset _t'5 (inv_g_index (Econst_int Int.zero tint)))
 (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tlong) (Econst_int Int.zero tint) tint)
  (Ssequence (Sset _cond (Ecast (Econst_int Int.zero tint) tlong))
   (Ssequence (Ssequence (Sset _j (Econst_int Int.one tint)) inv_gather_loop)
    (Sifthenelse (Ebinop Oeq (Etempvar _cond tlong) (Econst_int Int.zero tint) tint) Sbreak Sskip))) Sskip).
Proof. reflexivity. Qed.

Definition inv_test_modified := [_t'5;_cond;_j;_t'6].
Definition inv_test_frame (le lf : temp_env) := forall id,~In id inv_test_modified -> lf!id=le!id.
Lemma inv_test_frame_refl le : inv_test_frame le le.
Proof. intros id _;reflexivity. Qed.
Lemma inv_test_frame_trans le lm lf : inv_test_frame le lm -> inv_test_frame lm lf -> inv_test_frame le lf.
Proof. intros A B id Outside;rewrite (B id Outside);apply A;exact Outside. Qed.
Lemma inv_test_frame_set le id v : In id inv_test_modified -> inv_test_frame le (PTree.set id v le).
Proof. intros Member key Outside;rewrite PTree.gso;[reflexivity|intro Eq;subst key;contradiction]. Qed.
Lemma inv_test_frame_length le lf : inv_test_frame le lf -> lf!_len=le!_len.
Proof. intro Frame;apply Frame;unfold inv_test_modified;cbn [In];intuition discriminate. Qed.

Lemma eval_inv_g_array e le m b : e!_g=Some (b,fg_s62_type) ->
 eval_expr secp_ge e le m inv_g_array (Vptr b Ptrofs.zero).
Proof.
 intro Ptr;destruct fg_array_layout as (co & Composite & Offset).
 eapply eval_Elvalue with (loc:=b) (ofs:=Ptrofs.zero).
 - change Ptrofs.zero with (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0)) at 1.
   unfold inv_g_array;eapply eval_Efield_struct with (co:=co) (delta:=0).
   + eapply eval_Elvalue;[apply eval_Evar_local;exact Ptr|apply deref_loc_copy;reflexivity].
   + reflexivity.
   + exact Composite.
   + exact Offset.
 - apply deref_loc_reference;reflexivity.
Qed.
Lemma eval_inv_g_index e le m b ix j w : (j<5)%nat -> typeof ix=tint ->
 e!_g=Some (b,fg_s62_type) -> eval_expr secp_ge e le m ix (Vint (Int.repr (Z.of_nat j))) ->
 Mem.load Mint64 m b (8*Z.of_nat j)=Some (Vlong w) ->
 eval_expr secp_ge e le m (inv_g_index ix) (Vlong w).
Proof.
 intros J Ty Ptr Index Load.
 assert (Signed : Int.signed (Int.repr (Z.of_nat j))=Z.of_nat j).
 { apply Int.signed_repr;change (-2147483648<=Z.of_nat j<=2147483647);lia. }
 assert (Addr : Ptrofs.add Ptrofs.zero
  (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr (Z.of_nat j))))=Ptrofs.repr (8*Z.of_nat j)).
 { unfold Ptrofs.of_ints;rewrite Signed,Ptrofs.add_zero_l;unfold Ptrofs.mul;
   rewrite (Ptrofs.unsigned_repr (Z.of_nat j)) by (change Ptrofs.max_unsigned with (2^64-1);lia);reflexivity. }
 eapply eval_Elvalue with (loc:=b) (ofs:=Ptrofs.repr (8*Z.of_nat j)).
 - unfold inv_g_index;apply eval_Ederef;eapply eval_Ebinop with
    (v1:=Vptr b Ptrofs.zero) (v2:=Vint (Int.repr (Z.of_nat j))).
   + apply eval_inv_g_array;exact Ptr.
   + exact Index.
   + rewrite Ty;change (Some (Vptr b (Ptrofs.add Ptrofs.zero
       (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr (Z.of_nat j))))))=
       Some (Vptr b (Ptrofs.repr (8*Z.of_nat j))));rewrite Addr;reflexivity.
 - apply deref_loc_value with (chunk:=Mint64);[reflexivity|].
   unfold Mem.loadv;rewrite Ptrofs.unsigned_repr;
    [exact Load|change Ptrofs.max_unsigned with (2^64-1);lia].
Qed.

Lemma eval_inv_gather_guard e le m j len : (j<=len<=5)%nat ->
 le!_j=Some (Vint (Int.repr (Z.of_nat j))) -> le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 eval_expr secp_ge e le m inv_gather_guard (Vint (if (j <? len)%nat then Int.one else Int.zero)).
Proof.
 intros Bound J Len;unfold inv_gather_guard;eapply eval_Ebinop;
  [apply eval_Etempvar;exact J|apply eval_Etempvar;exact Len|].
 change (Some (Val.of_bool (Int.lt (Int.repr (Z.of_nat j)) (Int.repr (Z.of_nat len))))=
  Some (Vint (if (j <? len)%nat then Int.one else Int.zero))).
 unfold Int.lt;rewrite !Int.signed_repr by (change Int.min_signed with (-2^31);change Int.max_signed with (2^31-1);lia).
 destruct (zlt (Z.of_nat j) (Z.of_nat len)),(Nat.ltb_spec j len);try lia;reflexivity.
Qed.
Lemma exec_inv_gather_step e le m j : (j<5)%nat -> le!_j=Some (Vint (Int.repr (Z.of_nat j))) ->
 Clight2.exec_stmt secp_ge e le m inv_gather_step E0
  (PTree.set _j (Vint (Int.repr (Z.of_nat (S j)))) le) m Out_normal.
Proof.
 intros J Ptr;unfold inv_gather_step;apply exec_Sset;eapply eval_Ebinop;
  [apply eval_Etempvar;exact Ptr|constructor|].
 change (Some (Vint (Int.add (Int.repr (Z.of_nat j)) Int.one))=Some (Vint (Int.repr (Z.of_nat (S j))))).
 unfold Int.add;rewrite Int.unsigned_repr by (change Int.max_unsigned with (2^32-1);lia).
 rewrite Int.unsigned_one;f_equal;f_equal;f_equal;lia.
Qed.

Fixpoint inv_gather_words n (w : nat->int64) j acc := match n with
 | O=>acc | S n=>inv_gather_words n w (S j) (Int64.or acc (w j)) end.
Definition inv_gather_work_env le w acc := PTree.set _cond (Vlong (Int64.or acc w))
 (PTree.set _t'6 (Vlong w) le).
Lemma exec_inv_gather_work e le m b j acc w : (j<5)%nat ->
 e!_g=Some (b,fg_s62_type) -> le!_j=Some (Vint (Int.repr (Z.of_nat j))) ->
 le!_cond=Some (Vlong acc) -> Mem.load Mint64 m b (8*Z.of_nat j)=Some (Vlong w) ->
 Clight2.exec_stmt secp_ge e le m inv_gather_work E0 (inv_gather_work_env le w acc) m Out_normal /\
 inv_test_frame le (inv_gather_work_env le w acc).
Proof.
 intros J G Index Cond Load;split.
 - unfold inv_gather_work,inv_gather_work_env;eapply exec_Sseq_1 with
    (t1:=E0) (t2:=E0) (le1:=PTree.set _t'6 (Vlong w) le) (m1:=m).
   + apply exec_Sset;eapply eval_inv_g_index;[exact J|reflexivity|exact G|apply eval_Etempvar;exact Index|exact Load].
   + apply exec_Sset;eapply eval_Ebinop.
     * apply eval_Etempvar;rewrite PTree.gso by discriminate;exact Cond.
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
 - unfold inv_gather_work_env;eapply inv_test_frame_trans;apply inv_test_frame_set;
   unfold inv_test_modified;cbn [In];tauto.
Qed.

Theorem exec_inv_gather n len j w acc e le m b :
 (j+n=len)%nat -> (1<=j<=len /\ len<=5)%nat -> e!_g=Some (b,fg_s62_type) ->
 le!_j=Some (Vint (Int.repr (Z.of_nat j))) -> le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 le!_cond=Some (Vlong acc) ->
 (forall i,(i<len)%nat -> Mem.load Mint64 m b (8*Z.of_nat i)=Some (Vlong (w i))) -> exists lef,
 Clight2.exec_stmt secp_ge e le m inv_gather_loop E0 lef m Out_normal /\
 lef!_cond=Some (Vlong (inv_gather_words n w j acc)) /\ inv_test_frame le lef.
Proof.
 revert j acc le;induction n as [|n IH];intros j acc le Sum Bound G J Len Cond Loads.
 - assert (JL : j=len) by lia;subst j;exists le;split.
   + unfold inv_gather_loop;eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
     eapply exec_Sseq_2;[|discriminate];eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
     * pose proof (eval_inv_gather_guard e le m len len ltac:(lia) J Len) as Guard;rewrite Nat.ltb_irrefl in Guard;exact Guard.
     * reflexivity.
     * constructor.
   + split;[exact Cond|apply inv_test_frame_refl].
 - destruct (exec_inv_gather_work e le m b j acc (w j) ltac:(lia) G J Cond (Loads j ltac:(lia))) as (Work & WorkFrame).
   set (lw:=inv_gather_work_env le (w j) acc).
   set (ls:=PTree.set _j (Vint (Int.repr (Z.of_nat (S j)))) lw).
   assert (JW : lw!_j=Some (Vint (Int.repr (Z.of_nat j)))).
   { unfold lw,inv_gather_work_env;rewrite !PTree.gso by discriminate;exact J. }
   assert (LS : ls!_len=Some (Vint (Int.repr (Z.of_nat len)))).
   { unfold ls,lw,inv_gather_work_env;rewrite !PTree.gso by discriminate;exact Len. }
   assert (CS : ls!_cond=Some (Vlong (Int64.or acc (w j)))).
   { unfold ls;rewrite PTree.gso by discriminate;apply PTree.gss. }
   destruct (IH (S j) (Int64.or acc (w j)) ls ltac:(lia) ltac:(lia) G
    ltac:(apply PTree.gss) LS CS Loads) as (lef & Rest & Result & RestFrame).
   exists lef;split.
   + unfold inv_gather_loop at 1;eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0)
      (le1:=lw) (m1:=m) (out1:=Out_normal) (le2:=ls) (m2:=m).
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m);[|exact Work].
       eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
       -- pose proof (eval_inv_gather_guard e le m j len ltac:(lia) J Len) as Guard.
          rewrite (proj2 (Nat.ltb_lt j len) ltac:(lia)) in Guard;exact Guard.
       -- reflexivity.
       -- constructor.
     * left;reflexivity.
     * apply exec_inv_gather_step;[lia|exact JW].
     * exact Rest.
   + split;[exact Result|];eapply inv_test_frame_trans;[exact WorkFrame|].
     eapply inv_test_frame_trans;[|exact RestFrame];apply inv_test_frame_set;
      unfold inv_test_modified;cbn [In];tauto.
Qed.

Lemma inv_or_zero a b : Int64.or a b=Int64.zero <-> a=Int64.zero /\ b=Int64.zero.
Proof.
 split.
 - intro Zero.
   assert (A : Int64.unsigned a=0).
   { pose proof (Int64.or_le a b) as L;rewrite Zero,Int64.unsigned_zero in L;
     pose proof (Int64.unsigned_range_2 a);lia. }
   assert (B : Int64.unsigned b=0).
   { pose proof (Int64.or_le b a) as L;rewrite Int64.or_commut,Zero,Int64.unsigned_zero in L;
     pose proof (Int64.unsigned_range_2 b);lia. }
   split;[rewrite <-(Int64.repr_unsigned a),A|rewrite <-(Int64.repr_unsigned b),B];reflexivity.
 - intros [-> ->];apply Int64.or_zero.
Qed.
Lemma inv_gather_zero n w : forall j acc,
 inv_gather_words n w j acc=Int64.zero <->
 acc=Int64.zero /\ forall i,(i<n)%nat -> w (j+i)%nat=Int64.zero.
Proof.
 induction n as [|n IH];intros j acc;cbn [inv_gather_words].
 - split;[intro E;split;[exact E|intros;lia]|intros [E _];exact E].
 - rewrite IH,inv_or_zero;split.
   + intros [[A W] Rest];split;[exact A|];intros [|i] I.
     * rewrite Nat.add_0_r;exact W.
     * replace (j+S i)%nat with (S j+i)%nat by lia;apply Rest;lia.
   + intros [A Words];split;[split;[exact A|]|].
     * replace j with (j+0)%nat at 1 by lia;apply Words;lia.
     * intros i I;replace (S j+i)%nat with (j+S i)%nat by lia;apply Words;lia.
Qed.
Lemma inv_int64_zero_eq a : Int64.eq a Int64.zero=true <-> a=Int64.zero.
Proof. split;[apply Int64.same_if_eq|intro E;subst a;apply Int64.eq_true]. Qed.
Definition inv_g_is_zero len (w : nat->int64) :=
 Int64.eq (w 0%nat) Int64.zero && Int64.eq (inv_gather_words (len-1) w 1 Int64.zero) Int64.zero.
Lemma inv_g_is_zero_correct len w : (0<len)%nat ->
 inv_g_is_zero len w=true <-> forall i,(i<len)%nat -> w i=Int64.zero.
Proof.
 intro Positive;unfold inv_g_is_zero;rewrite andb_true_iff,!inv_int64_zero_eq,inv_gather_zero;split.
 - intros [Low [_ Rest]] [|i] I;[exact Low|].
   change (w (1+i)%nat=Int64.zero);apply Rest;lia.
 - intro All;split;[apply All;lia|];split;[reflexivity|].
   intros i I;apply All;lia.
Qed.
Definition inv_zero_out len w := if inv_g_is_zero len w then Out_break else Out_normal.
Lemma inv_zero_out_correct len w : (0<len)%nat ->
 inv_zero_out len w=Out_break <-> forall i,(i<len)%nat -> w i=Int64.zero.
Proof.
 intro Pos;rewrite <-inv_g_is_zero_correct by exact Pos;unfold inv_zero_out.
 destruct (inv_g_is_zero len w);split;intro E;try reflexivity;discriminate.
Qed.

Lemma eval_inv_long_zero e le m id w : le!id=Some (Vlong w) ->
 eval_expr secp_ge e le m (Ebinop Oeq (Etempvar id tlong) (Econst_int Int.zero tint) tint)
  (Vint (if Int64.eq w Int64.zero then Int.one else Int.zero)).
Proof.
 intro Value;eapply eval_Ebinop;[apply eval_Etempvar;exact Value|constructor|].
 change (Some (Val.of_bool (Int64.eq w Int64.zero))=
  Some (Vint (if Int64.eq w Int64.zero then Int.one else Int.zero)));destruct (Int64.eq w Int64.zero);reflexivity.
Qed.

Theorem exec_inv_zero_from_loads len w e le m b : (0<len<=5)%nat ->
 e!_g=Some (b,fg_s62_type) -> le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 (forall i,(i<len)%nat -> Mem.load Mint64 m b (8*Z.of_nat i)=Some (Vlong (w i))) -> exists lef,
 Clight2.exec_stmt secp_ge e le m inv_zero_test E0 lef m (inv_zero_out len w) /\ inv_test_frame le lef.
Proof.
 intros Bound G Len Loads.
 set (l0:=PTree.set _t'5 (Vlong (w 0%nat)) le).
 assert (SetLow : Clight2.exec_stmt secp_ge e le m
  (Sset _t'5 (inv_g_index (Econst_int Int.zero tint))) E0 l0 m Out_normal).
 { apply exec_Sset;eapply eval_inv_g_index with (j:=0%nat);
   [lia|reflexivity|exact G|constructor|apply Loads;lia]. }
 assert (LowFrame : inv_test_frame le l0).
 { apply inv_test_frame_set;unfold inv_test_modified;cbn [In];tauto. }
 assert (Low : l0!_t'5=Some (Vlong (w 0%nat))) by apply PTree.gss.
 unfold inv_zero_out,inv_g_is_zero;destruct (Int64.eq (w 0%nat) Int64.zero) eqn:LowZero;cbn [andb].
 - set (lz:=PTree.set _cond (Vlong Int64.zero) l0).
   set (lj:=PTree.set _j (Vint Int.one) lz).
   assert (Length : lj!_len=Some (Vint (Int.repr (Z.of_nat len)))).
   { unfold lj,lz,l0;rewrite !PTree.gso by discriminate;exact Len. }
   assert (Cond : lj!_cond=Some (Vlong Int64.zero)).
   { unfold lj;rewrite PTree.gso by discriminate;apply PTree.gss. }
   destruct (exec_inv_gather (len-1) len 1 w Int64.zero e lj m b ltac:(lia) ltac:(lia) G
    ltac:(apply PTree.gss) Length Cond Loads) as (lc & Gather & FinalCond & GatherFrame).
   exists lc;split.
   + rewrite inv_zero_test_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=l0) (m1:=m);[exact SetLow|].
     eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
     * pose proof (eval_inv_long_zero e l0 m _t'5 (w 0%nat) Low) as Check;rewrite LowZero in Check;exact Check.
     * reflexivity.
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lz) (m1:=m).
       -- apply exec_Sset;eapply eval_Ecast;[constructor|reflexivity].
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lc) (m1:=m).
          ++ eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lj) (m1:=m);
              [apply exec_Sset;constructor|exact Gather].
          ++ eapply exec_Sifthenelse with
              (v1:=Vint (if Int64.eq (inv_gather_words (len-1) w 1 Int64.zero) Int64.zero then Int.one else Int.zero))
              (b:=Int64.eq (inv_gather_words (len-1) w 1 Int64.zero) Int64.zero).
             ** apply eval_inv_long_zero;exact FinalCond.
             ** destruct (Int64.eq (inv_gather_words (len-1) w 1 Int64.zero) Int64.zero);reflexivity.
             ** destruct (Int64.eq (inv_gather_words (len-1) w 1 Int64.zero) Int64.zero);constructor.
   + eapply inv_test_frame_trans;[exact LowFrame|].
     eapply inv_test_frame_trans with (lm:=lz);[apply inv_test_frame_set;unfold inv_test_modified;cbn [In];tauto|].
     eapply inv_test_frame_trans with (lm:=lj);
      [apply inv_test_frame_set;unfold inv_test_modified;cbn [In];tauto|exact GatherFrame].
 - exists l0;split;[|exact LowFrame].
   rewrite inv_zero_test_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=l0) (m1:=m);[exact SetLow|].
   eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
   + pose proof (eval_inv_long_zero e l0 m _t'5 (w 0%nat) Low) as Check;rewrite LowZero in Check;exact Check.
   + reflexivity.
   + constructor.
Qed.

Lemma inv_control_g_load i : (i<5)%nat ->
 xload inv_control_regs 5 (8*Z.of_nat i) tulong=Some (XLv (10+i)).
Proof. destruct i as [|[|[|[|[|i]]]]];intro I;try lia;reflexivity. Qed.
Theorem exec_inv_zero_test len rho beta e le m : (0<len<=5)%nat ->
 rep rho beta inv_control_regs m -> tmatch rho beta (inv_control_temps len) le ->
 ematch beta (snd inv_start_alloc) e -> exists lef,
 Clight2.exec_stmt secp_ge e le m inv_zero_test E0 lef m
  (inv_zero_out len (fun i=>rho (10+i)%nat)) /\
 inv_test_frame le lef /\ lef!_len=Some (Vint (Int.repr (Z.of_nat len))).
Proof.
 intros Bound Rep Temps Env.
 assert (Base : bas beta 5=0) by (eapply rep_owned_region_base_zero;[exact Rep|reflexivity|reflexivity]).
 assert (Length : le!_len=Some (Vint (Int.repr (Z.of_nat len)))) by exact (Temps _len _ eq_refl).
 assert (Loads : forall i,(i<len)%nat ->
  Mem.load Mint64 m (blk beta 5) (8*Z.of_nat i)=Some (Vlong (rho (10+i)%nat))).
 { intros i I;pose proof (xload_u64_defined_sound rho beta _ m _ _ _ Rep (inv_control_g_load i ltac:(lia))) as Load.
   rewrite Base,Z.add_0_l in Load;exact Load. }
 destruct (exec_inv_zero_from_loads len (fun i=>rho (10+i)%nat) e le m (blk beta 5)
  Bound (proj1 (Env _g)) Length Loads) as (lef & Exec & Frame).
 exists lef;split;[exact Exec|];split;[exact Frame|];rewrite (inv_test_frame_length _ _ Frame);exact Length.
Qed.

Lemma inv_signed62_zero n : forall w : nat->Z,
 (forall i,(i<n)%nat -> 0<=w i<2^62) ->
 norm62_value_z n w=0 <-> forall i,(i<=n)%nat -> w i=0.
Proof.
 induction n as [|n IH];intros w Bounds;cbn [norm62_value_z].
 - split;[intros Zero i I;assert (i=0)%nat by lia;subst i;exact Zero|intro Words;apply Words;lia].
 - assert (Lower : forall i,(i<n)%nat -> 0<=(fun j=>w (S j)) i<2^62)
    by (intros i I;apply Bounds;lia).
   specialize (IH (fun j=>w (S j)) Lower).
   split.
   + intro Zero;pose proof (Bounds 0%nat ltac:(lia)) as Low.
     assert (Tail : norm62_value_z n (fun j=>w (S j))=0) by lia.
     assert (Head : w 0%nat=0) by lia.
     intros [|i] I;[exact Head|apply (proj1 IH Tail);lia].
   + intro Words;rewrite (Words 0%nat ltac:(lia)).
     rewrite (proj2 IH ltac:(intros i I;apply Words;lia));ring.
Qed.

Definition inv_active_value len w := norm62_value_z (len-1) (fun i=>Int64.signed (w i)).
Definition inv_active_low_bounds len w := forall i,(S i<len)%nat -> 0<=Int64.signed (w i)<2^62.
Lemma inv_zero_out_value len w : (0<len)%nat -> inv_active_low_bounds len w ->
 inv_zero_out len w=Out_break <-> inv_active_value len w=0.
Proof.
 intros Pos Bounds;rewrite inv_zero_out_correct by exact Pos.
 unfold inv_active_value;rewrite inv_signed62_zero by (intros i I;apply Bounds;lia).
 split.
 - intros Words i I;rewrite (Words i ltac:(lia));apply Int64.signed_zero.
 - intros Words i I;rewrite <-(Int64.repr_signed (w i)),(Words i ltac:(lia));reflexivity.
Qed.

Corollary exec_inv_zero_test_numeric len rho beta e le m : (0<len<=5)%nat ->
 rep rho beta inv_control_regs m -> tmatch rho beta (inv_control_temps len) le ->
 ematch beta (snd inv_start_alloc) e -> inv_active_low_bounds len (fun i=>rho (10+i)%nat) ->
 exists lef out,
 Clight2.exec_stmt secp_ge e le m inv_zero_test E0 lef m out /\
 (out=Out_break <-> inv_active_value len (fun i=>rho (10+i)%nat)=0) /\
 (out=Out_break \/ out=Out_normal) /\ inv_test_frame le lef /\
 lef!_len=Some (Vint (Int.repr (Z.of_nat len))).
Proof.
 intros Bound Rep Temps Env Digits;destruct (exec_inv_zero_test len rho beta e le m Bound Rep Temps Env)
  as (lef & Exec & Frame & Length).
 exists lef,(inv_zero_out len (fun i=>rho (10+i)%nat));split;[exact Exec|];split.
 - apply inv_zero_out_value;[lia|exact Digits].
 - split;[unfold inv_zero_out;destruct (inv_g_is_zero len _);auto|split;assumption].
Qed.
