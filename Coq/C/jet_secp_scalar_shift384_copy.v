(** The four original quotient stores at shift 384. Constant control-flow
    guards are proved against the actual statement tree, including the
    short-circuit branches that avoid out-of-range product reads. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_scalar_shift384_control C.jet_secp_statement_prefix.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition shift384_copy_value i word := if (i<?2)%nat then word else Int64.zero.
Definition shift384_copy_temps (i:nat) le word := match i with
 | O=>PTree.set _t'1 (Vlong word) (PTree.set _t'17 (Vlong word)
   (PTree.set _t'3 (Vlong Int64.zero) (PTree.set _t'2 (Vint Int.zero) le)))
 | S O=>PTree.set _t'4 (Vlong word) (PTree.set _t'15 (Vlong word)
   (PTree.set _t'6 (Vlong Int64.zero) (PTree.set _t'5 (Vint Int.zero) le)))
 | S (S O)=>PTree.set _t'7 (Vlong Int64.zero) le
 | _=>PTree.set _t'10 (Vlong Int64.zero) le
 end.
Definition shift384_copy_ids (i:nat) : list ident := match i with
 | O=>[_t'1;_t'17;_t'3;_t'2]
 | S O=>[_t'4;_t'15;_t'6;_t'5]
 | S (S O)=>[_t'7]
 | _=>[_t'10] end.
Lemma shift384_copy_other i le word id : ~In id (shift384_copy_ids i) ->
 (shift384_copy_temps i le word)!id=le!id.
Proof.
 intro Outside;unfold shift384_copy_temps,shift384_copy_ids in *.
 destruct i as [|[|[|i]]];repeat rewrite PTree.gso;
 try reflexivity;intro Eq;subst id;apply Outside;cbn [In];tauto.
Qed.

Local Ltac copy_lookup := first [eassumption|apply PTree.gss|rewrite PTree.gso by discriminate;copy_lookup].
Local Ltac copy_sem := first [reflexivity|
 rewrite ?Int64.shru_zero,?Int64.or_zero;reflexivity].
Local Ltac copy_expr bl word Load := first
 [apply eval_Etempvar;copy_lookup|apply eval_Econst_int|apply eval_Econst_long|
  solve [eapply (eval_shift384_array _ _ _ bl 0 word);[lia|eassumption|copy_lookup|apply Load;lia]]|
  solve [eapply (eval_shift384_array _ _ _ bl 1 word);[lia|eassumption|copy_lookup|apply Load;lia]]|
  eapply eval_Ecast;[copy_expr bl word Load|copy_sem]|
  eapply eval_Ebinop;[copy_expr bl word Load|copy_expr bl word Load|copy_sem]].

Theorem exec_shift384_copy i e le m mf br bl word : (i<4)%nat ->
 e!_l=Some (bl,tarray tulong 8) -> le!_r=Some (Vptr br Ptrofs.zero) ->
 le!_shift=Some (Vint (Int.repr 384)) -> le!_shiftlow=Some (Vint Int.zero) ->
 le!_shiftlimbs=Some (Vint (Int.repr 6)) ->
 ((i<2)%nat -> Mem.load Mint64 m bl (8*(6+Z.of_nat i))=Some (Vlong word)) ->
 Mem.store Mint64 m br (8*Z.of_nat i) (Vlong (shift384_copy_value i word))=Some mf ->
 Clight2.exec_stmt secp_ge e le m (shift384_copy_statement i) E0
  (shift384_copy_temps i le word) mf Out_normal.
Proof.
 intros Index Local R Shift Low Limbs Load Store.
 destruct i as [|[|[|[|i]]]];try lia;
 cbn [shift384_copy_statement shift384_parts split_statement_last fn_body
  f_secp256k1_scalar_mul_shift_var fst nth Nat.add];
 unfold shift384_copy_temps.
 all: unfold Clight2.exec_stmt.
 all: repeat first
 [ lazymatch goal with
   | |- exec_stmt _ _ _ _ _ (Ssequence _ _) _ _ _ _=>
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0)
   | |- exec_stmt _ _ _ _ _ (Sifthenelse _ _ _) _ _ _ _=>
     eapply exec_Sifthenelse;[copy_expr bl word Load|reflexivity|];
     lazymatch goal with |- exec_stmt _ _ _ _ _ (if ?choice then _ else _) _ _ _ _=>
       let known:=eval vm_compute in choice in change choice with known end;
     cbn beta iota zeta
   | |- exec_stmt _ _ _ _ _ (Sset _ _) _ _ _ _=>
     apply exec_Sset;copy_expr bl word Load
   end ].
 all: try change (cast_int_long Signed (Int.repr 0)) with Int64.zero.
 all: try change (if Int.eq Int.zero Int.zero then Int.zero else Int.one) with Int.zero.
 all: try change (Int64.repr (Int.unsigned Int.zero)) with Int64.zero.
 all: rewrite ?Int64.shru_zero,?Int64.or_zero.
 all: eapply exec_Sassign with (loc:=br);
  [first [eapply (eval_shift384_dest _ _ _ br 0)|eapply (eval_shift384_dest _ _ _ br 1)|
    eapply (eval_shift384_dest _ _ _ br 2)|eapply (eval_shift384_dest _ _ _ br 3)];
   [lia|copy_lookup]|copy_expr bl word Load|reflexivity|].
 all: apply assign_loc_value with (chunk:=Mint64);[reflexivity|exact Store].
Qed.
