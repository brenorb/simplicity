(** Context accesses and low-counter overflow update in the frozen secp
    SHA implementation. Reuse the existing checked field layouts and validate
    their expression transport; the global counter read is proved directly. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Memory Values Events.
Require Import C.jet_transport C.jet_sha_linkage C.jet_secp_linkage
  C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_readBit_layout.
Require C.jets_sha C.jets_secp.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma secp_sha_ctx_checked k id : expr_okb sha_ge secp_ge (ctx_field_expr k id)=true.
Proof. destruct k;vm_compute;reflexivity. Qed.
Lemma secp_sha_counter_symbol : Genv.find_symbol secp_ge jets_sha._sha256_max_counter=
  Some (secp_symbol_block jets_secp._sha256_max_counter).
Proof. vm_compute;reflexivity. Qed.
Local Opaque sha_ge secp_ge.

Lemma eval_secp_ctx_field_lvalue k id e le m bc base :
  le!id=Some (Vptr bc (Ptrofs.repr base)) ->
  eval_lvalue secp_ge e le m (ctx_field_expr k id)
    bc (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr (ctx_offset k))) Full.
Proof.
  intro Pointer;eapply (proj2 (eval_expr_transport sha_ge secp_ge e le m));
    [apply eval_ctx_field_lvalue;exact Pointer|apply secp_sha_ctx_checked].
Qed.
Lemma eval_secp_ctx_field k id e le m bc base chunk v :
  0<=base -> base+88<=Ptrofs.max_unsigned -> access_mode (ctx_field_type k)=By_value chunk ->
  le!id=Some (Vptr bc (Ptrofs.repr base)) -> Mem.load chunk m bc (base+ctx_offset k)=Some v ->
  eval_expr secp_ge e le m (ctx_field_expr k id) v.
Proof.
  intros Base Hi Mode Pointer Load;eapply (proj1 (eval_expr_transport sha_ge secp_ge e le m));
    [eapply eval_ctx_field;eassumption|apply secp_sha_ctx_checked].
Qed.
Lemma eval_secp_ctx_block id e le m bc base : le!id=Some (Vptr bc (Ptrofs.repr base)) ->
  eval_expr secp_ge e le m (ctx_field_expr SBlock id)
    (Vptr bc (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 16))).
Proof.
  intro Pointer;eapply (proj1 (eval_expr_transport sha_ge secp_ge e le m));
    [apply eval_ctx_block;exact Pointer|apply secp_sha_ctx_checked].
Qed.
Lemma exec_secp_ctx_assign k id e le m mf bc base chunk a v v' :
  0<=base -> base+88<=Ptrofs.max_unsigned -> access_mode (ctx_field_type k)=By_value chunk ->
  le!id=Some (Vptr bc (Ptrofs.repr base)) -> eval_expr secp_ge e le m a v ->
  sem_cast v (typeof a) (ctx_field_type k) m=Some v' ->
  Mem.store chunk m bc (base+ctx_offset k) v'=Some mf ->
  Clight2.exec_stmt secp_ge e le m (Sassign (ctx_field_expr k id) a) E0 le mf Out_normal.
Proof.
  intros Base Hi Mode Pointer Eval Cast Store.
  eapply exec_Sassign;[apply eval_secp_ctx_field_lvalue;exact Pointer|exact Eval|exact Cast|].
  eapply assign_loc_value;[exact Mode|];unfold Mem.storev;rewrite ctx_address by assumption;exact Store.
Qed.

Lemma secp_sha_bounded_overflow c vn : Int64.unsigned c+Int64.unsigned vn<=64 ->
  Int64.cmpu Cle (Int64.sub sha_max_counter c) vn=false.
Proof.
  intro Small;pose proof (Int64.unsigned_range c) as C;pose proof (Int64.unsigned_range vn) as N.
  rewrite C.jet_sha_uchars_loop.cmpu_le_bool,C.jet_sha_uchars_loop.long_sub_unsigned;
    change (Int64.unsigned sha_max_counter) with 2305843009213693952;[apply Z.leb_gt|];lia.
Qed.

Lemma secp_sha_small_overflow c vn : Int64.unsigned c+Int64.unsigned vn<64 ->
  Int64.cmpu Cle (Int64.sub sha_max_counter c) vn=false.
Proof. intro Small;apply secp_sha_bounded_overflow;lia. Qed.

Lemma exec_secp_sha_bounded_overflow m le bx c vn :
  Int64.unsigned c+Int64.unsigned vn<=64 ->
  le!jets_sha._ctx=Some (Vptr bx Ptrofs.zero) -> le!jets_sha._len=Some (Vlong vn) ->
  Mem.load Mint64 m bx 8=Some (Vlong c) -> Mem.load Mint8unsigned m bx 80=Some (Vint Int.zero) ->
  Mem.load Mint64 m (secp_symbol_block jets_secp._sha256_max_counter) 0=Some (Vlong sha_max_counter) ->
  Mem.valid_access m Mint8unsigned bx 80 Writable ->exists lef mf,
  Clight2.exec_stmt secp_ge empty_env le m uc_ovf E0 lef mf Out_normal /\
  Mem.store Mint8unsigned m bx 80 (Vint Int.zero)=Some mf /\
  (forall id,In id [jets_sha._ctx;jets_sha._arr;jets_sha._len;jets_sha._delta;jets_sha._block] ->lef!id=le!id).
Proof.
  intros Small Ctx Len Counter Overflow Max Access.
  destruct (Mem.valid_access_store m Mint8unsigned bx 80 (Vint Int.zero) Access) as (mf & Store).
  set (le5:=PTree.set jets_sha._t'5 (Vint Int.zero) le).
  set (le6:=PTree.set jets_sha._t'6 (Vlong sha_max_counter) le5).
  set (le7:=PTree.set jets_sha._t'7 (Vlong c) le6).
  set (lef:=PTree.set jets_sha._t'1 (Vint Int.zero) le7).
  exists lef,mf;split.
  - unfold uc_ovf;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lef) (m1:=m).
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le5) (m1:=m).
      * apply exec_Sset;eapply (eval_secp_ctx_field SOverflow) with (chunk:=Mint8unsigned) (base:=0);
          [lia|change (88<=18446744073709551615);lia|reflexivity|exact Ctx|exact Overflow].
      * eapply exec_Sifthenelse with (b:=false);[apply eval_Etempvar;apply PTree.gss|reflexivity|].
        unfold uc_ovf_else;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le6) (m1:=m).
        { apply exec_Sset;eapply eval_Elvalue.
          - apply eval_Evar_global;[reflexivity|exact secp_sha_counter_symbol].
          - eapply deref_loc_value;[reflexivity|exact Max]. }
        eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le7) (m1:=m).
        { apply exec_Sset;eapply (eval_secp_ctx_field SCounter) with (chunk:=Mint64) (base:=0);
            [lia|change (88<=18446744073709551615);lia|reflexivity| |exact Counter].
          unfold le6,le5;rewrite !PTree.gso by discriminate;exact Ctx. }
        apply exec_Sset;eapply eval_Ecast with (v1:=Val.of_bool false);[|reflexivity].
        eapply eval_Ebinop with (v1:=Vlong (Int64.sub sha_max_counter c)) (v2:=Vlong vn).
        -- eapply eval_Ebinop;
             [apply eval_Etempvar;unfold le7;rewrite PTree.gso by discriminate;apply PTree.gss|
              apply eval_Etempvar;apply PTree.gss|reflexivity].
        -- apply eval_Etempvar;unfold le7,le6,le5;rewrite !PTree.gso by discriminate;exact Len.
        -- change (Some (Val.of_bool (Int64.cmpu Cle (Int64.sub sha_max_counter c) vn))=Some (Val.of_bool false)).
           rewrite secp_sha_bounded_overflow by exact Small;reflexivity.
    + eapply (exec_secp_ctx_assign SOverflow) with (chunk:=Mint8unsigned) (base:=0) (v:=Vint Int.zero);
        [lia|change (88<=18446744073709551615);lia|reflexivity| | |reflexivity|exact Store].
      * unfold lef,le7,le6,le5;rewrite !PTree.gso by discriminate;exact Ctx.
      * apply eval_Etempvar;apply PTree.gss.
  - split;[exact Store|];intros id Member.
    unfold lef,le7,le6,le5.
    repeat rewrite PTree.gso by (destruct Member as [<-|[<-|[<-|[<-|[<-|[]]]]]];discriminate).
    reflexivity.
Qed.

Lemma exec_secp_sha_small_overflow m le bx c vn :
  Int64.unsigned c+Int64.unsigned vn<64 ->
  le!jets_sha._ctx=Some (Vptr bx Ptrofs.zero) -> le!jets_sha._len=Some (Vlong vn) ->
  Mem.load Mint64 m bx 8=Some (Vlong c) -> Mem.load Mint8unsigned m bx 80=Some (Vint Int.zero) ->
  Mem.load Mint64 m (secp_symbol_block jets_secp._sha256_max_counter) 0=Some (Vlong sha_max_counter) ->
  Mem.valid_access m Mint8unsigned bx 80 Writable ->exists lef mf,
  Clight2.exec_stmt secp_ge empty_env le m uc_ovf E0 lef mf Out_normal /\
  Mem.store Mint8unsigned m bx 80 (Vint Int.zero)=Some mf /\
  (forall id,In id [jets_sha._ctx;jets_sha._arr;jets_sha._len;jets_sha._delta;jets_sha._block] ->lef!id=le!id).
Proof. intro Small;apply exec_secp_sha_bounded_overflow;lia. Qed.
