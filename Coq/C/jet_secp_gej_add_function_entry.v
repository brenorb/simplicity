(** Actual eleven-local entry and free-list layout of gej_add_var. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition gej_add_helper_env b22 b12 bu bv bs bt bh bi b2 b3 bk :=
 PTree.set _t (bk,curve_fe_type) (PTree.set _h3 (b3,curve_fe_type)
  (PTree.set _h2 (b2,curve_fe_type) (PTree.set _i (bi,curve_fe_type)
   (PTree.set _h (bh,curve_fe_type) (PTree.set _s2 (bt,curve_fe_type)
    (PTree.set _s1 (bs,curve_fe_type) (PTree.set _u2 (bv,curve_fe_type)
     (PTree.set _u1 (bu,curve_fe_type) (PTree.set _z12 (b12,curve_fe_type)
      (PTree.set _z22 (b22,curve_fe_type) empty_env)))))))))).
Definition gej_add_entry_temps ba bb := PTree.set _rzr (Vlong Int64.zero)
 (PTree.set _b (Vptr bb Ptrofs.zero) (PTree.set _a (Vptr ba Ptrofs.zero)
  (PTree.set _r (Vptr ba Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_gej_add_var))))).
Lemma gej_add_function_ok : fn_okb f_secp256k1_gej_add_var=true.
Proof. reflexivity. Qed.
Lemma gej_add_function_entry m m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 mi ba bb b22 b12 bu bv bs bt bh bi b2 b3 bk :
 Mem.alloc m 0 40=(m1,b22) -> Mem.alloc m1 0 40=(m2,b12) -> Mem.alloc m2 0 40=(m3,bu) ->
 Mem.alloc m3 0 40=(m4,bv) -> Mem.alloc m4 0 40=(m5,bs) -> Mem.alloc m5 0 40=(m6,bt) ->
 Mem.alloc m6 0 40=(m7,bh) -> Mem.alloc m7 0 40=(m8,bi) -> Mem.alloc m8 0 40=(m9,b2) ->
 Mem.alloc m9 0 40=(m10,b3) -> Mem.alloc m10 0 40=(mi,bk) ->
 function_entry2 secp_ge f_secp256k1_gej_add_var
  [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero;Vlong Int64.zero] m
  (gej_add_helper_env b22 b12 bu bv bs bt bh bi b2 b3 bk) (gej_add_entry_temps ba bb) mi.
Proof.
 intros A22 A12 AU AV AS AT AH AI A2 A3 AK.
 destruct (fn_okb_true _ gej_add_function_ok) as (HN1 & HN2 & HD).
 constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
 eapply alloc_variables_cons with (m1:=m1) (b1:=b22);[exact A22|].
 eapply alloc_variables_cons with (m1:=m2) (b1:=b12);[exact A12|].
 eapply alloc_variables_cons with (m1:=m3) (b1:=bu);[exact AU|].
 eapply alloc_variables_cons with (m1:=m4) (b1:=bv);[exact AV|].
 eapply alloc_variables_cons with (m1:=m5) (b1:=bs);[exact AS|].
 eapply alloc_variables_cons with (m1:=m6) (b1:=bt);[exact AT|].
 eapply alloc_variables_cons with (m1:=m7) (b1:=bh);[exact AH|].
 eapply alloc_variables_cons with (m1:=m8) (b1:=bi);[exact AI|].
 eapply alloc_variables_cons with (m1:=m9) (b1:=b2);[exact A2|].
 eapply alloc_variables_cons with (m1:=m10) (b1:=b3);[exact A3|].
 eapply alloc_variables_cons with (m1:=mi) (b1:=bk);[exact AK|constructor].
Qed.
Lemma gej_add_function_blocks b22 b12 bu bv bs bt bh bi b2 b3 bk :
 blocks_of_env secp_ge (gej_add_helper_env b22 b12 bu bv bs bt bh bi b2 b3 bk)=
 [(bt,0,40);(bs,0,40);(bi,0,40);(bv,0,40);(bu,0,40);(b2,0,40);(bh,0,40);(b3,0,40);(bk,0,40);(b22,0,40);(b12,0,40)].
Proof. reflexivity. Qed.
