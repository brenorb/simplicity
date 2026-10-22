(** Exact production fe_inv_var entry and statement composition. Execution of
    each called helper is discharged by the numeric/storage layer, not assumed
    by a public jet contract. The modular-inverse call remains to be proved. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_secp_fns C.jet_secp_linkage C.jets_secp
 C.jet_secp_curve_statements C.jet_secp_modinfo_fe_global.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge modinfo_fe_block.

Definition fe_inv_env bt bs := PTree.set _s (bs,Tstruct _secp256k1_modinv64_signed62 noattr)
 (PTree.set _tmp (bt,curve_fe_type) empty_env).
Definition fe_inv_tmp_address := Eaddrof (Evar _tmp curve_fe_type) (tptr curve_fe_type).
Definition fe_inv_s_address := Eaddrof (Evar _s (Tstruct _secp256k1_modinv64_signed62 noattr))
 (tptr (Tstruct _secp256k1_modinv64_signed62 noattr)).
Definition fe_inv_copy := Sassign (Evar _tmp curve_fe_type)
 (Ederef (Etempvar _x (tptr curve_fe_type)) curve_fe_type).
Definition fe_inv_normalize := curve_call _secp256k1_fe_normalize_var f_secp256k1_fe_normalize_var
 None [fe_inv_tmp_address].
Definition fe_inv_pack := curve_call _secp256k1_fe_to_signed62 f_secp256k1_fe_to_signed62
 None [fe_inv_s_address;fe_inv_tmp_address].
Definition fe_inv_inverse := curve_call _secp256k1_modinv64_var f_secp256k1_modinv64_var
 None [fe_inv_s_address;
  Eaddrof (Evar _secp256k1_const_modinfo_fe (Tstruct _secp256k1_modinv64_modinfo noattr))
   (tptr (Tstruct _secp256k1_modinv64_modinfo noattr))].
Definition fe_inv_unpack := curve_call _secp256k1_fe_from_signed62 f_secp256k1_fe_from_signed62
 None [Etempvar _r (tptr curve_fe_type);fe_inv_s_address].
Definition fe_inv_body := Ssequence fe_inv_copy (Ssequence fe_inv_normalize
 (Ssequence fe_inv_pack (Ssequence fe_inv_inverse fe_inv_unpack))).

Lemma fe_inv_body_source : fn_body f_secp256k1_fe_inv_var=fe_inv_body.
Proof. reflexivity. Qed.

Local Ltac helper_member := unfold secp_pure;repeat (first [left;reflexivity|right]).
Local Ltac inv_args HR := first [apply eval_Enil |
 eapply eval_Econs;
 [first [apply eval_Eaddrof;apply eval_Evar_local;reflexivity |
         apply eval_Eaddrof;apply eval_Evar_global;[reflexivity|exact modinfo_fe_global_symbol] |
         apply eval_Etempvar;exact HR] |
  reflexivity | inv_args HR]].

Theorem exec_fe_inv_body_from_calls le m mc mn mp mi mf bt bs bd :
 le!_r=Some (Vptr bd Ptrofs.zero) ->
 Clight2.exec_stmt secp_ge (fe_inv_env bt bs) le m fe_inv_copy E0 le mc Out_normal ->
 Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_fe_normalize_var)
  [Vptr bt Ptrofs.zero] E0 mn Vundef ->
 Clight2.eval_funcall secp_ge mn (Internal f_secp256k1_fe_to_signed62)
  [Vptr bs Ptrofs.zero;Vptr bt Ptrofs.zero] E0 mp Vundef ->
 Clight2.eval_funcall secp_ge mp (Internal f_secp256k1_modinv64_var)
  [Vptr bs Ptrofs.zero;Vptr modinfo_fe_block Ptrofs.zero] E0 mi Vundef ->
 Clight2.eval_funcall secp_ge mi (Internal f_secp256k1_fe_from_signed62)
  [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (fe_inv_env bt bs) le m (fn_body f_secp256k1_fe_inv_var)
  E0 le mf Out_normal.
Proof.
 intros HR Copy Norm Pack Inverse Unpack;rewrite fe_inv_body_source;unfold fe_inv_body.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=le);[exact Copy|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mn) (le1:=le).
 - unfold fe_inv_normalize;eapply exec_curve_call with (vargs:=[Vptr bt Ptrofs.zero]) (v:=Vundef).
   + helper_member.
   + reflexivity.
   + unfold fe_inv_tmp_address;inv_args HR.
   + exact Norm.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mp) (le1:=le).
   + unfold fe_inv_pack;eapply exec_curve_call with
      (vargs:=[Vptr bs Ptrofs.zero;Vptr bt Ptrofs.zero]) (v:=Vundef).
     * helper_member.
     * reflexivity.
     * unfold fe_inv_s_address,fe_inv_tmp_address;inv_args HR.
     * exact Pack.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=le).
     * unfold fe_inv_inverse;eapply exec_curve_call with
        (vargs:=[Vptr bs Ptrofs.zero;Vptr modinfo_fe_block Ptrofs.zero]) (v:=Vundef).
       -- helper_member.
       -- reflexivity.
       -- unfold fe_inv_s_address;inv_args HR.
       -- exact Inverse.
     * unfold fe_inv_unpack;eapply exec_curve_call with
        (vargs:=[Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero]) (v:=Vundef).
       -- helper_member.
       -- reflexivity.
       -- unfold fe_inv_s_address;inv_args HR.
       -- exact Unpack.
Qed.

Definition fe_inv_entry_temps bd bx := PTree.set _x (Vptr bx Ptrofs.zero)
 (PTree.set _r (Vptr bd Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_fe_inv_var))).

Lemma fe_inv_entry m mt mi bt bs bd bx :
 Mem.alloc m 0 40=(mt,bt) -> Mem.alloc mt 0 40=(mi,bs) ->
 function_entry2 secp_ge f_secp256k1_fe_inv_var [Vptr bd Ptrofs.zero;Vptr bx Ptrofs.zero] m
  (fe_inv_env bt bs) (fe_inv_entry_temps bd bx) mi.
Proof.
 intros AT AS;assert (Ok : fn_okb f_secp256k1_fe_inv_var=true) by reflexivity.
 destruct (fn_okb_true _ Ok) as (HN1 & HN2 & HD).
 constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
 eapply alloc_variables_cons with (m1:=mt) (b1:=bt);[exact AT|].
 eapply alloc_variables_cons with (m1:=mi) (b1:=bs);[exact AS|constructor].
Qed.
