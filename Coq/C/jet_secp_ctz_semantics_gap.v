(** Diagnostic evidence for fixed production secp external dependencies.
    These statements do not prove ctz correctness or any public jet. *)
From Coq Require Import String List PArith ZArith.
From compcert Require Import AST Builtins Events Ctypes Clight Clightdefs Integers Values.
Require Import C.jets_secp C.jet_secp_linkage.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition ctz64_signature := mksignature [AST.Tlong] AST.Tint cc_default.

Lemma production_ctzl_unknown :
 lookup_builtin_function "__builtin_ctzl" ctz64_signature=None.
Proof. reflexivity. Qed.

Lemma production_ctzll_unknown :
 lookup_builtin_function "__builtin_ctzll" ctz64_signature=None.
Proof. reflexivity. Qed.

Lemma production_ctzl_is_abstract_external :
 builtin_or_external_sem "__builtin_ctzl" ctz64_signature=
 external_functions_sem "__builtin_ctzl" ctz64_signature.
Proof. unfold builtin_or_external_sem;rewrite production_ctzl_unknown;reflexivity. Qed.

Definition production_ctz_first_callee :=
 match fn_body f_secp256k1_ctz64_var with
 | Ssequence _ (Ssequence (Sifthenelse _ (Ssequence (Scall _ (Evar callee _) _) _) _) _) => Some callee
 | _ => None
 end.

Lemma production_ctz_calls_ctzl : production_ctz_first_callee=Some ___builtin_ctzl.
Proof. reflexivity. Qed.

Definition production_ctz_guard :=
 match fn_body f_secp256k1_ctz64_var with
 | Ssequence _ (Ssequence (Sifthenelse guard _ _) _) => guard
 | _ => Econst_int Int.zero tint
 end.

Lemma production_ctz_guard_true e le m :
 eval_expr secp_ge e le m production_ctz_guard (Vint Int.one).
Proof.
 unfold production_ctz_guard.
 eapply eval_Ebinop with (v1:=Vlong (Int64.repr (-1))) (v2:=Vlong (Int64.repr (-1))).
 - eapply eval_Ecast;[constructor|reflexivity].
 - constructor.
 - reflexivity.
Qed.

Lemma production_ctzl_declared :
 List.find (fun entry=>Pos.eqb (fst entry) ___builtin_ctzl) (prog_defs prog)=
 Some (___builtin_ctzl,Gfun (External (EF_builtin "__builtin_ctzl" ctz64_signature)
   (Tcons tulong Tnil) tint cc_default)).
Proof. reflexivity. Qed.

(** CompCert's generic external-call properties do not give a totality or a
    counting contract. This countermodel does not assign the actual abstract
    constant: it shows why those properties alone cannot fill the gap. *)
Definition ctz_empty_external : extcall_sem := fun _ _ _ _ _ _=>False.

Lemma ctz_empty_external_valid sg : extcall_properties ctz_empty_external sg.
Proof. constructor;unfold ctz_empty_external;intros;contradiction. Qed.

Theorem ctz_generic_properties_insufficient ge m :
 ~ (forall sem,extcall_properties sem ctz64_signature ->
    exists t result mf,sem ge [Vlong Int64.one] m t result mf).
Proof.
 intro Total;destruct (Total ctz_empty_external (ctz_empty_external_valid ctz64_signature))
  as (t & result & mf & Impossible);exact Impossible.
Qed.

Definition secp_memset_signature := mksignature [AST.Tlong;AST.Tint;AST.Tlong] AST.Tlong cc_default.
Lemma production_memset_declared :
 List.find (fun entry=>Pos.eqb (fst entry) _memset) (prog_defs prog)=
 Some (_memset,Gfun (External (EF_external "memset" secp_memset_signature)
   (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid) cc_default)).
Proof. reflexivity. Qed.

Fixpoint secp_statement_callees s : list ident :=
 match s with
 | Scall _ (Evar id _) _ => [id]
 | Ssequence a b | Sifthenelse _ a b | Sloop a b =>
     secp_statement_callees a++secp_statement_callees b
 | _ => []
 end.
Lemma production_wnaf_calls_memset :
 In _memset (secp_statement_callees (fn_body f_secp256k1_ecmult_wnaf)).
Proof. vm_compute;tauto. Qed.

