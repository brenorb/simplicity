(** Exact original challenge statements; execution premises are discharged by
    the constructor, hashing and scalar-storage contracts in the lifecycle. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_exec C.jet_secp_linkage C.jet_secp_curve_statements
 C.jet_secp_generator_sha_start C.jet_secp_schnorr_challenge_entry
 C.jet_secp_schnorr_challenge_copy.
Require Import C.jets_secp.
Import ListNotations Ctypes Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition schnorr_challenge_address id ty:=Eaddrof (Evar id ty) (tptr ty).
Definition schnorr_challenge_state:=Efield (Evar _sha_buf schnorr_challenge_state_type) _s (tarray tuint 8).
Definition schnorr_challenge_tag_call:=curve_call _secp256k1_schnorrsig_sha256_tagged
 f_secp256k1_schnorrsig_sha256_tagged None
 [schnorr_challenge_address __res schnorr_challenge_context_type;schnorr_challenge_state].
Definition schnorr_challenge_absorb_call id:=curve_call _sha256_uchars f_sha256_uchars None
 [schnorr_challenge_address _sha schnorr_challenge_context_type;Etempvar id (tptr tuchar);
  if Pos.eqb id _msg then Etempvar _msglen tulong else Econst_int (Int.repr 32) tint].
Definition schnorr_challenge_finalize_call:=curve_call _sha256_finalize f_sha256_finalize None
 [schnorr_challenge_address _sha schnorr_challenge_context_type].
Definition schnorr_challenge_digest_call:=curve_call _sha256_fromMidstate f_sha256_fromMidstate None
 [Evar _buf (tarray tuchar 32);schnorr_challenge_state].
Definition schnorr_challenge_scalar_call:=curve_call _secp256k1_scalar_set_b32 f_secp256k1_scalar_set_b32 None
 [Etempvar _e (tptr (Tstruct __5826 noattr));Evar _buf (tarray tuchar 32);
  Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)].
Lemma schnorr_challenge_body_source:fn_body f_secp256k1_schnorrsig_challenge=
 Ssequence (Ssequence schnorr_challenge_tag_call schnorr_challenge_copy)
 (Ssequence (schnorr_challenge_absorb_call _r32)
 (Ssequence (schnorr_challenge_absorb_call _pubkey32)
 (Ssequence (schnorr_challenge_absorb_call _msg)
 (Ssequence schnorr_challenge_finalize_call
 (Ssequence schnorr_challenge_digest_call schnorr_challenge_scalar_call))))).
Proof. reflexivity. Qed.
Definition schnorr_challenge_functions:=
 [(_secp256k1_schnorrsig_sha256_tagged,f_secp256k1_schnorrsig_sha256_tagged);
 (_sha256_uchars,f_sha256_uchars);(_sha256_finalize,f_sha256_finalize);
 (_sha256_fromMidstate,f_sha256_fromMidstate);(_secp256k1_scalar_set_b32,f_secp256k1_scalar_set_b32)].
Lemma schnorr_challenge_symbols id fd:In (id,fd) schnorr_challenge_functions ->
 Genv.find_symbol secp_ge id=Some (secp_symbol_block id) /\
 Genv.find_funct secp_ge (Vptr (secp_symbol_block id) Ptrofs.zero)=Some (Internal fd).
Proof.
 intro Member;destruct Member as [Pair|[Pair|[Pair|[Pair|[Pair|Impossible]]]]];
 try contradiction;inversion Pair;subst;vm_compute;split;reflexivity.
Qed.
Local Opaque secp_ge.
Lemma eval_schnorr_challenge_state e le m bs:e!_sha_buf=Some (bs,schnorr_challenge_state_type) ->
 eval_expr secp_ge e le m schnorr_challenge_state (Vptr bs Ptrofs.zero).
Proof.
 intro State;destruct generator_sha_state_layout as (co & Cenv & Offset).
 unfold schnorr_challenge_state.
 eapply eval_Elvalue with (loc:=bs) (ofs:=Ptrofs.zero) (bf:=Full).
 - rewrite <-(Ptrofs.add_zero_l Ptrofs.zero);eapply eval_Efield_struct with (co:=co) (delta:=0).
   + eapply eval_Elvalue;[apply eval_Evar_local;exact State|apply deref_loc_copy;reflexivity].
   + reflexivity.
   + exact Cenv.
   + exact Offset.
 - apply deref_loc_reference;reflexivity.
Qed.
Lemma exec_schnorr_challenge_call id fd args vargs v e le m mf:
 In (id,fd) schnorr_challenge_functions ->e!id=None ->
 eval_exprlist secp_ge e le m args (type_of_params (fn_params fd)) vargs ->
 Clight2.eval_funcall secp_ge m (Internal fd) vargs E0 mf v ->
 Clight2.exec_stmt secp_ge e le m (curve_call id fd None args) E0 le mf Out_normal.
Proof.
 intros Member Global Args Call;destruct (schnorr_challenge_symbols id fd Member) as [Symbol Function].
 unfold curve_call;eapply exec_Scall with (vf:=Vptr (secp_symbol_block id) Ptrofs.zero)
 (f:=Internal fd) (vargs:=vargs) (vres:=v).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[exact Global|exact Symbol]|apply deref_loc_reference;reflexivity].
 - exact Args.
 - exact Function.
 - reflexivity.
 - exact Call.
Qed.
Local Ltac schnorr_args:=
 first [apply eval_Enil|eapply eval_Econs;
  [first [apply eval_schnorr_challenge_state;reflexivity|
          apply eval_Eaddrof;apply eval_Evar_local;reflexivity|
          apply eval_Etempvar;reflexivity|
          eapply eval_Elvalue;[apply eval_Evar_local;reflexivity|apply deref_loc_reference;reflexivity]|
          eapply eval_Ecast;[constructor|reflexivity]|constructor]
  |reflexivity|schnorr_args]].
Theorem exec_schnorr_challenge_body m mt mc m1 m2 m3 mh md mf bb bs bc br be ba oa bm om bp op:
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_schnorrsig_sha256_tagged)
  [Vptr br Ptrofs.zero;Vptr bs Ptrofs.zero] E0 mt Vundef ->
 Clight2.exec_stmt secp_ge (schnorr_challenge_env bb bs bc br)
  (schnorr_challenge_temps be ba oa bm om bp op) mt schnorr_challenge_copy E0
  (schnorr_challenge_temps be ba oa bm om bp op) mc Out_normal ->
 Clight2.eval_funcall secp_ge mc (Internal f_sha256_uchars)
  [Vptr bc Ptrofs.zero;Vptr ba oa;Vlong (Int64.repr 32)] E0 m1 (Vint Int.one) ->
 Clight2.eval_funcall secp_ge m1 (Internal f_sha256_uchars)
  [Vptr bc Ptrofs.zero;Vptr bp op;Vlong (Int64.repr 32)] E0 m2 (Vint Int.one) ->
 Clight2.eval_funcall secp_ge m2 (Internal f_sha256_uchars)
  [Vptr bc Ptrofs.zero;Vptr bm om;Vlong (Int64.repr 32)] E0 m3 (Vint Int.one) ->
 Clight2.eval_funcall secp_ge m3 (Internal f_sha256_finalize) [Vptr bc Ptrofs.zero] E0 mh (Vint Int.one) ->
 Clight2.eval_funcall secp_ge mh (Internal f_sha256_fromMidstate)
  [Vptr bb Ptrofs.zero;Vptr bs Ptrofs.zero] E0 md Vundef ->
 Clight2.eval_funcall secp_ge md (Internal f_secp256k1_scalar_set_b32)
  [Vptr be Ptrofs.zero;Vptr bb Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge (schnorr_challenge_env bb bs bc br)
  (schnorr_challenge_temps be ba oa bm om bp op) m (fn_body f_secp256k1_schnorrsig_challenge)
  E0 (schnorr_challenge_temps be ba oa bm om bp op) mf Out_normal.
Proof.
 intros Tag Copy R P M Final Digest Scalar;rewrite schnorr_challenge_body_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mt);[|exact Copy].
   unfold schnorr_challenge_tag_call;eapply exec_schnorr_challenge_call with (v:=Vundef);
    [left;reflexivity|reflexivity|schnorr_args|exact Tag].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1).
   + unfold schnorr_challenge_absorb_call;cbn [Pos.eqb].
     eapply exec_schnorr_challenge_call with (v:=Vint Int.one);
      [right;left;reflexivity|reflexivity|schnorr_args|exact R].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2).
     * unfold schnorr_challenge_absorb_call;cbn [Pos.eqb].
       eapply exec_schnorr_challenge_call with (v:=Vint Int.one);
        [right;left;reflexivity|reflexivity|schnorr_args|exact P].
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3).
       -- unfold schnorr_challenge_absorb_call;cbn [Pos.eqb].
          eapply exec_schnorr_challenge_call with (v:=Vint Int.one);
           [right;left;reflexivity|reflexivity|schnorr_args|exact M].
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mh).
          ++ unfold schnorr_challenge_finalize_call;eapply exec_schnorr_challenge_call with (v:=Vint Int.one);
              [right;right;left;reflexivity|reflexivity|schnorr_args|exact Final].
          ++ eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md).
             ** unfold schnorr_challenge_digest_call;eapply exec_schnorr_challenge_call with (v:=Vundef);
                 [right;right;right;left;reflexivity|reflexivity|schnorr_args|exact Digest].
             ** unfold schnorr_challenge_scalar_call;eapply exec_schnorr_challenge_call with (v:=Vundef);
                 [right;right;right;right;left;reflexivity|reflexivity|schnorr_args|exact Scalar].
Qed.
