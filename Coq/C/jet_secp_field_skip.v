(** Original skip_fe, including its real skipBits call, at arbitrary valid
    cursors and output contents. None padding imposes no zero-bit premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_exec C.jet_sx_exec C.jet_sx_mem C.jet_output_layout C.jet_frame_inv
 C.jet_bitcoin_effects C.jet_skipBits_layout C.jet_secp_linkage C.jets_secp.
Require C.jets.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge ge0.

Theorem eval_secp_skip_fe m bd base bw edge cursor :
 write_frame_at m bd base bw edge cursor 256 -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_skip_fe) (Vptr bd (Ptrofs.repr base)::nil) E0 mf Vundef /\
 write_effect m mf bd base bw edge cursor 256 (repeat None 256) /\
 lframe (fun b _=>b<>bd) m mf.
Proof.
 intro Output.
 destruct (eval_skipBits_padding m bd base bw edge cursor 256 Output)
   as (mf & Skip & Cells & Prefix & Fields & Loads & Perms & Valid).
 assert (Member : In (C.jets._skipBits,C.jets.f_skipBits) secp_core_helpers)
   by (unfold secp_core_helpers;repeat (first [left;reflexivity|right])).
 pose proof (secp_transport_call _ _ Member _ _ _ _ _ Skip) as SkipS.
 destruct (secp_core_helpers_entries _ _ Member) as (b0 & bf & HS0 & HF0 & HS & HF).
 exists mf;split.
 - eapply eval_funcall_internal with (e:=empty_env)
     (le1:=PTree.set _dst (Vptr bd (Ptrofs.repr base)) (PTree.empty val))
     (le2:=PTree.set _dst (Vptr bd (Ptrofs.repr base)) (PTree.empty val))
     (m1:=m) (m2:=mf) (out:=Out_normal).
   + constructor.
     * cbn;repeat constructor;cbn;intuition discriminate.
     * cbn;repeat constructor;cbn;intuition discriminate.
     * intros i j HI HJ HE;cbn in HJ;contradiction.
     * constructor.
     * reflexivity.
   + unfold f_skip_fe;cbn [fn_body].
     eapply exec_Scall with (vf:=Vptr bf Ptrofs.zero)
       (vargs:=[Vptr bd (Ptrofs.repr base);Vlong (Int64.repr 256)])
       (f:=Internal C.jets.f_skipBits) (vres:=Vundef).
     * reflexivity.
     * eapply eval_Elvalue.
       -- eapply eval_Evar_global;[reflexivity|exact HS].
       -- apply deref_loc_reference;reflexivity.
     * eapply eval_Econs;[apply eval_Etempvar;apply PTree.gss|reflexivity|].
       eapply eval_Econs;[constructor|reflexivity|constructor].
     * exact HF.
     * reflexivity.
     * exact SkipS.
   + reflexivity.
   + reflexivity.
 - split.
   + split;[exact Cells|];split;[exact Prefix|];split;[exact Fields|].
     split;[intros chunk b ofs HB HW;apply Loads;exact HB|];split;assumption.
   + split.
     * intros chunk b ofs HV HO;apply Loads;left.
       apply (HO ofs ltac:(pose proof (size_chunk_pos chunk);lia)).
     * split;[intros;apply Perms;assumption|exact Valid].
Qed.

Theorem eval_secp_skip_fe_from_prefix m0 bd base bw edge cursor N bi written0 outs0 m :
 write_frame_at m0 bd base bw edge cursor N -> Z.of_nat (length outs0)+256<=N ->
 finv m0 bd base bw edge cursor N bi m written0 outs0 -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_skip_fe) (Vptr bd (Ptrofs.repr base)::nil) E0 mf Vundef /\
 finv m0 bd base bw edge cursor N bi mf true (outs0++repeat None 256) /\
 lframe (fun b _=>b<>bd) m mf.
Proof.
 intros Output Cap Inv.
 pose proof (finv_wframe m0 bd base bw edge cursor N bi Output m written0 outs0 Inv) as Current.
 assert (Space : write_frame_at m bd base bw edge (cursor-Z.of_nat (length outs0)) 256).
 { eapply write_frame_at_le with (count:=N-Z.of_nat (length outs0));[lia|exact Current]. }
 destruct (eval_secp_skip_fe m bd base bw edge (cursor-Z.of_nat (length outs0)) Space)
   as (mf & Call & Effect & Frame).
 exists mf;split;[exact Call|];split;[|exact Frame].
 eapply finv_write with (n2:=256);[exact Output|exact Inv|rewrite repeat_length;reflexivity|exact Cap|exact Effect].
Qed.
