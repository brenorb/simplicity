(** Shared actual-initializer and preservation contract for readonly
    four-limb scalar globals. No constant value or initial load is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory Globalenvs Ctypes Clight.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_scalar_lambda_global C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_add_reader_support C.jet_sx_mem C.jet_clight_forward C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition scalar_constant_state b words m := scalar_at m b 0 words /\
 forall ofs,~Mem.perm m b ofs Max Writable.

Theorem scalar_constant_initializes (gv:globvar type) b words m :
 Genv.find_var_info (Clight.genv_genv secp_ge) b=Some gv ->
 length words=4%nat -> gvar_init gv=map Init_int64 words ->
 gvar_readonly gv=true -> gvar_volatile gv=false ->
 Genv.init_mem jets_secp.prog=Some m -> scalar_constant_state b words m.
Proof.
 intros Info Count InitData Readonly Volatile Init.
 rewrite scalar_lambda_genv_projection in Info.
 destruct (Genv.init_mem_characterization jets_secp.prog b Info Init) as (Read & Bounds & Loads & Bytes).
 unfold Genv.perm_globvar in Read,Bounds;rewrite Readonly,Volatile in Read,Bounds.
 destruct words as [|w0 [|w1 [|w2 [|w3 words]]]];try discriminate Count;destruct words;[|discriminate Count].
 rewrite InitData in Read,Bounds,Loads.
 change (Mem.range_perm m b 0 32 Cur Readable) in Read.
 specialize (Loads Volatile).
 change (Mem.load Mint64 m b 0=Some (Vlong w0) /\ Mem.load Mint64 m b 8=Some (Vlong w1) /\
  Mem.load Mint64 m b 16=Some (Vlong w2) /\ Mem.load Mint64 m b 24=Some (Vlong w3) /\ True) in Loads.
 split.
 - unfold scalar_at;split;[reflexivity|];split;[lia|];split;[exists 0;lia|];split;
   [change (32<=18446744073709551615);lia|];split;[exact Read|].
   intros i word Nth;destruct i as [|[|[|[|i]]]];try (destruct i;discriminate);
   injection Nth as <-;cbn [Z.of_nat Z.mul];tauto.
 - intros ofs Write;destruct (Bounds ofs Max Writable Write) as (_ & Order);inversion Order.
Qed.

Lemma scalar_constant_valid b words m : scalar_constant_state b words m -> Mem.valid_block m b.
Proof. intros [(Count & Base & Align & Fits & Read & Loads) _];eapply Mem.perm_valid_block;apply (Read 0);lia. Qed.

Theorem scalar_constant_readonly b words m mf : scalar_constant_state b words m ->
 readonly_preserved m mf -> scalar_constant_state b words mf.
Proof.
 intros State [Forward Unchanged];pose proof (scalar_constant_valid b words m State) as Valid.
 destruct State as [Stored NoWrite].
 assert (Frame:lframe (fun b' _=>b'=b) m mf).
 { apply lframe_unchanged;eapply Mem.unchanged_on_implies;[exact Unchanged|].
   intros b' ofs Eq Valid';subst b';split;[exact Valid|apply NoWrite]. }
 split.
 - eapply scalar_at_lframe;[exact Stored|exact Frame|intros;reflexivity].
 - intros ofs Write;apply (NoWrite ofs);exact (proj2 (Forward b Valid) ofs Writable Write).
Qed.

Lemma scalar_constant_separate b words m bx : scalar_constant_state b words m ->
 Mem.range_perm m bx 0 32 Cur Freeable -> bx<>b.
Proof.
 intros [_ NoWrite] Owned Eq;apply (NoWrite 0);rewrite <-Eq;apply Mem.perm_cur_max.
 eapply Mem.perm_implies;[apply (Owned 0);lia|constructor].
Qed.
