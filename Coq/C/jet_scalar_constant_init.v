(** Four-limb readonly constants initialized by an arbitrary actual program. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory Globalenvs Ctypes Clight.
Require Import C.jet_secp_scalar_constant C.jet_secp_scalar_get_b32_storage.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Theorem scalar_constant_initializes_at (p:Clight.program) (gv:globvar type) b words m :
 Genv.find_var_info (Genv.globalenv p) b=Some gv ->
 length words=4%nat -> gvar_init gv=map Init_int64 words ->
 gvar_readonly gv=true -> gvar_volatile gv=false ->
 Genv.init_mem p=Some m -> scalar_constant_state b words m.
Proof.
 intros Info Count InitData Readonly Volatile Init.
 destruct (Genv.init_mem_characterization p b Info Init) as (Read & Bounds & Loads & Bytes).
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

