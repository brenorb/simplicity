(** Fix the result of a model-guaranteed witness using deterministic memory
    stores. These lemmas retain the existing external-library premises; they
    make no claim about arbitrary executions of abstract external functions. *)
From Coq Require Import ZArith List Strings.String.
From compcert Require Import Integers AST Values Memory Events Globalenvs.
Require Import C.jet_memcpy_model C.jet_memset_model.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Set Default Timeout 10.
Lemma memcpy_model_at_storebytes (ge:Senv.t) m bd od bs os n bytes mf:
 memcpy_model ->Mem.valid_block m bs ->Mem.valid_block m bd ->
 Mem.loadbytes m bs (Ptrofs.unsigned os) n=Some bytes ->
 Mem.range_perm m bd (Ptrofs.unsigned od) (Ptrofs.unsigned od+n) Cur Writable ->
 (bs<>bd \/ Ptrofs.unsigned os+n<=Ptrofs.unsigned od \/ Ptrofs.unsigned od+n<=Ptrofs.unsigned os) ->
 (0<n<=Int64.max_unsigned /\n<=64) ->
 Ptrofs.unsigned os+n<=Ptrofs.max_unsigned+1 ->Ptrofs.unsigned od+n<=Ptrofs.max_unsigned+1 ->
 Mem.storebytes m bd (Ptrofs.unsigned od) bytes=Some mf ->
 external_call (EF_external "memcpy" memcpy_sig) ge
 [Vptr bd od;Vptr bs os;Vlong (Int64.repr n)] m E0 (Vptr bd od) mf.
Proof.
 intros Model Source Destination Bytes Writable Separate Size SourceEnd DestinationEnd Store.
 destruct (Model ge m bd od bs os n bytes Source Destination Bytes Writable Separate Size SourceEnd DestinationEnd)
 as (out & Effect & Call).
 rewrite Store in Effect;injection Effect as Same;subst out;exact Call.
Qed.
Lemma memset_model_for_at_storebytes sem (ge:Senv.t) m bd od c n mf:
 memset_model_for sem ->Mem.valid_block m bd ->
 Mem.range_perm m bd (Ptrofs.unsigned od) (Ptrofs.unsigned od+n) Cur Writable ->
 0<n<=1024 ->Mem.storebytes m bd (Ptrofs.unsigned od) (memset_bytes c n)=Some mf ->
 sem ge [Vptr bd od;Vint c;Vlong (Int64.repr n)] m E0 (Vptr bd od) mf.
Proof.
 intros Model Destination Writable Size Store.
 destruct (Model ge m bd od c n Destination Writable Size) as (out & Effect & Call).
 rewrite Store in Effect;injection Effect as Same;subst out;exact Call.
Qed.
Lemma memset_model_at_storebytes (ge:Senv.t) m bd od c n mf:
 memset_model ->Mem.valid_block m bd ->
 Mem.range_perm m bd (Ptrofs.unsigned od) (Ptrofs.unsigned od+n) Cur Writable ->
 0<n<=1024 ->Mem.storebytes m bd (Ptrofs.unsigned od) (memset_bytes c n)=Some mf ->
 external_call (EF_external "memset" memset_sig) ge
 [Vptr bd od;Vint c;Vlong (Int64.repr n)] m E0 (Vptr bd od) mf.
Proof. exact (memset_model_for_at_storebytes _ ge m bd od c n mf). Qed.
