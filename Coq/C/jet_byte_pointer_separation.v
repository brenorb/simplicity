(** A readable concrete byte excludes a pointer fragment at the same address.
    Mptr is Mint64 in the project's frozen LP64 target. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Memory Memdata Values.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma decode_leading_byte_not_pointer byte rest bp op:
 decode_val Mptr (Byte byte::rest)<>Vptr bp op.
Proof.
 change (decode_val Mint64 (Byte byte::rest)<>Vptr bp op).
 unfold decode_val;cbn [proj_bytes proj_value].
 destruct (proj_bytes rest);discriminate.
Qed.
Lemma decode_uint8_byte_head cell rest n:
 decode_val Mint8unsigned (cell::rest)=Vint n ->exists byte,cell=Byte byte.
Proof.
 destruct cell;cbn [decode_val proj_bytes];intro H;try discriminate.
 eexists;reflexivity.
Qed.
Local Opaque decode_val.
Theorem readable_byte_not_pointer m b ofs n bp op:
 Mem.load Mint8unsigned m b ofs=Some (Vint n) ->Mem.load Mptr m b ofs<>Some (Vptr bp op).
Proof.
 intros ByteLoad PtrLoad.
 pose proof (Mem.load_result _ _ _ _ _ ByteLoad) as BD.
 pose proof (Mem.load_result _ _ _ _ _ PtrLoad) as PD.
 change (Vint n=decode_val Mint8unsigned [Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents m))]) in BD.
 change (Vptr bp op=decode_val Mptr (Mem.getN 8 ofs (Maps.PMap.get b (Mem.mem_contents m)))) in PD.
 cbv [Mem.getN] in PD.
 lazymatch type of BD with Vint ?x=decode_val Mint8unsigned (?cell::?rest)=>
 destruct (decode_uint8_byte_head cell rest x (eq_sym BD)) as [byte Cell];rewrite Cell in PD end.
 eapply decode_leading_byte_not_pointer;symmetry;exact PD.
Qed.
