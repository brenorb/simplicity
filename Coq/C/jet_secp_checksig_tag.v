(** Standard Simplicity Signature tag: the actual frozen secp global and its
    initialized, preserved representation. This is not yet a public jet proof. *)
From Coq Require Import ZArith List Lia Strings.String.
From compcert Require Import Integers AST Ctypes Clight Memory Globalenvs Values.
Require Import Simplicity.Digest Simplicity.MerkleRoot Simplicity.Word
 C.jet_secp_linkage C.jets_secp C.jet_sx_mem C.jet_clight_forward C.jet_uint32_array_init
 C.jet_secp_schnorr_startup.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition checksig_tag_hash:=MerkleRoot.tag (MerkleRoot.prefix++["Signature"]).
Definition checksig_iv_words:=map Int.repr
 [-303315125;2001476530;-882122114;953564290;1863085798;37330614;1211883153;654973851].
Definition checksig_iv_word:=Word.from_hash256 checksig_tag_hash.
Lemma checksig_iv_registers:checksig_iv_words=Digest.hash256_reg checksig_tag_hash.
Proof.
 assert (Unsigned:map Int.unsigned checksig_iv_words=map Int.unsigned (Digest.hash256_reg checksig_tag_hash))
  by (vm_compute;reflexivity).
 assert (Recover:forall xs:list Int.int,map Int.repr (map Int.unsigned xs)=xs).
 { intro xs;induction xs as [|x xs IH];cbn;[reflexivity|];rewrite Int.repr_unsigned,IH;reflexivity. }
 rewrite <-(Recover checksig_iv_words),<-(Recover (Digest.hash256_reg checksig_tag_hash));rewrite Unsigned;reflexivity.
Qed.
Definition checksig_tag_block:=secp_symbol_block _signatureIV.
Definition checksig_tag_ok m:=uint32_array_at m checksig_tag_block 0 checksig_iv_words /\
 Mem.range_perm m checksig_tag_block 0 32 Cur Readable /\
 (forall pos,~Mem.perm m checksig_tag_block pos Max Writable).
Lemma checksig_tag_info:Genv.find_var_info (Genv.globalenv jets_secp.prog) checksig_tag_block=Some v_signatureIV.
Proof. vm_compute;reflexivity. Qed.
Lemma checksig_tag_symbol:Genv.find_symbol (Clight.genv_genv secp_ge) _signatureIV=Some checksig_tag_block.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge checksig_tag_block.
Theorem checksig_tag_initial m:Genv.init_mem jets_secp.prog=Some m ->checksig_tag_ok m.
Proof.
 intro Init;destruct (Genv.init_mem_characterization jets_secp.prog checksig_tag_block checksig_tag_info Init)
 as (Perm & Bounds & Loads & _).
 change (Mem.range_perm m checksig_tag_block 0 32 Cur Readable) in Perm.
 specialize (Loads eq_refl).
 change (Mem.load Mint32 m checksig_tag_block 0=Some (Vint (Int.repr (-303315125))) /\
  Mem.load Mint32 m checksig_tag_block 4=Some (Vint (Int.repr 2001476530)) /\
  Mem.load Mint32 m checksig_tag_block 8=Some (Vint (Int.repr (-882122114))) /\
  Mem.load Mint32 m checksig_tag_block 12=Some (Vint (Int.repr 953564290)) /\
  Mem.load Mint32 m checksig_tag_block 16=Some (Vint (Int.repr 1863085798)) /\
  Mem.load Mint32 m checksig_tag_block 20=Some (Vint (Int.repr 37330614)) /\
  Mem.load Mint32 m checksig_tag_block 24=Some (Vint (Int.repr 1211883153)) /\
  Mem.load Mint32 m checksig_tag_block 28=Some (Vint (Int.repr 654973851)) /\True) in Loads.
 split.
 - intros i x Nth;destruct i as [|[|[|[|[|[|[|[|i]]]]]]]];
   cbn [checksig_iv_words map nth_error] in Nth;
   try (destruct i;discriminate Nth);injection Nth as Same;subst x;cbn [Z.of_nat Z.mul Z.add];tauto.
 - split;[exact Perm|];intros pos Write;pose proof (proj2 (Bounds pos Max Writable Write)) as Order.
   change (perm_order Readable Writable) in Order;inversion Order.
Qed.
Theorem checksig_tag_framed m mf P:checksig_tag_ok m ->mem_forward m mf ->lframe P m mf ->
 (forall pos,P checksig_tag_block pos) ->checksig_tag_ok mf.
Proof.
 intros (Words & Perm & NoWrite) Forward Frame Outside.
 assert (Valid:Mem.valid_block m checksig_tag_block) by (eapply Mem.perm_valid_block;apply (Perm 0);lia).
 split.
 - intros i x Nth;rewrite (proj1 Frame Mint32 checksig_tag_block (0+4*Z.of_nat i) Valid);
   [exact (Words i x Nth)|intros;apply Outside].
 - split.
   + intros pos Range;apply (proj1 (proj2 Frame));[exact Valid|apply Outside|apply Perm;exact Range].
   + intros pos Write;apply (NoWrite pos);exact (proj2 (Forward _ Valid) pos Writable Write).
Qed.
Definition checksig_startup m:=schnorr_startup m /\checksig_tag_ok m.
Theorem checksig_startup_initial m:Genv.init_mem jets_secp.prog=Some m ->checksig_startup m.
Proof. intro Init;split;[apply schnorr_startup_initial|apply checksig_tag_initial];exact Init. Qed.
Theorem checksig_startup_exists:exists m,Genv.init_mem jets_secp.prog=Some m /\checksig_startup m.
Proof.
 destruct schnorr_startup_exists as (m & Init & _);exists m;split;[exact Init|apply checksig_startup_initial;exact Init].
Qed.
Theorem checksig_startup_framed m mf:checksig_startup m ->mem_forward m mf ->lframe (fun _ _=>True) m mf ->checksig_startup mf.
Proof.
 intros [Schnorr Tag] Forward Frame;split.
 - eapply schnorr_startup_framed;[exact Schnorr|exact Forward|exact Frame].
 - eapply checksig_tag_framed;[exact Tag|exact Forward|exact Frame|intros;exact I].
Qed.
