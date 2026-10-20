(** Unchanged ctx8_add_values proof, renamed from C.jet_sha_add_buffer_spec. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Integers.
Require sha.SHA256 sha.common_lemmas.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Simplicity.Alg Simplicity.SHA256.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_assertion_spec C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha256_count_assertion C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_elements_support_sha_ctx8_bridge.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem nonce_ctx8_add_values (buf : Ty.tySem (buffer_type (Word 3) 5)) (count : Ty.tySem (Word 6))
    (state : Ty.tySem (Word 8)) (vs : list (Ty.tySem (Word 3))) :
  let lbuf := buffer_list (Word 3) 5 buf in
  let regs := state_regs state in
  let total := @toZ (WordToZ 6) count + (Z.of_nat (length lbuf) + Z.of_nat (length vs)) / 64 in
  let result :=
    match vs with
    | [] => if @toZ (WordToZ 6) count <? ctx8_limit then Some (buf, (count, state)) else None
    | _ => ctx8_add_list (buf, (count, state)) vs
    end in
  exists (buf' : Ty.tySem (buffer_type (Word 3) 5)) (h' : Ty.tySem (Word 8)),
    buffer_list (Word 3) 5 buf' = fst (absorb lbuf regs vs) /\
    state_regs h' = snd (absorb lbuf regs vs) /\
    result = if total <? ctx8_limit then Some (buf', (@fromZ (WordToZ 6) total, h')) else None.
Proof.
  intros lbuf regs total result.
  pose proof (buffer_list_length (Word 3) 5 buf) as HL. change (Nat.pow 2 6) with 64%nat in HL. fold lbuf in HL.
  destruct vs as [|v0 vs'].
  - exists buf, state. split; [reflexivity|]. split; [reflexivity|].
    assert (HT : total = @toZ (WordToZ 6) count).
    { unfold total. cbn [length]. rewrite Z.add_0_r, Z.div_small by lia. lia. }
    unfold result. rewrite HT, (@from_toZ (WordToZ 6) count). reflexivity.
  - assert (Hne : v0 :: vs' <> []) by discriminate.
    pose proof (ctx8_add_list_closed (v0 :: vs') buf count state Hne) as HClosed. cbv zeta in HClosed.
    destruct HClosed as [HCa HCb].
    change (exists (buf' : Ty.tySem (buffer_type (Word 3) 5)) (h' : Ty.tySem (Word 8)),
      buffer_list (Word 3) 5 buf' = fst (absorb lbuf regs (v0 :: vs')) /\
      state_regs h' = snd (absorb lbuf regs (v0 :: vs')) /\
      ctx8_add_list (buf, (count, state)) (v0 :: vs') =
        (if total <? ctx8_limit then Some (buf', (@fromZ (WordToZ 6) total, h')) else None)).
    destruct (Z.ltb_spec total ctx8_limit) as [HT|HT].
    + destruct (HCa HT) as (buf' & h' & HS1 & HS2 & HS3). exists buf', h'. auto.
    + destruct (absorb_length (v0 :: vs') lbuf regs HL) as [_ HltA].
      destruct (buffer_exists (Word 3) 5 (fst (absorb lbuf regs (v0 :: vs')))
        ltac:(change (Nat.pow 2 6) with 64%nat; exact HltA)) as [buf' Hb'].
      assert (Hlr : length regs = 8%nat).
      { unfold regs, state_regs. rewrite map_length. apply (jet_word32_chunks.word32_chunks_length 3). }
      assert (HrA : forall vs (lb : list (Ty.tySem (Word 3))) rg, (length lb < 64)%nat -> length rg = 8%nat ->
        length (snd (absorb lb rg vs)) = 8%nat).
      { clear. induction vs as [|x vs IH]; intros lb rg HL Hlr; [exact Hlr|].
        destruct (Nat.eq_dec (length lb) 63) as [E|E].
        - rewrite absorb_cons_full by exact E. apply IH; [cbn; lia|].
          apply sha.common_lemmas.length_hash_block; [exact Hlr|].
          apply jet_elements_support_sha_be32_exec.be_words_length. rewrite map_length, app_length. cbn [length]. lia.
        - rewrite absorb_cons_small by lia. apply IH; [rewrite app_length; cbn [length]; lia|exact Hlr]. }
      destruct (state_exists _ (HrA (v0 :: vs') lbuf regs HL Hlr)) as [h' Hh'].
      exists buf', h'. split; [exact Hb'|]. split; [exact Hh'|]. apply HCb. exact HT.
Qed.
