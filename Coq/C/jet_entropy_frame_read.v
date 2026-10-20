(** Entire 544-bit input prefix from the original encoded product input. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_read32_input_word_total C.jet_uint32_array_init C.jet_elements_support_sha_block_local.
Require Import C.jet_elements_support_sha_compress_call.
Require Import C.jets_elements C.jet_elements_linkage.
Require Import C.jet_entropy_frame_read_txid C.jet_entropy_frame_read_tail.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition entropy_input_type := Ty.Prod (Ty.Prod Word256 Word32) Word256.

Theorem entropy_read_prefix m bs sbase bi edge rc
    (h : Ty.tySem Word256) (ix : Ty.tySem Word32) (con : Ty.tySem Word256) :
  frame_base_valid sbase -> (8 | sbase) ->
  frame_fields_at m bs sbase bi edge rc ->
  0 <= rc -> rc + 544 <= Int64.max_unsigned ->
  frame_input_cells_at m bi edge rc (@encode entropy_input_type ((h, ix), con)) ->
  exists m1 m2 m3 m4 m5 bl bo bc br bt bytes mcp mtx mi ms mr,
    Mem.alloc m 0 16 = (m1, bl) /\
    Mem.alloc m1 0 40 = (m2, bo) /\
    Mem.alloc m2 0 32 = (m3, bc) /\
    Mem.alloc m3 0 32 = (m4, br) /\
    Mem.alloc m4 0 32 = (m5, bt) /\
    Mem.loadbytes m5 bs sbase 16 = Some bytes /\
    Mem.storebytes m5 bl 0 bytes = Some mcp /\
    Clight2.eval_funcall elements_ge mcp (Internal f_read32s)
      [Vptr bo Ptrofs.zero; Vlong (Int64.repr 8); Vptr bl Ptrofs.zero] E0 mtx Vundef /\
    Clight2.eval_funcall elements_ge mtx (Internal f_simplicity_read32)
      [Vptr bl Ptrofs.zero] E0 mi (Vlong (Int64.repr (@toZ (WordToZ 5) ix))) /\
    Mem.store Mint64 mi bo 32 (Vlong (Int64.repr (@toZ (WordToZ 5) ix))) = Some ms /\
    Clight2.eval_funcall elements_ge ms (Internal f_read32s)
      [Vptr bc Ptrofs.zero; Vlong (Int64.repr 8); Vptr bl Ptrofs.zero] E0 mr Vundef /\
    uint32_array_at mr bo 0 (hash256_reg (to_hash256 h)) /\
    Mem.load Mint64 mr bo 32 = Some (Vlong (Int64.repr (@toZ (WordToZ 5) ix))) /\
    uint32_array_at mr bc 0 (hash256_reg (to_hash256 con)) /\
    frame_fields_at mr bl 0 bi edge (rc + 544) /\
    mext m mr /\
    (forall b, Mem.valid_block m b -> ~ In b [bl; bo; bc; br; bt]) /\
    NoDup [bl; bo; bc; br; bt] /\
    Forall2 (fun b z => Mem.range_perm mr b 0 z Cur Freeable /\ Mem.valid_block mr b)
      [bl; bo; bc; br; bt] [16; 40; 32; 32; 32].
Proof.
  intros HB HA HF H0 HM HI.
  change (frame_input_cells_at m bi edge rc ((encode h ++ encode ix) ++ encode con)) in HI.
  rewrite <- app_assoc in HI. apply frame_input_cells_at_app in HI.
  destruct HI as [HTX HI]. rewrite (encode_word_length 8 h) in HI.
  change (frame_input_cells_at m bi edge (rc + 256) (encode ix ++ encode con)) in HI.
  apply frame_input_cells_at_app in HI. destruct HI as [HIX HCON].
  rewrite (encode_word_length 5 ix) in HCON.
  change (frame_input_cells_at m bi edge (rc + 256 + 32) (encode con)) in HCON.
  apply frame_input_word_at_encode in HIX.
  destruct (read32_input_loads m bi edge (rc + 256) ix ltac:(lia) HIX)
    as (_ & high & low & HLoad & HLow).
  assert (Vi : Mem.valid_block m bi) by (eapply load_valid_block; exact HLoad).
  destruct (entropy_txid_prefix m bs sbase bi edge rc h HB HA HF H0 ltac:(lia) HTX)
    as (m1 & m2 & m3 & m4 & m5 & bl & bo & bc & br & bt & bytes & mcp & mtx &
        A1 & A2 & A3 & A4 & A5 & B0 & S0 & CTX & ArrTX & Fields & X & Fresh & ND & Owned).
  destruct X as (VX & KX & PX & AX).
  assert (IX : frame_input_word_at mtx bi edge (rc + 256) ix).
  { eapply frame_input_bits_at_preserved; [|exact HIX].
    intros ofs w HL. rewrite KX by exact Vi. exact HL. }
  assert (CON : frame_input_cells_at mtx bi edge (rc + 256 + 32) (encode con)).
  { apply frame_input_word_at_encode. apply frame_input_word_at_encode in HCON.
    eapply frame_input_bits_at_preserved; [|exact HCON].
    intros ofs w HL. rewrite KX by exact Vi. exact HL. }
  pose proof Owned as Own. repeat rewrite Forall2_cons_iff in Own.
  destruct Own as [[PL VL] [[PO VO] [[PC VC] [[PR VR] [[PT VT] _]]]]].
  assert (Fl : forall b, Mem.valid_block m b -> b <> bl).
  { intros b V E; subst b. apply (Fresh bl V). left; reflexivity. }
  assert (Fo : forall b, Mem.valid_block m b -> b <> bo).
  { intros b V E; subst b. apply (Fresh bo V). right; left; reflexivity. }
  assert (Fc : forall b, Mem.valid_block m b -> b <> bc).
  { intros b V E; subst b. apply (Fresh bc V). right; right; left; reflexivity. }
  assert (D : bl <> bo /\ bl <> bc /\ bo <> bc).
  { inversion ND as [|? ? NL NRest]. inversion NRest as [|? ? NO NRest2].
    repeat split; intro E; subst; [apply NL; left; reflexivity|
      apply NL; right; left; reflexivity|apply NO; left; reflexivity]. }
  destruct D as [Hlo [Hlc Hoc]].
  destruct (entropy_read_tail mtx bl bo bc bi edge (rc + 256) h ix con
    ltac:(lia) ltac:(lia) Fields ltac:(intro E; apply (Fl bi Vi); congruence)
    ltac:(intro E; apply (Fo bi Vi); congruence) ltac:(intro E; apply (Fc bi Vi); congruence)
    Hlo Hlc Hoc PL PO PC ArrTX IX CON)
    as (mi & ms & mr & CI & SI & CC & HT & HX & HC & HFields & K & P & V).
  replace (rc + 256 + 288) with (rc + 544) in HFields by lia.
  assert (Kr : forall ch b ofs, Mem.valid_block m b -> Mem.load ch mr b ofs = Mem.load ch m b ofs).
  { intros ch b ofs HV. rewrite K by (first [apply Fl|apply Fo|apply Fc]; exact HV).
    apply KX; exact HV. }
  assert (Pr : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mr b ofs k p).
  { intros; apply P, PX; assumption. }
  assert (Vr : forall b, Mem.valid_block m b -> Mem.valid_block mr b).
  { intros; apply V, VX; assumption. }
  assert (XR : mext m mr).
  { split; [exact Vr|]. split; [exact Kr|]. split; [exact Pr|].
    intros ch b ofs p [HP HA']. split; [intros ofs' Ho; apply Pr, HP; exact Ho|exact HA']. }
  exists m1, m2, m3, m4, m5, bl, bo, bc, br, bt, bytes, mcp, mtx, mi, ms, mr.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [exact B0|]. split; [exact S0|]. split; [exact CTX|]. split; [exact CI|].
  split; [exact SI|]. split; [exact CC|]. split; [exact HT|]. split; [exact HX|].
  split; [exact HC|]. split; [exact HFields|]. split; [exact XR|]. split; [exact Fresh|]. split; [exact ND|].
  eapply entropy_owned_preserved; [exact P|exact V|exact Owned].
Qed.
