(** C skip branch versus one exact literal step; not a public jet theorem. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_control C.jet_secp_wnaf_digit
  C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric C.jet_secp_linkage C.jets_secp.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma wnaf_skip_residual n bit carry :
  0<=bit -> (n/2^bit) mod 2=carry ->
  ((n/2^bit)+carry)/2=n/2^(bit+1)+carry.
Proof.
  intros Bit Low.
  assert (Div : n/2^(bit+1)=(n/2^bit)/2).
  { rewrite Z.pow_add_r by lia.
    change (n/(2^bit*2)=n/2^bit/2).
    rewrite Z.div_div by (try apply Z.pow_pos_nonneg;lia).
    reflexivity. }
  rewrite Div.
  pose proof (Z.div_mod (n/2^bit) 2 ltac:(lia)) as Split.
  rewrite Low in Split.
  symmetry;apply Z.div_unique with (r:=0);lia.
Qed.

Theorem exec_wnaf_literal_skip le m bs n bit carry (word : Ty.tySem (Word 7)) :
  0<=n<2^256 -> 0<=bit<256 -> (carry=0 \/ carry=1) ->
  (n/2^bit) mod 2=carry ->
  @toZ (WordToZ 7) word=n/2^bit+carry ->
  le!_bit=Some (Vint (Int.repr bit)) -> le!_carry=Some (Vint (Int.repr carry)) ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) ->
  exists next : Ty.tySem (Word 7),
    @literal_wnaf15_step Alg.CoreFunSem (Bit.zero,word)=((Bit.zero,next),inl tt) /\
    @toZ (WordToZ 7) next=n/2^(bit+1)+carry /\
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_dispatch E0
      (PTree.set _bit (Vint (Int.repr (bit+1)))
        (PTree.set _t'2 (Vint (Int.repr carry)) le)) m Out_continue.
Proof.
  intros N HBit Carry Low HWord HB HC Storage.
  assert (Even : Z.testbit (@toZ (WordToZ 7) word) 0=Datatypes.false).
  { pose proof (Z.div_mod (n/2^bit) 2 ltac:(lia)) as Split.
    rewrite Low in Split.
    replace (@toZ (WordToZ 7) word) with (2*(n/2^bit/2+carry)) by lia.
    apply Z.testbit_even_0. }
  exists (@literal_wnaf_shift128 Alg.CoreFunSem (Bit.zero,word)).
  split;[apply literal_wnaf15_even_numeric;exact Even|].
  split.
  - rewrite literal_wnaf_shift128_value.
    change ((0*2^128+@toZ (WordToZ 7) word)/2=n/2^(bit+1)+carry).
    rewrite HWord;change ((n/2^bit+carry)/2=n/2^(bit+1)+carry).
    apply wnaf_skip_residual;lia || assumption.
  - apply exec_wnaf_dispatch_skip with (n:=n);assumption.
Qed.
