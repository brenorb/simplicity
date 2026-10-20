(** Candidate hashBlock port with the literal Arith.add boundary.
    Its semantic equality with the existing C-to-Coq-SHA target is proved
    here. Canonical source correspondence and the public/startup composition
    are separate obligations; this module alone registers no jet. *)
From Coq Require Import ZArith List FunctionalExtensionality.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Simplicity.SHA256.
Require Import C.jet_canonical_add_adapter.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_sha_add32 {term : Alg.Core.Algebra} :
  term (Ty.Prod Word32 Word32) Word32 := @canonical_add_word 5 term >>> I H.

Lemma literal_sha_add32_matches :
  @literal_sha_add32 Alg.CoreFunSem = @SHA256.add32 Alg.CoreFunSem.
Proof.
  apply functional_extensionality; intro a.
  unfold literal_sha_add32, SHA256.add32.
  change (snd (@canonical_add_word 5 Alg.CoreFunSem a) = snd (@Word.adder 5 Alg.CoreFunSem a)).
  rewrite canonical_add_word_matches_adder; reflexivity.
Qed.

Definition sha_block_tree {term : Alg.Core.Algebra}
    (a32 : term (Ty.Prod Word32 Word32) Word32) : term (Ty.Prod Word256 Word512) Word256 :=
let x32 := @SHA256.xor3Word32 term in
let diag := O I H &&& I O H in
let odiag := O diag in
let idiag := I diag in
let bigDiag := O I I H &&& I O O H in
let part1Schedule := odiag &&& bigDiag in
let smallSigma0 := @SHA256.rotate32 (-7) term &&& @SHA256.rotate32 (-18) term &&& @SHA256.shift32 (-3) term >>> x32 in
let smallSigma1 := @SHA256.rotate32 (-17) term &&& @SHA256.rotate32 (-19) term &&& @SHA256.shift32 (-10) term >>> x32 in
let smallSigma := (O O O (O H &&& (I H >>> smallSigma0)) >>> a32)
             &&& (I (O O I H &&& (I I O H >>> smallSigma1)) >>> a32) >>> a32 in
let schedule := (O part1Schedule &&& (O idiag &&& (O I I I H &&& I (O O O H))))
           &&& (I part1Schedule &&& (I idiag &&& (I I I I H &&& smallSigma))) in
let bigSigma0 := @SHA256.rotate32 (-2) term &&& @SHA256.rotate32 (-13) term &&& @SHA256.rotate32 (-22) term >>> x32 in
let bigSigma1 := @SHA256.rotate32 (-6) term &&& @SHA256.rotate32 (-11) term &&& @SHA256.rotate32 (-25) term >>> x32 in
let t1 := (O H &&& I I O O O O H >>> a32) &&& I O (I (I I H &&& ((O O H >>> bigSigma1) &&& (O O H &&& diag >>> @SHA256.chWord32 term) >>> a32)) >>> a32) >>> a32 in
let t12 := O ((O I H &&& I H >>> @SHA256.majWord32 term) &&& (O (O H &&& (I H >>> bigSigma0)) >>> a32)) >>> a32 in
let t1d := O O O H &&& I O O H >>> a32 in
let part1Round := ((t1 &&& I O O O O H) &&& I O odiag)
             &&& I O (bigDiag &&& idiag) in
let part2Round := ((t12 &&& O O I H) &&& O I H)
              &&& ((t1d &&& I O I H) &&& I I H) in
let round := part1Round >>> part2Round in
let step := round &&& I I schedule in
let k0 := 1116352408%Z in
let ks := [1899447441;3049323471;3921009573;
  961987163;1508970993;2453635748;2870763221;
  3624381080;310598401;607225278;1426881987;
  1925078388;2162078206;2614888103;3248222580;
  3835390401;4022224774;264347078;604807628;
  770255983;1249150122;1555081692;1996064986;
  2554220882;2821834349;2952996808;3210313671;
  3336571891;3584528711;113926993;338241895;
  666307205;773529912;1294757372;1396182291;
  1695183700;1986661051;2177026350;2456956037;
  2730485921;2820302411;3259730800;3345764771;
  3516065817;3600352804;4094571909;275423344;
  430227734;506948616;659060556;883997877;
  958139571;1322822218;1537002063;1747873779;
  1955562222;2024104815;2227730452;2361852424;
  2428436474;2756734187;3204031479;3329325298]%Z in
let compression := @SHA256.scribe32 k0 _ term &&& iden >>>
  fold_right (fun k (rec : term (Ty.Prod Word32 (Ty.Prod Word256 Word512)) Word256) =>
    @SHA256.scribe32 k _ term &&& step >>> rec) round ks in
let collate (x : term Word256 Word32) := O x &&& I x >>> a32 in
  O H &&& compression >>>
    ((collate (O O O H) &&& collate (O O I H)) &&&
     (collate (O I O H) &&& collate (O I I H))) &&&
    ((collate (I O O H) &&& collate (I O I H)) &&&
     (collate (I I O H) &&& collate (I I I H))).

Lemma sha_block_tree_existing (term : Alg.Core.Algebra) :
  @sha_block_tree term (@SHA256.add32 term) = @SHA256.hashBlock term.
Proof. reflexivity. Qed.

Definition literal_sha_256_block {term : Alg.Core.Algebra} : term (Ty.Prod Word256 Word512) Word256 :=
  @sha_block_tree term (@literal_sha_add32 term).

Lemma literal_sha_256_block_matches :
  @literal_sha_256_block Alg.CoreFunSem = @SHA256.hashBlock Alg.CoreFunSem.
Proof.
  unfold literal_sha_256_block; rewrite literal_sha_add32_matches.
  apply sha_block_tree_existing.
Qed.
