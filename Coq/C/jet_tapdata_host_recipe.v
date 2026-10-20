(** The fixed TapData constant recipe from Digest.hs and the vendored
    Digest/Pure/SHA.hs. Word32 operations use CompCert's unsigned word model.
    This is a port of the two complete blocks used by this constant, not a
    claimed interpreter/correctness theorem for arbitrary Haskell decoders. *)
From Coq Require Import ZArith List Strings.String.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Word Simplicity.Digest.
Require Import C.jet_sha_tapdata_spec C.jet_sha_finalize_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition tap_host_state := (((Int.int * Int.int) * (Int.int * Int.int)) *
                             ((Int.int * Int.int) * (Int.int * Int.int)))%type.
Definition tap_host_iv : tap_host_state :=
  (((Int.repr 0x6a09e667, Int.repr 0xbb67ae85), (Int.repr 0x3c6ef372, Int.repr 0xa54ff53a)),
   ((Int.repr 0x510e527f, Int.repr 0x9b05688c), (Int.repr 0x1f83d9ab, Int.repr 0x5be0cd19))).
Definition tap_host_ror x n := Int.ror x (Int.repr n).
Definition tap_host_bsig0 x := Int.xor (Int.xor (tap_host_ror x 2) (tap_host_ror x 13)) (tap_host_ror x 22).
Definition tap_host_bsig1 x := Int.xor (Int.xor (tap_host_ror x 6) (tap_host_ror x 11)) (tap_host_ror x 25).
Definition tap_host_lsig0 x := Int.xor (Int.xor (tap_host_ror x 7) (tap_host_ror x 18)) (Int.shru x (Int.repr 3)).
Definition tap_host_lsig1 x := Int.xor (Int.xor (tap_host_ror x 17) (tap_host_ror x 19)) (Int.shru x (Int.repr 10)).
Definition tap_host_ch x y z := Int.xor (Int.and x y) (Int.and (Int.not x) z).
Definition tap_host_maj x y z := Int.or (Int.and x (Int.or y z)) (Int.and y z).

Definition tap_host_step (s : tap_host_state) (kw : Int.int * Int.int) : tap_host_state :=
  let '(((a,b),(c,d)),((e,f),(g,h))) := s in
  let '(k,w) := kw in
  let t1 := Int.add (Int.add (Int.add (Int.add h (tap_host_bsig1 e)) (tap_host_ch e f g)) k) w in
  let t2 := Int.add (tap_host_bsig0 a) (tap_host_maj a b c) in
  (((Int.add t1 t2,a),(b,c)),((Int.add d t1,e),(f,g))).

Definition tap_host_schedule_word (ws : list Int.int) j :=
  Int.add (Int.add (Int.add (tap_host_lsig1 (nth (j-2) ws Int.zero)) (nth (j-7) ws Int.zero))
    (tap_host_lsig0 (nth (j-15) ws Int.zero))) (nth (j-16) ws Int.zero).
Definition tap_host_be32 (bs : list Int.int) j :=
  fold_left (fun a b => Int.add (Int.shl a (Int.repr 8)) b)
    (firstn 4 (skipn (4*j) bs)) Int.zero.
Definition tap_host_feedforward (s t : tap_host_state) : tap_host_state :=
  let '(((a,b),(c,d)),((e,f),(g,h))) := s in
  let '(((a',b'),(c',d')),((e',f'),(g',h'))) := t in
  (((Int.add a a',Int.add b b'),(Int.add c c',Int.add d d')),
   ((Int.add e e',Int.add f f'),(Int.add g g',Int.add h h'))).
Definition tap_host_compress s bs :=
  let first16 := map (tap_host_be32 bs) (seq 0 16) in
  let ws := fold_left (fun ws j => ws ++ [tap_host_schedule_word ws j]) (seq 16 48) first16 in
  tap_host_feedforward s (fold_left tap_host_step (combine SHA256.K256 ws) s).
Definition tap_host_state_words (s : tap_host_state) :=
  let '(((a,b),(c,d)),((e,f),(g,h))) := s in [a;b;c;d;e;f;g;h].
Definition tap_host_hash (s : tap_host_state) : Digest.hash256 :=
  let '(((a,b),(c,d)),((e,f),(g,h))) := s in Digest.Hash256 [a;b;c;d;e;f;g;h] eq_refl.
Definition tap_host_put32 x :=
  map (fun k => Int.and (Int.shru x (Int.repr k)) (Int.repr 255)) [24;16;8;0].

Definition tap_host_tag_bytes := map (fun b => Int.repr (Byte.unsigned b)) (SHA256.str_to_bytes "TapData"%string).
Definition tap_host_pad len :=
  let bits := 8 * len in
  let r := 448 - bits mod 512 - 1 in
  let k := if Z.leb r (-1) then r + 512 else r in
  [Int.repr 128] ++ repeat Int.zero (Z.to_nat ((k+1)/8-1)) ++
    map (fun s => Int.repr (Z.land (Z.shiftr bits s) 255)) [56;48;40;32;24;16;8;0].
Definition tap_host_tag_state := tap_host_compress tap_host_iv (tap_host_tag_bytes ++ tap_host_pad 7).
Definition tap_host_tag_digest := flat_map tap_host_put32 (tap_host_state_words tap_host_tag_state).
Definition tap_host_prefix_state := tap_host_compress tap_host_iv (tap_host_tag_digest ++ tap_host_tag_digest).
Definition tap_host_prefix := from_hash256 (tap_host_hash tap_host_prefix_state).

Lemma tap_host_round_constants : map Int.unsigned SHA256.K256 =
  [0x428a2f98;0x71374491;0xb5c0fbcf;0xe9b5dba5;0x3956c25b;0x59f111f1;0x923f82a4;0xab1c5ed5;
   0xd807aa98;0x12835b01;0x243185be;0x550c7dc3;0x72be5d74;0x80deb1fe;0x9bdc06a7;0xc19bf174;
   0xe49b69c1;0xefbe4786;0x0fc19dc6;0x240ca1cc;0x2de92c6f;0x4a7484aa;0x5cb0a9dc;0x76f988da;
   0x983e5152;0xa831c66d;0xb00327c8;0xbf597fc7;0xc6e00bf3;0xd5a79147;0x06ca6351;0x14292967;
   0x27b70a85;0x2e1b2138;0x4d2c6dfc;0x53380d13;0x650a7354;0x766a0abb;0x81c2c92e;0x92722c85;
   0xa2bfe8a1;0xa81a664b;0xc24b8b70;0xc76c51a3;0xd192e819;0xd6990624;0xf40e3585;0x106aa070;
   0x19a4c116;0x1e376c08;0x2748774c;0x34b0bcb5;0x391c0cb3;0x4ed8aa4a;0x5b9cca4f;0x682e6ff3;
   0x748f82ee;0x78a5636f;0x84c87814;0x8cc70208;0x90befffa;0xa4506ceb;0xbef9a3f7;0xc67178f2].
Proof. vm_compute; reflexivity. Qed.
Lemma tap_host_tag_bytes_matches : tap_host_tag_bytes = tag_bytes.
Proof. vm_compute; reflexivity. Qed.
Lemma tap_host_pad_matches : tap_host_pad 7 = sha_pad (Int64.repr 7).
Proof. vm_compute; reflexivity. Qed.
Lemma tap_host_full_blocks :
  List.length (tap_host_tag_bytes ++ tap_host_pad 7) = 64%nat /\
  List.length (tap_host_tag_digest ++ tap_host_tag_digest) = 64%nat.
Proof. vm_compute; auto. Qed.
Lemma tap_host_tag_matches : from_hash256 (tap_host_hash tap_host_tag_state) = tag_word.
Proof. vm_compute; reflexivity. Qed.
Lemma tap_host_prefix_matches : tap_host_prefix = tapdata_prefix.
Proof. vm_compute; reflexivity. Qed.
